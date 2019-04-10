{-# language GADTs #-}
{-# language TemplateHaskell #-}
{-# language LambdaCase, RecursiveDo, ScopedTypeVariables #-}
module Reflex.Packrat where

import Reflex
import Reflex.Network
import Control.Monad.Fix
import Data.Char
import Data.GADT.Compare.TH
import Data.Dependent.Sum ((==>))

import qualified Data.Dependent.Map as DMap

data Edit = Edit !Int !Int String
  deriving Show

data Result t a
  = Success (Dynamic t a) (Derivs t)
  | Failure

data Derivs t
  = Derivs
  { dvAdd :: Dynamic t (Result t Int)
  , dvMul :: Dynamic t (Result t Int)
  , dvPrimary :: Dynamic t (Result t Int)
  , dvDecimal :: Dynamic t (Result t Int)
  , dvChar :: Dynamic t (Result t Char)
  }

pAdd :: Reflex t => Derivs t -> Dynamic t (Result t Int)
pAdd d = do
  mul <- dvMul d
  case mul of
    Success l d' -> do
      char <- dvChar d'
      case char of
        Success dC d'' -> do
          c <- dC
          case c of
            '+' -> do
              add <- dvAdd d''
              case add of
                Success r d''' -> pure $ Success ((+) <$> l <*> r) d'''
                res -> pure res
            _ -> pure mul
        Failure -> pure mul
    res -> pure res

pMul :: Reflex t => Derivs t -> Dynamic t (Result t Int)
pMul d = do
  primary <- dvPrimary d
  case primary of
    Success l d' -> do
      char <- dvChar d'
      case char of
        Success dC d'' -> do
          c <- dC
          case c of
            '*' -> do
              mul <- dvMul d''
              case mul of
                Success r d''' -> pure $ Success ((*) <$> l <*> r) d'''
                res -> pure res
            _ -> pure primary
        Failure -> pure primary
    res -> pure res

pPrimary :: Reflex t => Derivs t -> Dynamic t (Result t Int)
pPrimary d = dvDecimal d

pDecimal :: Reflex t => Derivs t -> Dynamic t (Result t Int)
pDecimal d = do
  char <- dvChar d
  case char of
    Success dC d' -> do
      c <- dC
      pure $
        if isDigit c
        then Success (pure $ read [c]) d'
        else Failure
    Failure -> pure Failure

getString :: Reflex t => Derivs t -> Dynamic t [Char]
getString dvs =
  dvChar dvs >>=
  \case
    Failure -> pure []
    Success c dvs' -> (:) <$> c <*> getString dvs'

getSuccess :: Reflex t => Dynamic t (Result t a) -> Dynamic t (Maybe a)
getSuccess d = d >>= \case; Failure -> pure Nothing; Success a _ -> Just <$> a

getChr :: Reflex t => Int -> Derivs t -> Dynamic t (Result t Char)
getChr 0 dvs = dvChar dvs
getChr n dvs = do
  res <- dvChar dvs
  case res of
    Failure -> pure res
    Success _ dvs' -> getChr (n-1) dvs'

data EditKey a where
  EditKey :: Int -> EditKey (Int, Int, String)
deriveGEq ''EditKey
deriveGCompare ''EditKey

fanEdit :: Reflex t => Event t Edit -> EventSelector t EditKey
fanEdit eEdit =
  fan $
  (\(Edit from to values) ->
     let res = (from, to, values) in
     DMap.fromList $ fmap (\ix -> EditKey ix ==> res) [from..to-1]) <$>
  eEdit

parse ::
  forall t m.
  (Reflex t, MonadHold t m, MonadFix m, Adjustable t m) =>
  Event t Edit ->
  m (Derivs t)
parse eEdit = parse' 0 $ fanEdit eEdit
  where
    mkChrs :: Int -> String -> EventSelector t EditKey -> m (Dynamic t (Result t Char))
    mkChrs pos vs editES = do
      rec
        dPos <-
          holdDyn pos $
          attachWithMaybe
            (\p (Edit from to values) ->
               let valTo = from + length values in
               if valTo <= p
               then
                 if to == valTo
                 then Nothing
                 else Just $ p + valTo - to
               else Nothing)
            (current dPos)
            eEdit

      let
        eEditPos =
          switchDyn $
          (\p -> (,) p <$> select editES (EditKey p)) <$> dPos

      rec
        chr <-
          networkHold (chrsRes pos eEditPos vs editES) $
          attachWithMaybe
            (\res (p, (from, to, values)) -> do
                if from <= p && p < to
                then
                  let ix = p-from in
                  if length values <= ix
                  -- this char and those following it have been deleted
                  then
                    case res of
                      Failure -> Nothing
                      Success _ dvs -> Just . sample . current $ getChr (to-p-1) dvs
                  -- this char has been inserted
                  else
                    case res of
                      Failure -> Just $ chrsRes p eEditPos (drop (from-p) values) editES
                      Success{} -> Nothing
                else Nothing)
            (current chr)
            eEditPos
      pure chr

    chrsRes ::
      Int ->
      Event t (Int, (Int, Int, String)) ->
      String ->
      EventSelector t EditKey ->
      m (Result t Char)
    chrsRes _ _ [] _ = pure Failure
    chrsRes pos eEditPos (v:vs) editES = do
      dV <- holdDyn v $ editPos eEditPos
      chr <- mkChrs (pos+1) vs editES
      let
        d = Derivs add mul prim dec chr
        add = pAdd d
        mul = pMul d
        prim = pPrimary d
        dec = pDecimal d
      pure $ Success dV d

    editPos =
      fmapMaybe
      (\(pos, (from, to, values)) ->
          if from <= pos && pos < to
          then
            let ix = pos-from in
            if length values <= ix
            -- char was deleted
            then Nothing
            -- char was changed
            else Just $ values !! ix
          else Nothing)

    parse' :: Int -> EventSelector t EditKey -> m (Derivs t)
    parse' pos editES = do
      chr <- mkChrs pos "" editES
      let
        d = Derivs add mul prim dec chr
        add = pAdd d
        mul = pMul d
        prim = pPrimary d
        dec = pDecimal d
      pure d
