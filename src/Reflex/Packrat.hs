{-# language GADTs #-}
{-# language TemplateHaskell #-}
{-# language LambdaCase, RecursiveDo, ScopedTypeVariables #-}
module Reflex.Packrat where

import Reflex
import Reflex.Network
import Control.Applicative
import Control.Monad.Fix
import Data.Char
import Data.GADT.Compare.TH
import Data.Dependent.Sum ((==>))
import Data.Maybe (fromMaybe)
import Data.Vector.Unboxed (Vector)

import qualified Data.Dependent.Map as DMap
import qualified Data.Vector.Unboxed as Vector

data Edit = Edit !Int !Int !(Vector Char)
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

getChr :: (Reflex t, MonadSample t m) => Int -> Derivs t -> m (Result t Char)
getChr 0 dvs = sample . current $ dvChar dvs
getChr n dvs = do
  res <- sample . current $ dvChar dvs
  case res of
    Failure -> pure res
    Success _ dvs' -> getChr (n-1) dvs'

data EditKey a where
  EditKey :: Int -> EditKey (Int, Int, Vector Char)
deriveGEq ''EditKey
deriveGCompare ''EditKey

parse ::
  forall t m.
  (Reflex t, MonadHold t m, MonadFix m, Adjustable t m) =>
  Event t Edit ->
  m (Derivs t)
parse = parse' 0
  where
    mkChrs ::
      Int ->
      Vector Char ->
      Event t Edit ->
      Maybe (Result t Char) ->
      m (Dynamic t (Result t Char))
    mkChrs pos vs eEdit after = do
      rec
        dPos <-
          holdDyn pos $
          attachWithMaybe
            (\p (Edit from to values) ->
               if from >= to
               then Nothing
               else
                 if p >= to
                 then
                   let
                     change = Vector.length values - max 0 (to - from)
                   in
                     if change == 0
                     then Nothing
                     else Just $ p + change
                 else Nothing)
            (current dPos)
            eEdit

      let
        eEditPos =
          switchDyn $
          (\p -> (,) p <$> eEdit) <$> dPos

      rec
        chr <-
          networkHold (chrsRes pos eEditPos vs eEdit after) $
          attachWithMaybe
            (\res (p, Edit from to values) ->
               let
                 spanSize = to - from
                 change = Vector.length values - spanSize
                 valuesEnd = from + Vector.length values
               in
                 case compare change 0 of
                   -- some things may have been deleted
                   LT ->
                     if p == valuesEnd
                     then
                       case res of
                         Failure -> Nothing
                         Success _ dvs -> Just $ getChr (to-valuesEnd-1) dvs
                     -- the character was changed, not deleted
                     else Nothing
                   EQ ->
                     case res of
                       Failure ->
                         Just $ chrsRes p eEditPos (Vector.drop (p-from) values) eEdit Nothing
                       Success{} -> Nothing
                   -- some things may have been added
                   GT ->
                     if p == from
                     -- create new cells
                     then
                       Just $ do
                         after' <-
                           case res of
                             Failure -> pure res
                             Success _ dvs -> sample $ current (dvChar dvs)
                         chrsRes p eEditPos values eEdit $ Just after'
                     else Nothing)
            (current chr)
            eEditPos
      pure chr

    chrsRes ::
      Int ->
      Event t (Int, Edit) ->
      Vector Char ->
      Event t Edit ->
      Maybe (Result t Char) ->
      m (Result t Char)
    chrsRes pos eEditPos vec eEdit after
      | Vector.length vec == 0 = pure $ fromMaybe Failure after
      | otherwise = do
          dV <- holdDyn (Vector.head vec) $ editPos eEditPos
          chr <- mkChrs (pos+1) (Vector.tail vec) eEdit after
          let
            d = Derivs add mul prim dec chr
            add = pAdd d
            mul = pMul d
            prim = pPrimary d
            dec = pDecimal d
          pure $ Success dV d

    editPos =
      fmapMaybe
      (\(pos, Edit from to values) ->
          if from <= pos && pos < min (from + Vector.length values) to
          then Just $ values Vector.! (pos - from)
          else Nothing)

    parse' :: Int -> Event t Edit -> m (Derivs t)
    parse' pos eEdit = do
      chr <- mkChrs pos Vector.empty eEdit Nothing
      let
        d = Derivs add mul prim dec chr
        add = pAdd d
        mul = pMul d
        prim = pPrimary d
        dec = pDecimal d
      pure d
