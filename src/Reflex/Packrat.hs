{-# language LambdaCase, RecursiveDo, ScopedTypeVariables #-}
module Reflex.Packrat where

import Debug.Trace (trace)

{-

bug

edit 0 5 1*2*3
"1*2*3"
Just 6

edit 1 5 2
"122*3"
Just 1
"12"

edit 0 2 3*5
"3*"
Nothing

edit 2 3 5

quit


reason: the 'pos' is calculated incorrectly; the upper bound of an
edit should be minned with the size of the string


-}
import Reflex
import Reflex.Network
import Control.Monad.Fix
import Data.Char
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

getChr :: Reflex t => Int -> Derivs t -> Dynamic t (Result t Char)
getChr 0 dvs = dvChar dvs
getChr n dvs = do
  res <- dvChar dvs
  case res of
    Failure -> pure res
    Success _ dvs' -> getChr (n-1) dvs'

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
      m (Dynamic t (Result t Char))
    mkChrs pos vs eEdit = do
      rec
        dPos <-
          holdDyn pos $
          attachWithMaybe
            (\p (Edit from to values) ->
               let valTo = from + Vector.length values in
               if valTo < p
               then
                 if to == valTo
                 then Nothing
                 else Just $ p + valTo
               else Nothing)
            (current dPos)
            eEdit

      rec
        chr <-
          networkHold (chrsRes pos dPos vs eEdit) $
          attachWithMaybe
            (\(p, res) (Edit from to values) ->
               if p < to
               then
                 -- if this position is within the bounds of the edit
                 if from <= p
                 then
                   -- this char and those following it up to 'to' have been deleted
                   -- because the edit didn't provide values for them
                   if from + Vector.length values <= p
                   then
                     case res of
                       Failure -> Nothing
                       Success _ dvs -> Just . sample . current $ getChr (to-p-1) dvs
                   -- this char has a value provided
                   else
                     case res of
                       -- there was previously nothing here, so initialise the cells from
                       -- this position onward
                       Failure ->
                         Just $ chrsRes p dPos (Vector.drop (p-from) values) eEdit
                       -- there was something here, so its result dynamic will be updated
                       Success{} -> Nothing
                 else Nothing
               -- this character's position is after the edit
               --
               -- if the edit increases the size of the document and this character
               -- has no result yet, then it needs to be initialised
               else
                 case res of
                   Failure -> _
                   _ -> Nothing)
            ((,) <$> current dPos <*> current chr)
            eEdit
      pure chr

    chrsRes ::
      Int ->
      Dynamic t Int ->
      Vector Char ->
      Event t Edit ->
      m (Result t Char)
    chrsRes pos dPos vec eEdit
      | Vector.length vec == 0 = pure Failure
      | otherwise = do
          dV <- holdDyn (Vector.head vec) $ editPos dPos eEdit
          chr <- mkChrs (pos+1) (Vector.tail vec) eEdit
          let
            d = Derivs add mul prim dec chr
            add = pAdd d
            mul = pMul d
            prim = pPrimary d
            dec = pDecimal d
          pure $ Success dV d

    editPos dPos =
      attachWithMaybe
      (\pos (Edit from to values) ->
         if p < to
         then
           -- if this position is within the bounds of the edit
           if from <= p
           then
             let ix = pos-from in
             if Vector.length values <= ix
             -- char was deleted
             then Nothing
             -- char was changed
             else Just $ values Vector.! ix
           -- this character occurs before the edit
           else Nothing
         -- this character occurs after the edit
         --
         -- if the edit grows the document, then this character
         -- needs to take on the value of the character a certain
         -- number of places to the left
         --
         -- similarly, if the edit shrinks the document then this character needs to
         -- take the value of a character to the right
         --
         -- the edit grows the document if the size of 'values' is greater
         -- than the span size
         else
           let
             spanSize = to-from
             increase = Vector.length values - spansSize
           in
           case compare increase 0 of
             -- the document grows
             --
             -- we take on the value of the character 'increase' places to the left
             GT -> _
             -- the document didn't change size. this character didn't change.
             EQ -> Nothing
             -- the document shrinks
             --
             -- we take on the value of the character '-increase' places to the right
             LT -> _)
      (current dPos)

    parse' ::
      Int ->
      Event t Edit ->
      m (Derivs t)
    parse' pos eEdit = do
      chr <- mkChrs pos Vector.empty eEdit
      let
        d = Derivs add mul prim dec chr
        add = pAdd d
        mul = pMul d
        prim = pPrimary d
        dec = pDecimal d
      pure d
