{-# language GADTs #-}
{-# language TemplateHaskell #-}
{-# language LambdaCase, RecursiveDo, ScopedTypeVariables #-}
{-# language GeneralizedNewtypeDeriving #-}
{-# language DeriveFunctor, StandaloneDeriving #-}
{-# language RecursiveDo #-}
module Reflex.Packrat where

import Reflex
import Reflex.Network
import Control.Applicative
import Control.Monad.Fix
import Control.Monad.State
import Data.Char
import Data.GADT.Compare.TH
import Data.Dependent.Sum ((==>))
import Data.Map.Lazy (Map)
import Data.Maybe (fromMaybe, fromJust)
import Data.Vector.Unboxed (Vector)

import GHC.Exts (Any)
import Unsafe.Coerce (unsafeCoerce)

import qualified Data.Dependent.Map as DMap
import qualified Data.Map as Map
import qualified Data.Vector as Boxed
import qualified Data.Vector.Unboxed as Vector

data Result t a
  = Success (Dynamic t a) (Derivs t)
  | Failure
deriving instance Reflex t => Functor (Result t)

data Edit = Edit !Int !Int !(Vector Char)
  deriving Show

newtype Derivs t
  = Derivs
  { unDerivs :: Boxed.Vector (Dynamic t (Result t Any))
  }

newtype Prod t a
  = Prod
  { unProd :: Derivs t -> Dynamic t (Result t a)
  }
deriving instance Reflex t => Functor (Prod t)

instance Reflex t => Applicative (Prod t) where
  pure a = Prod $ \dvs -> pure $ Success (pure a) dvs
  Prod mf <*> Prod ma =
    Prod $ \dvs -> do
      fRes <- mf dvs
      case fRes of
        Failure -> pure Failure
        Success dF dvs' -> do
          aRes <- ma dvs'
          pure $
            case aRes of
              Failure -> Failure
              Success dA dvs'' -> Success (dF <*> dA) dvs''

instance Reflex t => Alternative (Prod t) where
  empty = Prod $ \_ -> pure Failure
  Prod ma <|> Prod mb =
    Prod $ \dvs -> do
      aRes <- ma dvs
      case aRes of
        Failure -> mb dvs
        Success{} -> pure aRes

-- 0 is reserved for char
newtype Grammar t a
  = Grammar
  { unGrammar :: State (Map Int (Prod t Any)) a
  } deriving (Functor, Applicative, Monad, MonadFix)

dvChar :: Derivs t -> Dynamic t (Result t Char)
dvChar (Derivs dvs) = unsafeCoerce (dvs Boxed.! 0)

rule :: forall t a. Prod t a -> Grammar t (Prod t a)
rule p = Grammar $ do
  m <- get
  let n = Map.size m
  put $ Map.insert n (unsafeCoerce p :: Prod t Any) m
  pure . Prod $ \(Derivs dvs) -> unsafeCoerce (dvs Boxed.! n)

anyChar :: Prod t Char
anyChar = Prod dvChar

satisfy :: Reflex t => (Char -> Bool) -> Prod t Char
satisfy f =
  Prod $ \dvs -> do
    res <- dvChar dvs
    case res of
      Success dC dvs' -> do
        c <- dC
        pure $
          if f c
          then Success dC dvs'
          else Failure
      _ -> pure Failure

additionGrammar :: Reflex t => Grammar t (Prod t Int)
additionGrammar = do
  digitP <- rule $ read . pure <$> satisfy isDigit
  primaryP <- rule digitP
  rec
    mulP <- rule $
      (*) <$> primaryP <* satisfy (=='*') <*> mulP <|>
      primaryP
  rec
    addP <- rule $
      (+) <$> mulP <* satisfy (=='+') <*> addP <|>
      mulP
  pure addP

digitGrammar :: Reflex t => Grammar t (Prod t Int)
digitGrammar =
  rule $ read . pure <$> satisfy isDigit

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
  forall t m a.
  (Reflex t, MonadHold t m, MonadFix m, Adjustable t m) =>
  Grammar t (Prod t a) ->
  Event t Edit ->
  m (Dynamic t String, Dynamic t (Result t a))
parse (Grammar grammar) e = do
  derivs <- parse' 0 e
  pure (getString derivs, unProd outputProd derivs)
  where
    outputProd :: Prod t a
    mapping :: Map Int (Prod t Any)
    (outputProd, mapping) =
      runState grammar $
      Map.singleton 0 (unsafeCoerce (Prod dvChar) :: Prod t Any)

    mappingVec :: Boxed.Vector (Prod t Any)
    mappingVec =
      Boxed.generate (Map.size mapping) $
      \ix -> fromJust $ Map.lookup ix mapping

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
        eEditPos = switchDyn $ (\p -> (,) p <$> eEdit) <$> dPos

      rec
        dAfter <-
          fmap join .
          holdDyn (pure Failure) $
          (\res (p, Edit from to values) ->
             case res of
               Failure -> pure Failure
               Success _ dvs ->
                 getChr (max (from + Vector.length values) to - p - 1) dvs) <$>
          current chr <@>
          eEditPos

        chr <-
          networkHold (chrsRes pos eEditPos vs eEdit after) $
          attachWithMaybe
            (\(after', res) (p, Edit from to values) ->
               {-

               F                                    T
               |-------------------(T - F)----------|
               |------VS-------|
                               |---(T - (F + VS))---|
                            (F + VS)
               |--( case 1 )---|
                               ^
                               |
                           ( case 2 )


                                            T
               F                            |--(F + VS - T)--|
               |-----------(T - F)----------|
               |---------------------VS----------------------|
                                                          (F + VS)
               |---------( case 3 )---------|
                                            ^
                                            |
                                        ( case 4 )


               case 1: if p already exists here then it changes
               case 2: set p to whatever is at T
               case 3: if p already exists here then it changes
               case 4: insert new values at p, and have them terminate with whatever is at T

               -}
               if from <= p && p < max (from + Vector.length values) to
               then
                 let valuesEnd = from + Vector.length values in
                 case res of
                   Success{}
                     -- F + VS ~> T will be deleted
                     | valuesEnd < to ->
                         if p == from + Vector.length values
                         then Just $ pure after'
                         else Nothing
                     -- T ~> F + VS will be created
                     | valuesEnd >= to ->
                         if p == to
                         then
                           Just $
                           chrsRes p eEditPos (Vector.drop (from-to) values) eEdit (Just after')
                         else Nothing
                   Failure
                     | p == from ->
                         Just $ chrsRes p eEditPos values eEdit Nothing
                     | otherwise -> Nothing
               else Nothing)
            ((,) <$> current dAfter <*> current chr)
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
      | Vector.length vec == 0 =
        pure $ fromMaybe Failure after
      | otherwise = do
          dV <- holdDyn (Vector.head vec) $ editPos eEditPos
          chr <- mkChrs (pos+1) (Vector.tail vec) eEdit after
          let d = mkDerivs chr
          pure $ Success dV d

    editPos =
      fmapMaybe
      (\(pos, Edit from to values) ->
          if from <= pos && pos < min (from + Vector.length values) to
          then Just $ values Vector.! (pos - from)
          else Nothing)

    mkDerivs chr =
      let
        d =
          Derivs $
          Boxed.imap
            (\k (Prod f) ->
               if k == 0
               then unsafeCoerce chr :: Dynamic t (Result t Any)
               else f d)
            mappingVec
      in
        d

    parse' :: Int -> Event t Edit -> m (Derivs t)
    parse' pos eEdit = do
      chr <- mkChrs pos Vector.empty eEdit Nothing
      let d = mkDerivs chr
      pure d
