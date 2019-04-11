{-# language FlexibleContexts #-}
{-# language LambdaCase #-}
module Main where

import Reflex
import Reflex.Host.Basic
import Reflex.Packrat
import Control.Concurrent
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Fix
import Data.IORef
import Text.Read

import qualified Data.Vector.Unboxed as Vector

network ::
  ( Reflex t, MonadHold t m, MonadFix m, Adjustable t m
  , MonadIO m, TriggerEvent t m
  , PerformEvent t m, MonadIO (Performable m)
  ) =>
  m ((), Event t ())
network = do
  quitRef <- liftIO $ newIORef False
  (eLine, sendLine) <- newTriggerEvent
  let
    eWords = words <$> eLine
    eEdit =
      fmapMaybe
        (\case
            "edit":from:to:val ->
              Edit <$>
              readMaybe from <*>
              readMaybe to <*>
              pure (Vector.fromList $ concat val)
            _ -> Nothing)
        eWords
    eQuit = fmapMaybe (\case; "quit":_ -> Just (); _ -> Nothing) eWords
  let
    loop = do
      b <- readIORef quitRef
      unless b $ do
        sendLine =<< getLine
        loop

  performEvent_ $ liftIO (writeIORef quitRef True) <$ eQuit

  (dString, dRes) <- parse additionGrammar eEdit
  performEvent_ $ liftIO . print <$> updated (getSuccess dRes)
  performEvent_ $ liftIO . print <$> updated dString

  void . liftIO $ forkIO loop

  pure ((), eQuit)

main :: IO ()
main = basicHostWithQuit network
