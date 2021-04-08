{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE OverloadedStrings #-}

module Util.Log
  ( MonadLog(..)
  , MonadLogIO
  , logIntToLvl
  , logMsgStr
  , runMonadLogIO
  , indentLog
  , unindentLog
  , MonadLogT
  , WLog.LogCfg
  ) where

import           Control.Monad.Identity

import qualified Control.Monad.IO.Class as IO

import qualified Control.Monad.Trans as MT
import qualified Control.Monad.State as MS
import qualified Control.Monad.Reader as MR
import qualified Control.Monad.Except as ME
import qualified Control.Monad.Writer as MW
import qualified Control.Monad.RWS as RWS
import qualified Data.Text as T

import qualified What4.Utils.Log as WLog

-- Simple logging monad transformer/class
class Monad m => MonadLog m where
  logMsg :: Integer -> T.Text -> m () -- log a message at a given logging level
  logIndent :: (Integer -> Integer) -> m Integer -- modify logging indentation level (returning old indent level)
  logIndent _ = return 0

-- | Wrapped IO monad for logging purposes
newtype MonadLogIO a =
  MonadLogIO { _unMonadLogIO :: MS.StateT (Integer, WLog.LogCfg) IO a }
  deriving (Functor, Applicative, Monad)

logIntToLvl :: Integer -> WLog.LogLevel
logIntToLvl i = case i of
  (-1) -> WLog.Error
  0 -> WLog.Warn
  1 -> WLog.Info
  _ -> WLog.Debug

instance MonadLog MonadLogIO where
  logMsg logLvl msg = MonadLogIO $ do
    (_indent, logCfg) <- MS.get
    IO.liftIO $ WLog.logIOWith logCfg (logIntToLvl logLvl) (T.unpack msg)

  logIndent f = MonadLogIO $ do
    (indent, logCfg) <- MS.get
    MS.put (f indent, logCfg)
    return indent

logMsgStr :: MonadLog m => Integer -> String -> m ()
logMsgStr logLvl msg = logMsg logLvl (T.pack msg)

runMonadLogIO :: MonadLogIO a -> WLog.LogCfg -> IO a
runMonadLogIO (MonadLogIO m) logCfg = MS.evalStateT m (0, logCfg)

logWithIndent :: MonadLog m => (Integer -> Integer) -> m a -> m a -- log inner function at given indentation level
logWithIndent f m = do
  oldIndent <- logIndent f
  a <- m
  void $ logIndent (\_ -> oldIndent)
  return a

indentLog :: MonadLog m => m a -> m a
indentLog m = logWithIndent ((+) 1) m

unindentLog :: MonadLog m => m a -> m a
unindentLog m = logIndent (\_ -> 0) >> m

newtype MonadLogT m a =
  MonadLogT { _unMonadLogT :: MS.StateT (Integer, Integer) (MW.WriterT [T.Text] m) a }
  deriving (Functor, Applicative, Monad)

instance MT.MonadTrans MonadLogT where
  lift m = MonadLogT $ MT.lift $ MT.lift $ m

instance Monad m => MonadLog (MonadLogT m) where
  logMsg logLvl msg = MonadLogT $ do
    (indent, lvl) <- MS.get
    when (lvl >= logLvl) $ MW.tell ([T.replicate (fromIntegral indent) " " <> msg])

  logIndent f = MonadLogT $ do
    (indent, lvl) <- MS.get
    MS.put (f indent, lvl)
    return indent

instance MonadLog Identity where
  logMsg _ _ = return ()
  logIndent _ = return 0

instance (Monoid w, MonadLog m) => MonadLog (MW.WriterT w m) where
  logMsg logLvl msg = MT.lift $ logMsg logLvl msg
  logIndent f = MT.lift $ logIndent f

instance (MonadLog m) => MonadLog (MS.StateT s m) where
  logMsg logLvl msg = MT.lift $ logMsg logLvl msg
  logIndent f = MT.lift $ logIndent f

instance (MonadLog m) => MonadLog (ME.ExceptT e m) where
  logMsg logLvl msg = MT.lift $ logMsg logLvl msg
  logIndent f = MT.lift $ logIndent f

instance (Monoid w, MonadLog m) => MonadLog (RWS.RWST e w s m) where
  logMsg logLvl msg = MT.lift $ logMsg logLvl msg
  logIndent f = MT.lift $ logIndent f

deriving instance ME.MonadError e m => ME.MonadError e (MonadLogT m)

instance MS.MonadState s m => MS.MonadState s (MonadLogT m) where
  state f = MonadLogT $ MT.lift $ MS.state f

instance MR.MonadReader r m => MR.MonadReader r (MonadLogT m) where
  ask = MonadLogT $ MT.lift MR.ask
  local f (MonadLogT m) = MonadLogT $ MS.mapStateT (MW.mapWriterT (MR.local f)) m


-- runMonadLogT :: Monad m => MonadLogT m a -> Integer -> m (a, [T.Text])
-- runMonadLogT (MonadLogT m) logLvl = MW.runWriterT (MS.evalStateT m (0, logLvl))
