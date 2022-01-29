{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Control.Monad.Trace where

import Control.Monad.Except
import Control.Monad.State
import Control.Applicative
import Data.Bifunctor (first)

newtype TraceT e t m a = Trace (ExceptT (e,[t]) m a) deriving(Functor,Applicative,Monad)

instance Monad m => MonadError e (TraceT e t m) where
    throwError e = Trace (throwError (e,[]))
    catchError (Trace x) f = Trace (catchError x ((\case Trace x -> x) . f . fst))

traceError :: Monad m => t -> TraceT e t m a -> TraceT e t m a
traceError t (Trace x) = Trace $ catchError x (\(e,ts) -> throwError (e,t:ts))

runTraceT :: TraceT e t m a -> m (Either (e,[t]) a)
runTraceT (Trace x) = runExceptT x

instance MonadState s m => MonadState s (TraceT e t m) where
    state s = Trace (state s)

instance MonadIO m => MonadIO (TraceT e t m) where
    liftIO x = Trace (liftIO x)

liftTrace :: Monad m => Either (e,[t]) r -> TraceT e t m r
liftTrace (Left e) = Trace (throwError e)
liftTrace (Right r) = pure r

withTraceT :: Functor m => (e -> e') -> TraceT e t m r -> TraceT e' t m r
withTraceT f (Trace x) = Trace (withExceptT (first f) x)