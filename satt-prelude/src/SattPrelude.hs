{-# LANGUAGE ImplicitParams #-}

module SattPrelude
  ( -- common
    module ClassyPrelude

    -- useful modules
  , module Control.Arrow
  , module Data.Bifoldable
  , module Data.Either
  , module Data.Functor.Classes
  , module Data.Functor.Foldable
  , module Data.Kind
  , module Lens.Micro
  , module Data.Void
  , absurd

    -- useful components
  , Proxy(..)
  , Generic1
  , coerce
  , (#.)
  , (.#)
  , groom
  , ushow
  , groomPrint
  , uprint
  , bivoid
  , throwErrorM
  , errorVoid
  , errorUnreachable
  , Nat
  , Symbol
  , KnownNat
  , KnownSymbol
  , natVal
  , symbolVal

    -- derivings
  , deriveEq1
  , deriveEq2
  , deriveOrd1
  , deriveOrd2
  , deriveShow1
  , deriveShow2
  , deriveBifunctor
  , deriveBifoldable
  , deriveBitraversable
  ) where

import           ClassyPrelude

import           Control.Arrow            (Kleisli (..), (<<<), (>>>))
import           Data.Bifoldable
import           Data.Coerce
import           Data.Either              (isLeft, isRight)
import           Data.Functor.Classes
import           Data.Functor.Foldable    (Corecursive (..), Fix (..),
                                           Recursive (..))
import           Data.Kind                (Type)
import           Data.Profunctor.Unsafe
import           Data.Proxy
import           Data.Singletons.TypeLits
import           Data.Void                hiding (absurd)
import           GHC.Generics             (Generic1)
import           Lens.Micro
import           Text.Groom
import           Text.Show.Unicode

import           Data.Bifunctor.TH
import           Data.Eq.Deriving
import           Data.Ord.Deriving
import           Text.Show.Deriving

import           GHC.Exception            (errorCallWithCallStackException)
import           GHC.Stack                (HasCallStack)

throwErrorM :: (HasCallStack, MonadThrow m) => String -> m a
throwErrorM s = throwM $ errorCallWithCallStackException s ?callStack

bivoid :: Bifunctor f => f a b -> f () ()
bivoid = bimap (const ()) (const ())
{-# INLINE bivoid #-}

errorVoid :: a -> Void
errorVoid = error "error void"

errorUnreachable :: a
errorUnreachable = error "unreachable"

-- for GHC 8.2.x bug (https://ghc.haskell.org/trac/ghc/ticket/13990)
absurd :: Void -> a
absurd = error "absurd"

groomPrint :: Show a => a -> IO ()
groomPrint = putStrLn . pack . groom
