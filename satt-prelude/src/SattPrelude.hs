{-# LANGUAGE ImplicitParams #-}

module SattPrelude
  ( -- common
    module ClassyPrelude

    -- useful modules
  , module Data.Bifoldable
  , module Data.Functor.Classes
  , module Data.Functor.Foldable

    -- useful components
  , Type
  , Proxy(..)
  , Void
  , Generic1
  , Kleisli
  , coerce
  , (#.)
  , (.#)
  , groom
  , ushow
  , (>>>)
  , (<<<)
  , (<&>)
  , throwErrorM
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

import           Control.Arrow
import           Data.Bifoldable
import           Data.Coerce
import           Data.Functor.Classes
import           Data.Functor.Foldable    (Corecursive (..), Fix (..),
                                           Recursive (..))
import           Data.Kind
import           Data.Profunctor.Unsafe
import           Data.Proxy
import           Data.Singletons.TypeLits
import           Data.Void
import           GHC.Generics
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

(<&>) :: Functor f => f a -> (a -> b) -> f b
x <&> f = fmap f x
