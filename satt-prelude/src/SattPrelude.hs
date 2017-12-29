{-# LANGUAGE ImplicitParams #-}

module SattPrelude
  ( -- common
    module ClassyPrelude

    -- useful modules
  , module Data.Functor.Classes
  , module Data.Bifoldable

    -- useful components
  , Type
  , Proxy(..)
  , coerce
  , (#.)
  , (.#)
  , groom
  , ushow
  , (>>>)
  , (<<<)
  , Generic1
  , errorM
  , Symbol
  , Nat
  , KnownSymbol
  , symbolVal
  , KnownNat
  , natVal
  , Elem
  , Lookup

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
import           Data.Kind
import           Data.Profunctor.Unsafe
import           Data.Promotion.Prelude
import           Data.Proxy
import           Data.Singletons.TypeLits
import           GHC.Generics
import           Text.Groom
import           Text.Show.Unicode

import           Data.Bifunctor.TH
import           Data.Eq.Deriving
import           Data.Ord.Deriving
import           Text.Show.Deriving

import           GHC.Exception            (errorCallWithCallStackException)
import           GHC.Stack                (HasCallStack)

errorM :: (HasCallStack, MonadThrow m) => String -> m a
errorM s = throwM $ errorCallWithCallStackException s ?callStack
