module SattPrelude
  ( -- common
    module ClassyPrelude

    -- useful modules
  , module Data.Functor.Classes

    -- useful components
  , Type
  , Proxy(..)
  , coerce
  , (#.)
  , (.#)
  , groom
  , ushow
  , Generic1

    -- derivings
  , module Data.Eq.Deriving
  , module Data.Ord.Deriving
  , module Text.Show.Deriving
  ) where

import           ClassyPrelude

import           Data.Coerce
import           Data.Functor.Classes
import           Data.Kind
import           Data.Profunctor.Unsafe
import           Data.Proxy
import           GHC.Generics
import           Text.Groom
import           Text.Show.Unicode

import           Data.Eq.Deriving
import           Data.Ord.Deriving
import           Text.Show.Deriving
