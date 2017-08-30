module Data.Universe.Instances where

import           ClassyPrelude

import           Data.Universe.Class

data EmptyType

deriving instance Eq EmptyType
deriving instance Ord EmptyType
deriving instance Show EmptyType

instance Universe EmptyType where
  universe = []

instance Finite EmptyType
