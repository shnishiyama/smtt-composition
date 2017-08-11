module Data.Universe.Instances where

import           ClassyPrelude

import           Data.Universe.Class

data EmptyType

instance Eq EmptyType where
  _ == _ = True

instance Ord EmptyType where
  compare _ _ = EQ

instance Show EmptyType where
  show _ = "empty type"

instance Universe EmptyType where
  universe = []

instance Finite EmptyType
