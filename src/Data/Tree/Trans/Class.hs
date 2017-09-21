module Data.Tree.Trans.Class where

import           Data.Tree.RankedTree

class (RankedTree ta, RankedTree tb) => TreeTransducer t ta tb | t -> ta, t -> tb where
  treeTrans :: t -> (ta -> tb)
