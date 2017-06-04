module Data.Tree.Transducer where

import Data.Tree.RankedTree

class TreeTransducer t where
  treeTrans :: (RankedTree a, RankedTree b) => t a b -> a -> b
