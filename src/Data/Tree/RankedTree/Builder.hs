module Data.Tree.RankedTree.Builder where

import Data.Tree.RankedTree


newtype RankedTreeBuilder m l = RankedTreeBuilder
  { rtLabelBuilder :: RankNumber -> Maybe (m l)
  } deriving (Eq, Ord, Show, Generic)

buildRankedTree :: (RtConstraint t l, MonadState s m, Integral i)
  => i -> RankedTreeBuilder m l -> m t
buildRankedTree = undefined
