module Data.Tree.RankedTree.Builder where

import qualified Data.HashMap         as HashMap
import           Data.Tree.RankedTree


buildRankedTreeByLeafCount :: forall m i t l.
  ( RtConstraint t l, Monad m, Integral i
  )
  => [l] -> m i -> i -> m t
buildRankedTree ls gen i
  | i <= 0                  = error "negative number"
  | isNothing $ lookup 0 ml = error "not contain any rank 0 labels"
  | otherwise               = buildRankedTreeByLeafCount' ml gen i
  where
    tr = treeLabelRank @(Proxy t)

    ml = HashMap.fromListWith (<>) [(tr l, [l]) | l <- ls]

buildRankedTreeByLeafCount' :: forall m i t l.
  ( RtConstraint t l, Monad m, Integral i
  )
  => HashMap RankNumber l -> m RankNumber -> i -> m t
buildRankedTreeByLeafCount' = undefined

buildRankedTreeOverLeafCount :: forall m i t l.
  ( RtConstraint t l, Monad m, Integral i
  )
  => [l] -> m i -> i -> m t
buildRankedTreeOverLeafCount ls gen i
  | i <= 0                  = error "negative number"
  | isNothing $ lookup 0 ml = error "not contain any rank 0 labels"
  | otherwise               = buildRankedTreeByLeafCount' ml gen i
  where
    tr = treeLabelRank @(Proxy t)

    ml = HashMap.fromListWith (<>) [(tr l, [l]) | l <- ls]

