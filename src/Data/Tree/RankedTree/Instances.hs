module Data.Tree.RankedTree.Instances where

import           SattPrelude

import           Data.Tree.RankedTree

data BinTree a
  = BinNode a (BinTree a) (BinTree a)
  | BinLeaf
  deriving (Eq, Ord, Show, Functor, Foldable, Generic)

instance Hashable a => Hashable (BinTree a)

type instance Element (BinTree a) = a

instance MonoFoldable (BinTree a)

instance RankedTree (BinTree a) where
  type LabelType (BinTree a) = Maybe a

  treeLabel (BinNode a _ _) = Just a
  treeLabel BinLeaf         = Nothing

  treeChilds (BinNode _ x y) = [x, y]
  treeChilds BinLeaf         = []

  treeLabelRank _ Just{}  = 2
  treeLabelRank _ Nothing = 0

  mkTreeUnchecked (Just x) cs = BinNode x (cs `indexEx` 0) (cs `indexEx` 1)
  mkTreeUnchecked Nothing  _  = BinLeaf

