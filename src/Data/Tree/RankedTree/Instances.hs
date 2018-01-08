{-# LANGUAGE OverloadedLists #-}

module Data.Tree.RankedTree.Instances where

import           SattPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label

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


type InputSampleAlphabet = TaggedRankedAlphabet
  ['("A", 2), '("B", 1), '("C", 0)]

type InputSampleTree = RankedLabelledTree InputSampleAlphabet

type OutputSampleAlphabet = TaggedRankedAlphabet
  ['("D", 2), '("E", 1), '("F", 0)]

type OutputSampleTree = RankedLabelledTree OutputSampleAlphabet


type InfixOpAlphabet = TaggedRankedAlphabet
  ['("one", 0), '("two", 0), '("plus", 2), '("multi", 2)]

type InfixOpTree = RankedLabelledTree InfixOpAlphabet

type PostfixOpAlphabet = TaggedRankedAlphabet
  ['("one", 1), '("two", 1), '("plus", 1), '("multi", 1), '("end", 0)]

type PostfixOpTree = RankedLabelledTree PostfixOpAlphabet
