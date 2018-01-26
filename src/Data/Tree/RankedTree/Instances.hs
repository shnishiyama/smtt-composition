{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE OverloadedLists    #-}

module Data.Tree.RankedTree.Instances where

import           SattPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label

data BinTree a
  = BinNode a (BinTree a) (BinTree a)
  | BinLeaf
  deriving (Eq, Ord, Show, Functor, Foldable, Generic, Hashable)

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


newtype ListTree a = ListTree
  { unListTree :: [a]
  }
  deriving (Eq, Ord, Show, Generic)
  deriving newtype Hashable

instance RankedTree (ListTree a) where
  type LabelType (ListTree a) = Maybe a

  treeLabel (ListTree l) = case l of
    []  -> Nothing
    x:_ -> Just x

  treeChilds (ListTree l) = case l of
    []   -> []
    _:xs -> [ListTree xs]

  treeLabelRank _ Just{}  = 1
  treeLabelRank _ Nothing = 0

  mkTreeUnchecked (Just x) cs = coerce (x:) $ cs `indexEx` 0
  mkTreeUnchecked Nothing _   = ListTree []


data NatNum
  = Zero
  | Succ NatNum
  deriving (Eq, Ord, Show, Generic, Hashable)

instance RankedTree NatNum where
  type LabelType NatNum = Bool

  treeLabel (Succ _) = True
  treeLabel Zero     = False

  treeChilds (Succ n) = [n]
  treeChilds Zero     = []

  treeLabelRank _ True  = 1
  treeLabelRank _ False = 0

  mkTreeUnchecked True  cs = Succ $ cs `indexEx` 0
  mkTreeUnchecked False _  = Zero


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


type MiniInfixOpAlphabet = TaggedRankedAlphabet
  ['("one", 0), '("plus", 2)]

type MiniInfixOpTree = RankedLabelledTree MiniInfixOpAlphabet

type MiniPostfixOpAlphabet = TaggedRankedAlphabet
  ['("one", 1), '("plus", 1), '("end", 0)]

type MiniPostfixOpTree = RankedLabelledTree MiniPostfixOpAlphabet
