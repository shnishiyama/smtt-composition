{-# LANGUAGE OverloadedLists #-}

module Data.Tree.RankedTree.Instances where

import           ClassyPrelude

import           Data.Tree.RankedTree

data TreeABC
  = TreeA TreeABC TreeABC
  | TreeB TreeABC
  | TreeC
  deriving (Eq, Ord, Show)

instance RankedTree TreeABC where
  type LabelType TreeABC = Char

  treeLabel (TreeA _ _) = 'a'
  treeLabel (TreeB _)   = 'b'
  treeLabel TreeC       = 'c'

  treeChilds (TreeA x y) = [x, y]
  treeChilds (TreeB x)   = [x]
  treeChilds TreeC       = []

  treeLabelRank _ 'a' = 2
  treeLabelRank _ 'b' = 1
  treeLabelRank _ 'c' = 0
  treeLabelRank _ c   = error $ "not allowed label character: " <> show c

  mkTreeUnchecked 'a' ts = TreeA (ts ! 0) (ts ! 1)
  mkTreeUnchecked 'b' ts = TreeB (ts ! 0)
  mkTreeUnchecked 'c' _  = TreeC
  mkTreeUnchecked c   _  = error $ "not allowed label character: " <> show c


-- | Infix operation tree
data InfixOpTree
  = InfixOne
  | InfixTwo
  | InfixPlus  InfixOpTree InfixOpTree
  | InfixMulti InfixOpTree InfixOpTree
  deriving (Eq, Ord)

-- | Appearance of infix operation trees
--
-- Examples:
--
-- >>> InfixMulti InfixOne (InfixPlus InfixTwo InfixOne)
-- "multi"("one","plus"("two","one"))
instance Show InfixOpTree where
  show = showTree

instance RankedTree InfixOpTree where
  type LabelType InfixOpTree = String

  treeLabel InfixOne     = "one"
  treeLabel InfixTwo     = "two"
  treeLabel InfixPlus{}  = "plus"
  treeLabel InfixMulti{} = "multi"

  treeChilds InfixOne         = []
  treeChilds InfixTwo         = []
  treeChilds (InfixPlus  x y) = [x, y]
  treeChilds (InfixMulti x y) = [x, y]

  treeLabelRank _ "one"   = 0
  treeLabelRank _ "two"   = 0
  treeLabelRank _ "plus"  = 2
  treeLabelRank _ "multi" = 2
  treeLabelRank _ s       = error $ "not allowed label string: " <> show s

  mkTreeUnchecked "one"   _  = InfixOne
  mkTreeUnchecked "two"   _  = InfixTwo
  mkTreeUnchecked "plus"  ts = InfixPlus  (ts ! 0) (ts ! 1)
  mkTreeUnchecked "multi" ts = InfixMulti (ts ! 0) (ts ! 1)
  mkTreeUnchecked s       _  = error $ "not allowed label string: " <> show s


-- | Postfix operation tree
data PostfixOpTree
  = PostfixOne   PostfixOpTree
  | PostfixTwo   PostfixOpTree
  | PostfixPlus  PostfixOpTree
  | PostfixMulti PostfixOpTree
  | PostfixEnd
  deriving (Eq, Ord)

-- | Appearance of postfix operation trees
--
-- Examples:
--
-- >>> PostfixTwo $ PostfixOne $ PostfixTwo $ PostfixPlus $ PostfixMulti $ PostfixEnd
-- "two"("one"("two"("plus"("multi"("$")))))
instance Show PostfixOpTree where
  show = showTree

instance RankedTree PostfixOpTree where
  type LabelType PostfixOpTree = String

  treeLabel PostfixOne{}   = "one"
  treeLabel PostfixTwo{}   = "two"
  treeLabel PostfixPlus{}  = "plus"
  treeLabel PostfixMulti{} = "multi"
  treeLabel PostfixEnd     = "$"

  treeChilds (PostfixOne   x) = [x]
  treeChilds (PostfixTwo   x) = [x]
  treeChilds (PostfixPlus  x) = [x]
  treeChilds (PostfixMulti x) = [x]
  treeChilds PostfixEnd       = []

  treeLabelRank _ "one"   = 1
  treeLabelRank _ "two"   = 1
  treeLabelRank _ "plus"  = 1
  treeLabelRank _ "multi" = 1
  treeLabelRank _ "$"     = 0
  treeLabelRank _ s       = error $ "not allowed label string: " <> show s

  mkTreeUnchecked "one"   ts = PostfixOne   (ts ! 0)
  mkTreeUnchecked "two"   ts = PostfixTwo   (ts ! 0)
  mkTreeUnchecked "plus"  ts = PostfixPlus  (ts ! 0)
  mkTreeUnchecked "multi" ts = PostfixMulti (ts ! 0)
  mkTreeUnchecked "$"     _  = PostfixEnd
  mkTreeUnchecked s       _  = error $ "not allowed label string: " <> show s
