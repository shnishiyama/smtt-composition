{-# LANGUAGE OverloadedLists #-}

module Data.Tree.RankedTree.Instances where

import           ClassyPrelude

import           Data.Universe.Class
import           Data.Tree.RankedTree

data TreeABC
  = TreeA TreeABC TreeABC
  | TreeB TreeABC
  | TreeC
  deriving (Eq, Ord, Show, Generic)

data TreeABCLabel
  = TreeALabel
  | TreeBLabel
  | TreeCLabel
  deriving (Eq, Ord, Enum, Bounded, Generic)

instance Show TreeABCLabel where
  show TreeALabel = "a"
  show TreeBLabel = "b"
  show TreeCLabel = "c"

instance NFData TreeABC
instance Universe TreeABCLabel
instance Finite TreeABCLabel
instance Hashable TreeABCLabel

instance RankedTree TreeABC where
  type LabelType TreeABC = TreeABCLabel

  treeLabel (TreeA _ _) = TreeALabel
  treeLabel (TreeB _)   = TreeBLabel
  treeLabel TreeC       = TreeCLabel

  treeChilds (TreeA x y) = [x, y]
  treeChilds (TreeB x)   = [x]
  treeChilds TreeC       = []

  treeLabelRank _ TreeALabel = 2
  treeLabelRank _ TreeBLabel = 1
  treeLabelRank _ TreeCLabel = 0

  mkTreeUnchecked TreeALabel ts = TreeA (ts ! 0) (ts ! 1)
  mkTreeUnchecked TreeBLabel ts = TreeB (ts ! 0)
  mkTreeUnchecked TreeCLabel _  = TreeC


-- | Infix operation tree
data InfixOpTree
  = InfixOne
  | InfixTwo
  | InfixPlus  InfixOpTree InfixOpTree
  | InfixMulti InfixOpTree InfixOpTree
  deriving (Eq, Ord, Generic)

data InfixOpTreeLabel
  = InfixOneLabel
  | InfixTwoLabel
  | InfixPlusLabel
  | InfixMultiLabel
  deriving (Eq, Ord, Enum, Bounded, Generic)

instance Show InfixOpTreeLabel where
  show InfixOneLabel   = "one"
  show InfixTwoLabel   = "two"
  show InfixPlusLabel  = "plus"
  show InfixMultiLabel = "multi"

instance NFData InfixOpTree
instance Universe InfixOpTreeLabel
instance Finite InfixOpTreeLabel
instance Hashable InfixOpTreeLabel

-- | Appearance of infix operation trees
--
-- Examples:
--
-- >>> InfixMulti InfixOne (InfixPlus InfixTwo InfixOne)
-- multi(one, plus(two, one))
instance Show InfixOpTree where
  show = showTree

instance RankedTree InfixOpTree where
  type LabelType InfixOpTree = InfixOpTreeLabel

  treeLabel InfixOne     = InfixOneLabel
  treeLabel InfixTwo     = InfixTwoLabel
  treeLabel InfixPlus{}  = InfixPlusLabel
  treeLabel InfixMulti{} = InfixMultiLabel

  treeChilds InfixOne         = []
  treeChilds InfixTwo         = []
  treeChilds (InfixPlus  x y) = [x, y]
  treeChilds (InfixMulti x y) = [x, y]

  treeLabelRank _ InfixOneLabel   = 0
  treeLabelRank _ InfixTwoLabel   = 0
  treeLabelRank _ InfixPlusLabel  = 2
  treeLabelRank _ InfixMultiLabel = 2

  mkTreeUnchecked InfixOneLabel   _  = InfixOne
  mkTreeUnchecked InfixTwoLabel   _  = InfixTwo
  mkTreeUnchecked InfixPlusLabel  ts = InfixPlus  (ts ! 0) (ts ! 1)
  mkTreeUnchecked InfixMultiLabel ts = InfixMulti (ts ! 0) (ts ! 1)


-- | Postfix operation tree
data PostfixOpTree
  = PostfixOne   PostfixOpTree
  | PostfixTwo   PostfixOpTree
  | PostfixPlus  PostfixOpTree
  | PostfixMulti PostfixOpTree
  | PostfixEnd
  deriving (Eq, Ord, Generic)

data PostfixOpTreeLabel
  = PostfixOneLabel
  | PostfixTwoLabel
  | PostfixPlusLabel
  | PostfixMultiLabel
  | PostfixEndLabel
  deriving (Eq, Ord, Enum, Bounded, Generic)

instance Show PostfixOpTreeLabel where
  show PostfixOneLabel   = "one"
  show PostfixTwoLabel   = "two"
  show PostfixPlusLabel  = "plus"
  show PostfixMultiLabel = "multi"
  show PostfixEndLabel   = "$"

instance NFData PostfixOpTree
instance Universe PostfixOpTreeLabel
instance Finite PostfixOpTreeLabel
instance Hashable PostfixOpTreeLabel

-- | Appearance of postfix operation trees
--
-- Examples:
--
-- >>> PostfixTwo $ PostfixOne $ PostfixTwo $ PostfixPlus $ PostfixMulti $ PostfixEnd
-- two(one(two(plus(multi($)))))
instance Show PostfixOpTree where
  show = showTree

instance RankedTree PostfixOpTree where
  type LabelType PostfixOpTree = PostfixOpTreeLabel

  treeLabel PostfixOne{}   = PostfixOneLabel
  treeLabel PostfixTwo{}   = PostfixTwoLabel
  treeLabel PostfixPlus{}  = PostfixPlusLabel
  treeLabel PostfixMulti{} = PostfixMultiLabel
  treeLabel PostfixEnd     = PostfixEndLabel

  treeChilds (PostfixOne   x) = [x]
  treeChilds (PostfixTwo   x) = [x]
  treeChilds (PostfixPlus  x) = [x]
  treeChilds (PostfixMulti x) = [x]
  treeChilds PostfixEnd       = []

  treeLabelRank _ PostfixOneLabel   = 1
  treeLabelRank _ PostfixTwoLabel   = 1
  treeLabelRank _ PostfixPlusLabel  = 1
  treeLabelRank _ PostfixMultiLabel = 1
  treeLabelRank _ PostfixEndLabel   = 0

  mkTreeUnchecked PostfixOneLabel   ts = PostfixOne   (ts ! 0)
  mkTreeUnchecked PostfixTwoLabel   ts = PostfixTwo   (ts ! 0)
  mkTreeUnchecked PostfixPlusLabel  ts = PostfixPlus  (ts ! 0)
  mkTreeUnchecked PostfixMultiLabel ts = PostfixMulti (ts ! 0)
  mkTreeUnchecked PostfixEndLabel   _  = PostfixEnd

data BinTree l
  = Node l (BinTree l) (BinTree l)
  | Leaf
  deriving (Eq, Ord, Show)

instance RankedTree (BinTree l) where
  type LabelType (BinTree l) = Maybe l

  treeLabel (Node l _ _) = Just l
  treeLabel Leaf         = Nothing

  treeChilds (Node _ a b) = [a, b]
  treeChilds Leaf         = []

  treeLabelRank _ Just{}  = 2
  treeLabelRank _ Nothing = 0

  mkTreeUnchecked (Just l) cs = Node l (cs ! 0) (cs ! 1)
  mkTreeUnchecked Nothing  _  = Leaf
