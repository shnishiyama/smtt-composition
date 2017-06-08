{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Tree.RankedTree where

import Control.CoercionExt
import Control.Lens

import Data.Proxy
import Data.TFFoldable
import Data.Monoid

-- | Ranked Labeled Tree Class
--
-- TODO:
-- * To use generic for deriving instance
-- * Builder using Template Haskell for easy building
--
-- Conditions:
-- * treeRank == length . treeChilds
-- * treeConstruct (treeLabel t) (treeChilds t) == t
--
class RankedTree t where
  type LabelType t :: *

  treeLabel :: t -> LabelType t
  treeChilds :: t -> [t]

  treeLabelRank :: Proxy t -> LabelType t -> Int

  mkTree :: LabelType t -> [t] -> t

treeRank :: forall t. RankedTree t => t -> Int
treeRank = treeLabelRank (Proxy :: Proxy t) . treeLabel

foldTree :: RankedTree t => (LabelType t -> [b] -> b) -> t -> b
foldTree f = go where
  go t = f (treeLabel t) [go c | c <- treeChilds t]


-- wrapper

newtype RankedTreeWrapper t = RankedTreeWrapper
  { unwrapRankedTree :: t
  } deriving (Show, Eq, Ord)

instance RankedTree t => RankedTree (RankedTreeWrapper t) where
  type LabelType (RankedTreeWrapper t) = LabelType t

  treeLabel (RankedTreeWrapper t) = treeLabel t
  treeChilds (RankedTreeWrapper t) = coerce $ treeChilds t
  treeLabelRank = treeLabelRank

  mkTree l = RankedTreeWrapper #. mkTree l . coerce

instance RankedTree t => TFFoldable (RankedTreeWrapper t) where
  type TFFoldElem (RankedTreeWrapper t) = LabelType t

  tfFoldMap f = foldTree $ \a bs -> f a <> mconcat bs

  tfFoldl f s t = foldl (tfFoldl f) is $ treeChilds t where
    is = f s $ treeLabel t

  tfFoldr f s t = f (treeLabel t) child where
    child = foldr (flip $ tfFoldr f) s $ treeChilds t


-- lenses

_rtroot :: RankedTree t => Lens' t (LabelType t)
_rtroot f t = (`mkTree` treeChilds t) <$> f (treeLabel t)

_rtbranches :: RankedTree t => Lens' t [t]
_rtbranches f t = mkTree (treeLabel t) <$> f (treeChilds t)

-- instances

data TreeABC
  = TreeA TreeABC TreeABC
  | TreeB TreeABC
  | TreeC
  deriving (Show, Eq)

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

  mkTree 'a' [x, y] = TreeA x y
  mkTree 'b' [x]    = TreeB x
  mkTree 'c' []     = TreeC


data InfixOpTree
  = InfixOne
  | InfixTwo
  | InfixPlus InfixOpTree InfixOpTree
  | InfixMulti InfixOpTree InfixOpTree
  deriving (Show, Eq, Ord)

instance RankedTree InfixOpTree where
  type LabelType InfixOpTree = String

  treeLabel InfixOne = "one"
  treeLabel InfixTwo = "two"
  treeLabel (InfixPlus _ _) = "plus"
  treeLabel (InfixMulti _ _) = "multi"

  treeChilds InfixOne = []
  treeChilds InfixTwo = []
  treeChilds (InfixPlus x y) = [x, y]
  treeChilds (InfixMulti x y) = [x, y]

  treeLabelRank _ "one" = 0
  treeLabelRank _ "two" = 0
  treeLabelRank _ "plus" = 2
  treeLabelRank _ "multi" = 2

  mkTree "one" [] = InfixOne
  mkTree "two" [] = InfixTwo
  mkTree "plus" [x, y] = InfixPlus x y
  mkTree "multi" [x, y] = InfixMulti x y


data PostfixOpTree
  = PostfixOne PostfixOpTree
  | PostfixTwo PostfixOpTree
  | PostfixPlus PostfixOpTree
  | PostfixMulti PostfixOpTree
  | PostfixEnd
  deriving (Show, Eq, Ord)

instance RankedTree PostfixOpTree where
  type LabelType PostfixOpTree = String

  treeLabel (PostfixOne _)   = "one"
  treeLabel (PostfixTwo _)   = "two"
  treeLabel (PostfixPlus _)  = "plus"
  treeLabel (PostfixMulti _) = "multi"
  treeLabel PostfixEnd       = "$"

  treeChilds (PostfixOne x)   = [x]
  treeChilds (PostfixTwo x)   = [x]
  treeChilds (PostfixPlus x)  = [x]
  treeChilds (PostfixMulti x) = [x]
  treeChilds PostfixEnd       = []

  treeLabelRank _ "one"   = 1
  treeLabelRank _ "two"   = 1
  treeLabelRank _ "plus"  = 1
  treeLabelRank _ "multi" = 1
  treeLabelRank _ "$"     = 0

  mkTree "one"   [x] = PostfixOne x
  mkTree "two"   [x] = PostfixTwo x
  mkTree "plus"  [x] = PostfixPlus x
  mkTree "multi" [x] = PostfixMulti x
  mkTree "$"     []  = PostfixEnd
