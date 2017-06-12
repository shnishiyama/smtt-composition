{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

{-# LANGUAGE FlexibleContexts    #-}

module Data.Tree.RankedTree
  (
  -- main
    RankedTree (..)
  , treeRank
  , foldTree
  , RankedTreeWrapper (..)

  -- instances
  , TreeABC (..)
  , InfixOpTree (..)
  , PostfixOpTree (..)
  ) where

import ClassyPrelude

import           Control.CoercionExt

import           Data.Proxy
import           Data.MonoTraversable

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

  modifyChilds :: (t -> t) -> t -> t
  modifyChilds f t = mkTree (treeLabel t) $ map f (treeChilds t)

treeRank :: forall t. RankedTree t => t -> Int
treeRank = treeLabelRank (Proxy :: Proxy t) . treeLabel

foldTree :: RankedTree t => (LabelType t -> [b] -> b) -> t -> b
foldTree f = go where
  go t = f (treeLabel t) [go c | c <- treeChilds t]

showTree :: (RankedTree t, Show (LabelType t)) => t -> String
showTree t = show (treeLabel t) <> childsStr (treeChilds t)
  where
    childsStr [] = ""
    childsStr ts = "(" <> intercalate "," (map showTree ts)  <> ")"

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


type instance Element (RankedTreeWrapper t) = LabelType t

instance RankedTree t => MonoFoldable (RankedTreeWrapper t) where
  ofoldMap f = foldTree $ \a bs -> f a `mappend` mconcat bs

  ofoldl' = undefined

  ofoldr f s t = f (treeLabel t) child where
    child = foldr (flip $ ofoldr f) s $ treeChilds t

  ofoldl1Ex' = undefined

  ofoldr1Ex = undefined


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
  deriving (Eq, Ord)

-- | Appearance of infix operation trees
--
-- Examples:
--
-- >>> InfixMulti InfixOne (InfixPlus InfixOne InfixTwo)
-- "multi"("one","plus"("one","two"))
instance Show InfixOpTree where
  show = showTree

instance RankedTree InfixOpTree where
  type LabelType InfixOpTree = String

  treeLabel InfixOne         = "one"
  treeLabel InfixTwo         = "two"
  treeLabel (InfixPlus _ _)  = "plus"
  treeLabel (InfixMulti _ _) = "multi"

  treeChilds InfixOne         = []
  treeChilds InfixTwo         = []
  treeChilds (InfixPlus x y)  = [x, y]
  treeChilds (InfixMulti x y) = [x, y]

  treeLabelRank _ "one"   = 0
  treeLabelRank _ "two"   = 0
  treeLabelRank _ "plus"  = 2
  treeLabelRank _ "multi" = 2

  mkTree "one" []       = InfixOne
  mkTree "two" []       = InfixTwo
  mkTree "plus" [x, y]  = InfixPlus x y
  mkTree "multi" [x, y] = InfixMulti x y


data PostfixOpTree
  = PostfixOne PostfixOpTree
  | PostfixTwo PostfixOpTree
  | PostfixPlus PostfixOpTree
  | PostfixMulti PostfixOpTree
  | PostfixEnd
  deriving (Eq, Ord)

-- | Appearance of postfix operation trees
--
-- Examples:
--
-- >>> PostfixMulti $ PostfixOne $ PostfixPlus $ PostfixOne $ PostfixTwo $ PostfixEnd
-- "multi"("one"("plus"("one"("two"("$")))))
instance Show PostfixOpTree where
  show = showTree

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
