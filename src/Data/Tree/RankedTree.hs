{-# LANGUAGE FlexibleContexts    #-}

module Data.Tree.RankedTree
  (
  -- main
    RankedTree (..)
  , treeRank
  , foldTree
  , showTree
  , RankedTreeWrapper (..)
  , RtApply
  , RtConstraint

  -- ranked tree wrapper
  , RankedTreeWithInitial(..)
  , RankedTreeLabelWithInitial(..)
  , toRankedTreeWithInitial

  -- instances
  , TreeABC (..)
  , InfixOpTree (..)
  , PostfixOpTree (..)
  ) where

import           ClassyPrelude

import           Data.Profunctor.Unsafe
import           Data.Coerce
import           Data.Proxy

-- | Ranked Labeled Tree Class
--
-- TODO:
-- * To use generic for deriving instance
-- * Builder using Template Haskell for easy building
-- * Rewrite to use vector for indexing access
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

type RtApply tz t = tz t (LabelType t)
type RtConstraint t l = (RankedTree t, l ~ LabelType t)

-- wrapper

newtype RankedTreeWrapper t = RankedTreeWrapper
  { unwrapRankedTree :: t
  } deriving (Show, Eq, Ord)

instance RankedTree t => RankedTree (RankedTreeWrapper t) where
  type LabelType (RankedTreeWrapper t) = LabelType t

  treeLabel (RankedTreeWrapper t) = treeLabel t
  treeChilds (RankedTreeWrapper t) = coerce $ treeChilds t
  treeLabelRank = coerce (treeLabelRank :: Proxy t -> LabelType t -> Int)

  mkTree l = RankedTreeWrapper #. mkTree l . coerce


type instance Element (RankedTreeWrapper t) = LabelType t

instance RankedTree t => MonoFoldable (RankedTreeWrapper t) where
  ofoldMap f = foldTree $ \a bs -> f a `mappend` mconcat bs

  ofoldl' f s t = g $ f s $ treeLabel t where
    g !s' = foldl' (ofoldl' f) s' $ treeChilds t

  ofoldr f s t = f (treeLabel t) child where
    child = foldr (flip $ ofoldr f) s $ treeChilds t

  ofoldl1Ex' f xs = fromMaybe errorEmpty $ ofoldl' mf Nothing xs where
    errorEmpty = error "ofoldl1Ex': empty structure"

    mf m y = Just $ case m of
      Nothing -> y
      Just x  -> f x y

  ofoldr1Ex f xs = fromMaybe errorEmpty $ ofoldr mf Nothing xs where
    errorEmpty = error "ofoldr1Ex: empty structure"

    mf x m = Just $ case m of
      Nothing -> x
      Just y  -> f x y


-- instances

data RankedTreeLabelWithInitial l
  = InitialLabel
  | RankedTreeLabel l
  deriving (Eq, Ord)

instance Show l => Show (RankedTreeLabelWithInitial l) where
  show InitialLabel        = "#"
  show (RankedTreeLabel l) = show l

data RankedTreeWithInitial t l
  = RankedTreeWithInitial (RankedTreeWithInitial t l)
  | RankedTreeWithoutInitial l [RankedTreeWithInitial t l]
  deriving (Eq, Ord)

instance (RtConstraint t l, Show l) => Show (RankedTreeWithInitial t l) where
  show = showTree

toRankedTreeWithInitial :: RankedTree t => t -> RankedTreeWithInitial t (LabelType t)
toRankedTreeWithInitial = RankedTreeWithInitial . go where
  go = foldTree RankedTreeWithoutInitial

instance RtConstraint t l => RankedTree (RankedTreeWithInitial t l) where
  type LabelType (RankedTreeWithInitial t l) = RankedTreeLabelWithInitial l

  treeLabel (RankedTreeWithInitial _)      = InitialLabel
  treeLabel (RankedTreeWithoutInitial l _) = RankedTreeLabel l

  treeChilds (RankedTreeWithInitial t)       = [t]
  treeChilds (RankedTreeWithoutInitial _ ts) = ts

  treeLabelRank _ InitialLabel        = 1
  treeLabelRank _ (RankedTreeLabel l) = treeLabelRank (Proxy :: Proxy t) l

  mkTree InitialLabel        [t] = RankedTreeWithInitial t
  mkTree (RankedTreeLabel l) ts  = RankedTreeWithoutInitial l ts
  mkTree InitialLabel        _   = error "not allowed tree"


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
  treeLabelRank _ c   = error $ "not allowed label character: " <> show c

  mkTree 'a' [x, y]  = TreeA x y
  mkTree 'b' [x]     = TreeB x
  mkTree 'c' []      = TreeC
  mkTree c   ts      = error $ "not allowed tree: (" <> show c <> "," <> show ts <> ")"


-- | Infix operation tree
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
-- >>> InfixMulti InfixOne (InfixPlus InfixTwo InfixOne)
-- "multi"("one","plus"("two","one"))
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
  treeLabelRank _ str     = error $ "not allowed label string: " <> show str

  mkTree "one"   []     = InfixOne
  mkTree "two"   []     = InfixTwo
  mkTree "plus"  [x, y] = InfixPlus x y
  mkTree "multi" [x, y] = InfixMulti x y
  mkTree str     ts     = error $ "not allowed tree: (" <> show str <> "," <> show ts <> ")"


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
-- >>> PostfixTwo $ PostfixOne $ PostfixTwo $ PostfixPlus $ PostfixMulti $ PostfixEnd
-- "two"("one"("two"("plus"("multi"("$")))))
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
  treeLabelRank _ str     = error $ "not allowed label string: " <> show str

  mkTree "one"   [x] = PostfixOne x
  mkTree "two"   [x] = PostfixTwo x
  mkTree "plus"  [x] = PostfixPlus x
  mkTree "multi" [x] = PostfixMulti x
  mkTree "$"     []  = PostfixEnd
  mkTree str     ts  = error $ "not allowed tree: (" <> show str <> "," <> show ts <> ")"
