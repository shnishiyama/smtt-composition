{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE OverloadedLists #-}

module Data.Tree.RankedTree
  (
    -- main
    RankNumber
  , NodeVec
  , length
  , empty
  , (!)
  , treeTag
  , TreeTag
  , RankedTree (..)
  , treeRank
  , foldTree
  , showTree
  , RankedTreeWrapper (..)
  , (:$)
  , RtApply
  , RtConstraint

    -- ranked tree wrapper
  , RankedTreeWithInitial(..)
  , RankedTreeLabelWithInitial(..)
  , toRankedTreeWithoutInitial
  , toRankedTreeWithInitial

    -- bottom label
  , bottomLabel

    -- instances
  , TreeABC (..)
  , InfixOpTree (..)
  , PostfixOpTree (..)
  ) where

import           ClassyPrelude hiding (length)

import           Data.Profunctor.Unsafe
import           Data.Coerce
import           Data.Proxy
import qualified Data.Vector as V

type RankNumber = Int
type NodeVec    = V.Vector

length :: NodeVec a -> RankNumber
length = V.length

(!) :: NodeVec a -> RankNumber -> a
(!) = (V.!)

type TreeTag = Proxy

treeTag :: TreeTag t
treeTag = Proxy

-- | Ranked Labeled Tree Class
--
-- TODO:
-- * To use generic for deriving instance
-- * Builder using Template Haskell for easy building
--
-- Conditions:
-- * treeRank == length . treeChilds
-- * mkTree (treeLabel t) (treeChilds t) == t
--
class RankedTree t where
  type LabelType t :: *

  treeLabel :: t -> LabelType t
  treeChilds :: t -> NodeVec t

  treeLabelRank :: TreeTag t -> LabelType t -> RankNumber

  mkTree :: LabelType t -> NodeVec t -> t
  mkTree l ts = let r = length ts in if r == labelRank
      then mkTreeUnchecked l ts
      else error $ "expected rank " <> show labelRank <> " label, but actual rank " <> show r
    where
      labelRank = treeLabelRank (treeTag :: TreeTag t) l

  mkTreeUnchecked :: LabelType t -> NodeVec t -> t
  mkTreeUnchecked = mkTree

  modifyChilds :: (t -> t) -> t -> t
  modifyChilds f t = mkTreeUnchecked (treeLabel t) $ f <$> treeChilds t

treeRank :: forall t. RankedTree t => t -> RankNumber
treeRank = treeLabelRank (treeTag :: TreeTag t) . treeLabel

foldTree :: RankedTree t => (LabelType t -> NodeVec b -> b) -> t -> b
foldTree f = go where
  go t = f (treeLabel t) $ go <$> treeChilds t

showTree :: (RankedTree t, Show (LabelType t)) => t -> String
showTree t = show (treeLabel t) <> childsStr (treeChilds t)
  where
    childsStr ts
      | V.null ts = ""
      | otherwise = "(" <> intercalate "," (showTree <$> ts)  <> ")"

type t1 :$ t2 = t1 t2
infixr 0 :$

type RtApply tz t = tz t :$ LabelType t
type RtConstraint t l = (RankedTree t, l ~ LabelType t)

-- wrapper

newtype RankedTreeWrapper t = RankedTreeWrapper
  { unwrapRankedTree :: t
  } deriving (Show, Eq, Ord)

instance RankedTree t => RankedTree (RankedTreeWrapper t) where
  type LabelType (RankedTreeWrapper t) = LabelType t

  treeLabel (RankedTreeWrapper t) = treeLabel t
  treeChilds (RankedTreeWrapper t) = coerce $ treeChilds t
  treeLabelRank = coerce (treeLabelRank :: Proxy t -> LabelType t -> RankNumber)

  mkTree l = RankedTreeWrapper #. mkTree l . coerce
  mkTreeUnchecked l = RankedTreeWrapper #. mkTreeUnchecked l . coerce


type instance Element (RankedTreeWrapper t) = LabelType t

instance RankedTree t => MonoFoldable (RankedTreeWrapper t) where
  ofoldMap f = foldTree $ \a bs -> f a `mappend` ofoldMap id bs

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

-- bottom label

bottomLabel :: l
bottomLabel = error "rank (0) bottom label"

-- instances

data RankedTreeLabelWithInitial t l
  = InitialLabel
  | RankedTreeLabel l
  deriving (Eq, Ord)

instance Show l => Show (RankedTreeLabelWithInitial t l) where
  show InitialLabel        = "#"
  show (RankedTreeLabel l) = show l

data RankedTreeWithInitial t l
  = RankedTreeWithInitial (RankedTreeWithInitial t l)
  | RankedTreeWithoutInitial l (NodeVec :$ RankedTreeWithInitial t l)
  deriving (Eq, Ord)

instance (RtConstraint t l, Show l) => Show (RankedTreeWithInitial t l) where
  show = showTree

toRankedTreeWithoutInitial :: RankedTree t => t -> RtApply RankedTreeWithInitial t
toRankedTreeWithoutInitial = foldTree RankedTreeWithoutInitial

toRankedTreeWithInitial :: RankedTree t => t -> RtApply RankedTreeWithInitial t
toRankedTreeWithInitial = RankedTreeWithInitial . toRankedTreeWithoutInitial

instance RtConstraint t l => RankedTree (RankedTreeWithInitial t l) where
  type LabelType (RankedTreeWithInitial t l) = RankedTreeLabelWithInitial t l

  treeLabel (RankedTreeWithInitial _)      = InitialLabel
  treeLabel (RankedTreeWithoutInitial l _) = RankedTreeLabel l

  treeChilds (RankedTreeWithInitial t)       = V.singleton t
  treeChilds (RankedTreeWithoutInitial _ ts) = ts

  treeLabelRank _ InitialLabel        = 1
  treeLabelRank _ (RankedTreeLabel l) = treeLabelRank (Proxy :: Proxy t) l

  mkTreeUnchecked InitialLabel ts = RankedTreeWithInitial (ts ! 0)
  mkTreeUnchecked (RankedTreeLabel l) ts = RankedTreeWithoutInitial l ts


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

  mkTreeUnchecked 'a' ts = TreeA (ts ! 0) (ts ! 1)
  mkTreeUnchecked 'b' ts = TreeB (ts ! 0)
  mkTreeUnchecked 'c' _  = TreeC
  mkTreeUnchecked c   _  = error $ "not allowed label character: " <> show c


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
  treeLabelRank _ s       = error $ "not allowed label string: " <> show s

  mkTreeUnchecked "one"   _  = InfixOne
  mkTreeUnchecked "two"   _  = InfixTwo
  mkTreeUnchecked "plus"  ts = InfixPlus (ts ! 0) (ts ! 1)
  mkTreeUnchecked "multi" ts = InfixMulti (ts ! 0) (ts ! 1)
  mkTreeUnchecked s       _  = error $ "not allowed label string: " <> show s


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
  treeLabelRank _ s       = error $ "not allowed label string: " <> show s

  mkTreeUnchecked "one"   ts = PostfixOne (ts ! 0)
  mkTreeUnchecked "two"   ts = PostfixTwo (ts ! 0)
  mkTreeUnchecked "plus"  ts = PostfixPlus (ts ! 0)
  mkTreeUnchecked "multi" ts = PostfixMulti (ts ! 0)
  mkTreeUnchecked "$"     _  = PostfixEnd
  mkTreeUnchecked s       _  = error $ "not allowed label string: " <> show s
