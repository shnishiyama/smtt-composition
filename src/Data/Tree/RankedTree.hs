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
  , lengthTree
  , (:$)
  , RtApply
  , RtConstraint

    -- ranked tree wrapper
  , RankedTreeWrapper (..)
  , wrapRankedTree

    -- ranked tree with initial
  , RankedTreeWithInitial(..)
  , RankedTreeLabelWithInitial(..)
  , toRankedTreeWithoutInitial
  , toRankedTreeWithInitial

    -- bottom label
  , bottomLabel
  ) where

import           ClassyPrelude

import           Data.Coerce
import           Data.Profunctor.Unsafe
import           Data.Proxy
import qualified Data.Vector            as V

type RankNumber = Int
type NodeVec    = V.Vector

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
      labelRank = treeLabelRank (treeTag @t) l

  mkTreeUnchecked :: LabelType t -> NodeVec t -> t
  mkTreeUnchecked = mkTree

  modifyChilds :: (t -> t) -> t -> t
  modifyChilds f t = mkTreeUnchecked (treeLabel t) $ f <$> treeChilds t

treeRank :: forall t. RankedTree t => t -> RankNumber
treeRank = treeLabelRank (treeTag @t) . treeLabel

foldTree :: RankedTree t => (LabelType t -> NodeVec b -> b) -> t -> b
foldTree f = go where
  go t = f (treeLabel t) $ go <$> treeChilds t

showTree :: (RankedTree t, Show :$ LabelType t) => t -> String
showTree t = show (treeLabel t) <> childsStr (treeChilds t)
  where
    childsStr ts
      | V.null ts = ""
      | otherwise = "(" <> intercalate "," (showTree <$> ts)  <> ")"

lengthTree :: forall t l. RtConstraint t l => t -> Int
lengthTree = olength .# RankedTreeWrapper @t @l

type t1 :$ t2 = t1 t2
infixr 0 :$

type RtApply tz t = tz t :$ LabelType t
type RtConstraint t l = (RankedTree t, l ~ LabelType t)

-- wrapper

newtype RankedTreeWrapper t l = RankedTreeWrapper
  { unwrapRankedTree :: t
  }

wrapRankedTree :: RankedTree t => t -> RtApply RankedTreeWrapper t
wrapRankedTree = coerce

instance (RtConstraint t l, Eq l) => Eq (RankedTreeWrapper t l) where
  t1 == t2 = treeLabel t1 == treeLabel t2 && treeChilds t1 == treeChilds t2

instance (RtConstraint t l, Ord l) => Ord (RankedTreeWrapper t l) where
  t1 `compare` t2 = case treeLabel t1 `compare` treeLabel t2 of
    EQ -> treeChilds t1 `compare` treeChilds t2
    r  -> r

instance (RtConstraint t l, Show l) => Show (RankedTreeWrapper t l) where
  show = showTree

instance RtConstraint t l => RankedTree (RankedTreeWrapper t l) where
  type LabelType (RankedTreeWrapper t l) = l

  treeLabel (RankedTreeWrapper t) = treeLabel t
  treeChilds (RankedTreeWrapper t) = coerce $ treeChilds t
  treeLabelRank = coerce (treeLabelRank @ t)

  mkTree l = RankedTreeWrapper #. mkTree l . coerce
  mkTreeUnchecked l = RankedTreeWrapper #. mkTreeUnchecked l . coerce


type instance Element (RankedTreeWrapper t l) = l

instance RtConstraint t l => MonoFoldable (RankedTreeWrapper t l) where
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

-- tree with initial

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
  treeLabelRank _ (RankedTreeLabel l) = treeLabelRank (treeTag @t) l

  mkTreeUnchecked InitialLabel        ts = RankedTreeWithInitial (ts ! 0)
  mkTreeUnchecked (RankedTreeLabel l) ts = RankedTreeWithoutInitial l ts
