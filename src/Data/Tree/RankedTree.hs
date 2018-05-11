{-# LANGUAGE DerivingStrategies #-}

module Data.Tree.RankedTree
  ( -- common
    RankedTree (..)
  , RankNumber
  , NodeVec
  , treeRank
  , foldTree
  , showTreeWithPrinter
  , showTree
  , showTreeForm
  , lengthTree
  , RtConstraint
  , RtApply

    -- wrapper
  , WrappedRankedTree (..)

    -- bottom
  , bottomLabel
  ) where

import           SmttPrelude

type RankNumber = Int
type NodeVec    = Vector

-- | Ranked Labeled Tree Class
--
-- Conditions:
--
-- skip:prop> treeRank t == length (treeChilds t)
-- skip:prop> mkTree (treeLabel t) (treeChilds t) == t
--
-- and, other methods are same as default implementations.
--
class RankedTree t where
  type LabelType t :: Type

  treeLabel :: t -> LabelType t
  treeChilds :: t -> NodeVec t

  treeLabelRank :: Proxy t -> LabelType t -> RankNumber

  mkTree :: LabelType t -> NodeVec t -> t
  mkTree l ts = let r = length ts in if r == labelRank
      then mkTreeUnchecked l ts
      else error $ "expected rank " <> show labelRank <> " label, but actual rank " <> show r
    where
      labelRank = treeLabelRank (Proxy @t) l

  mkTreeUnchecked :: LabelType t -> NodeVec t -> t

  modifyChilds :: (t -> t) -> t -> t
  modifyChilds f t = mkTreeUnchecked (treeLabel t) $ f <$> treeChilds t

treeRank :: forall t. RankedTree t => t -> RankNumber
treeRank = treeLabelRank (Proxy @t) . treeLabel

foldTree :: RankedTree t => (LabelType t -> NodeVec b -> b) -> t -> b
foldTree f = go where
  go t = f (treeLabel t) $ go <$> treeChilds t

showTreeWithPrinter :: RtConstraint t l => (l -> String) -> t -> String
showTreeWithPrinter f = foldTree go
  where
    go l childs = f l <> childsStr childs

    childsStr ts
      | null ts = ""
      | otherwise = "(" <> intercalate "," ts <> ")"

showTree :: (RankedTree t, Show (LabelType t)) => t -> String
showTree = showTreeWithPrinter show

showTreeForm :: (RankedTree t) => t -> String
showTreeForm = showTreeWithPrinter (const "*")

lengthTree :: forall t. RankedTree t => t -> Int
lengthTree = length .# RankedTreeWrapper @t @(LabelType t)


type RtConstraint t l = (RankedTree t, l ~ LabelType t)
type RtApply tz t = tz t (LabelType t)

-- wrapper

newtype WrappedRankedTree t l = RankedTreeWrapper
  { unwrapRankedTree :: t
  }
  deriving (Generic)
  deriving newtype Hashable

instance (RtConstraint t l, Eq l) => Eq (WrappedRankedTree t l) where
  t1 == t2 = treeLabel t1 == treeLabel t2 && treeChilds t1 == treeChilds t2

instance (RtConstraint t l, Ord l) => Ord (WrappedRankedTree t l) where
  t1 `compare` t2
    =  (treeLabel  t1 `compare` treeLabel  t2)
    <> (treeChilds t1 `compare` treeChilds t2)

instance (RtConstraint t l, Show l) => Show (WrappedRankedTree t l) where
  show = showTree

instance RtConstraint t l => RankedTree (WrappedRankedTree t l) where
  type LabelType (WrappedRankedTree t l) = l

  treeLabel (RankedTreeWrapper t) = treeLabel t
  treeChilds (RankedTreeWrapper t) = coerce $ treeChilds t
  treeLabelRank = coerce (treeLabelRank @t)

  mkTree l = RankedTreeWrapper #. mkTree l .# coerce
  mkTreeUnchecked l = RankedTreeWrapper #. mkTreeUnchecked l .# coerce

type instance Element (WrappedRankedTree t l) = l

instance RtConstraint t l => MonoFoldable (WrappedRankedTree t l) where
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


-- bottom

bottomLabel :: l
bottomLabel = error "bottom label (rank: 0)"
