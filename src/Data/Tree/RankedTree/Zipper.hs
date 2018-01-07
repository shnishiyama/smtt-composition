{-# LANGUAGE NoStrict #-}

module Data.Tree.RankedTree.Zipper
  ( -- common
    RankedTreeZipper(..)
  , zoomTopRtZipper
  , toTopTree
  , toTreeLabel
  , zoomNextLeftOutZipper
  , zoomNextLeftOutZipper1
  , zoomNextRightOutZipper
  , zoomNextRightOutZipper1

    -- a main instance
  , RTZipper
  , rtZipper
  , RtPathZipper (..)
  , rtPathZipper
  , _rtPathList
  ) where

import           SattPrelude

import           Control.Arrow
import           Data.Tree.RankedTree
import qualified Data.Vector          as V


-- | A class of zippers of ranked tree
class RankedTreeZipper tz where
  toZipper :: RtConstraint t l => t -> tz t l
  toTree :: RtConstraint t l => tz t l -> t

  zoomInRtZipper :: RtConstraint t l => tz t l -> Maybe (tz t l)
  zoomInRtZipper = zoomInIdxRtZipper 0

  zoomOutRtZipper :: RtConstraint t l => tz t l -> Maybe (tz t l)

  zoomLeftRtZipper :: RtConstraint t l => tz t l -> Maybe (tz t l)

  zoomRightRtZipper :: RtConstraint t l => tz t l -> Maybe (tz t l)

  zoomInIdxRtZipper :: RtConstraint t l => RankNumber -> tz t l -> Maybe (tz t l)
  zoomInIdxRtZipper n
    | n < 0     = const Nothing
    | otherwise = go n zoomInRtZipper
    where
      go 0  f = f
      go n' f = go (n' - 1) (f >=> zoomLeftRtZipper)

  modifyTreeZipper :: RtConstraint t l => (t -> t) -> tz t l -> tz t l
  modifyTreeZipper f z = setTreeZipper (f $ toTree z) z

  setTreeZipper :: RtConstraint t l => t -> tz t l -> tz t l
  setTreeZipper t = modifyTreeZipper $ const t

  walkZipper :: RtConstraint t l => (tz t l -> Maybe (tz t l)) -> tz t l -> tz t l
  walkZipper f = go where
    go tz = case f tz of
      Nothing  -> tz
      Just ntz -> go ntz

  walkLeftZipper :: RtConstraint t l => (t -> t) -> tz t l -> tz t l
  walkLeftZipper f = walkZipper $ (modifyTreeZipper f <$>) . zoomLeftRtZipper

  walkRightZipper :: RtConstraint t l => (t -> t) -> tz t l -> tz t l
  walkRightZipper f = walkZipper $ (modifyTreeZipper f <$>) . zoomRightRtZipper


zoomTopRtZipper :: (RankedTreeZipper tz, RtConstraint t l) => tz t l -> tz t l
zoomTopRtZipper tz = maybe tz zoomTopRtZipper $ zoomOutRtZipper tz

toTopTree :: (RankedTreeZipper tz, RtConstraint t l) => tz t l -> t
toTopTree = toTree . zoomTopRtZipper

toTreeLabel :: (RankedTreeZipper tz, RtConstraint t l) => tz t l -> l
toTreeLabel = treeLabel . toTree

checkResult :: (a -> Bool) -> a -> Maybe a
checkResult f x = if f x then pure x else empty

zoomNextLeftOutZipperBase :: (RankedTreeZipper tz, RtConstraint t l)
  => Bool -> (tz t l -> Bool) -> tz t l -> Maybe (tz t l)
zoomNextLeftOutZipperBase b f = runKleisli $ if b then goIn else goLeftOut
  where
    goIn
      =   Kleisli (checkResult f)
      <+> (Kleisli zoomInRtZipper >>> goIn)
      <+> goLeftOut

    goLeftOut
      =   (Kleisli zoomLeftRtZipper >>> goIn)
      <+> (Kleisli zoomOutRtZipper >>> goLeftOut)

{-# INLINE zoomNextLeftOutZipperBase #-}

zoomNextLeftOutZipper :: (RankedTreeZipper tz, RtConstraint t l)
  => (tz t l -> Bool) -> tz t l -> Maybe (tz t l)
zoomNextLeftOutZipper = zoomNextLeftOutZipperBase True

zoomNextLeftOutZipper1 :: (RankedTreeZipper tz, RtConstraint t l)
  => (tz t l -> Bool) -> tz t l -> Maybe (tz t l)
zoomNextLeftOutZipper1 = zoomNextLeftOutZipperBase False

zoomNextRightOutZipperBase :: (RankedTreeZipper tz, RtConstraint t l)
  => Bool -> (tz t l -> Bool) -> tz t l -> Maybe (tz t l)
zoomNextRightOutZipperBase b f = runKleisli $ if b then goIn else goRightOut
  where
    goIn
      =   Kleisli (checkResult f)
      <+> (Kleisli zoomInRtZipper >>> goIn)
      <+> goRightOut

    goRightOut
      =   (Kleisli zoomRightRtZipper >>> goIn)
      <+> (Kleisli zoomOutRtZipper >>> goRightOut)

{-# INLINE zoomNextRightOutZipperBase #-}

zoomNextRightOutZipper :: (RankedTreeZipper tz, RtConstraint t l)
  => (tz t l -> Bool) -> tz t l -> Maybe (tz t l)
zoomNextRightOutZipper = zoomNextRightOutZipperBase True

zoomNextRightOutZipper1 :: (RankedTreeZipper tz, RtConstraint t l)
  => (tz t l -> Bool) -> tz t l -> Maybe (tz t l)
zoomNextRightOutZipper1 = zoomNextRightOutZipperBase False


-- RTZipper

data RTZCrumb t l = RTZCrumb
  { rtzcLabel  :: l
  , rtzcIndex  :: RankNumber
  , rtzcLength :: RankNumber
  , rtzcChilds :: NodeVec t
  } deriving (Show, Eq, Ord, Generic)

fromTreeCrumb :: RtConstraint t l => RTZCrumb t l -> t -> t
fromTreeCrumb RTZCrumb{..} t = mkTreeUnchecked rtzcLabel rtzcChilds'
  where
    rtzcChilds' = rtzcChilds V.// [(rtzcIndex, t)]

-- | A zipper of ranked tree
--
-- Examples:
--
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.RankedTree.Label
-- >>> type ABCAlphabet = TaggedRankedAlphabet ['("A", 2), '("B", 1), '("C", 0)]
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> :{
-- treeABCSample :: RankedLabelledTree ABCAlphabet
-- treeABCSample = mkLabelledTree a
--   [ mkTree c []
--   , mkTree b [mkTree c []]
--   ]
-- :}
--
-- >>> treeABCZipper = rtZipper treeABCSample
-- >>> toTree treeABCZipper
-- A(C,B(C))
-- >>> toTree <$> zoomInRtZipper treeABCZipper
-- Just C
-- >>> toTree <$> (zoomInRtZipper >=> zoomRightRtZipper) treeABCZipper
-- Just B(C)
-- >>> :{
--   toTree <$>
--   (   zoomInRtZipper
--   >=> zoomRightRtZipper
--   >=> zoomOutRtZipper
--   ) treeABCZipper
-- :}
-- Just A(C,B(C))
--
-- >>> :{
-- toTopTree
--   <$> setTreeZipper (mkTree a [mkTree c [], mkTree c []])
--   <$> zoomInRtZipper treeABCZipper
-- :}
-- Just A(A(C,C),B(C))
--
-- >>> toTree <$> zoomOutRtZipper treeABCZipper
-- Nothing
-- >>> toTree <$> zoomRightRtZipper treeABCZipper
-- Nothing
-- >>> toTree <$> (zoomNextRightOutZipper (const True) <=< zoomInRtZipper) treeABCZipper
-- Just C
-- >>> toTree <$> (zoomNextRightOutZipper1 (const True) <=< zoomInRtZipper) treeABCZipper
-- Just B(C)
--
data RTZipper t l = RTZipper
  { rtzTree   :: t
  , rtzCrumbs :: [RTZCrumb t l]
  } deriving (Show, Eq, Ord, Generic)

rtZipper :: RtConstraint t l => t -> RTZipper t l
rtZipper t = RTZipper
  { rtzTree   = t
  , rtzCrumbs = []
  }

instance RankedTreeZipper RTZipper where
  toZipper = rtZipper
  toTree = rtzTree

  zoomInIdxRtZipper n (RTZipper t cs)
    | n >= len  = Nothing
    | otherwise = Just RTZipper
        { rtzTree   = tcs `indexEx` n
        , rtzCrumbs = RTZCrumb
          { rtzcLabel  = treeLabel t
          , rtzcIndex  = n
          , rtzcLength = len
          , rtzcChilds = tcs
          } : cs
        }
    where
      len = length tcs

      tcs = treeChilds t

  zoomOutRtZipper (RTZipper _ [])     = Nothing
  zoomOutRtZipper (RTZipper t (c:cs)) = Just RTZipper
    { rtzTree   = fromTreeCrumb c t
    , rtzCrumbs = cs
    }

  zoomLeftRtZipper (RTZipper _ []) = Nothing
  zoomLeftRtZipper (RTZipper t (c@RTZCrumb{..}:cs))
    | rtzcIndex == 0 = Nothing
    | otherwise      = Just RTZipper
      { rtzTree   = rtzcChilds `indexEx` nrtzcIndex
      , rtzCrumbs = c
        { rtzcIndex  = nrtzcIndex
        , rtzcChilds = rtzcChilds V.// [(rtzcIndex, t)]
        } : cs
      }
      where
        nrtzcIndex = rtzcIndex - 1

  walkLeftZipper _ tz@(RTZipper _ [])  = tz
  walkLeftZipper f (RTZipper t (c@RTZCrumb{..}:cs)) = go t rtzcIndex []
    where
      go t' 0 itx = RTZipper t' $ c
        { rtzcIndex  = 0
        , rtzcChilds = rtzcChilds V.// itx
        } : cs
      go t' n itx = let n' = n - 1
        in go (f $ rtzcChilds `indexEx` n') n' $ (n, t'):itx

  zoomRightRtZipper (RTZipper _ []) = Nothing
  zoomRightRtZipper (RTZipper t (c@RTZCrumb{..}:cs))
    | rtzcIndex == rtzcLength - 1 = Nothing
    | otherwise                   = Just RTZipper
      { rtzTree   = rtzcChilds `indexEx` nrtzcIndex
      , rtzCrumbs = c
        { rtzcIndex  = nrtzcIndex
        , rtzcChilds = rtzcChilds V.// [(rtzcIndex, t)]
        } : cs
      }
      where
        nrtzcIndex = rtzcIndex + 1

  walkRightZipper _ tz@(RTZipper _ [])  = tz
  walkRightZipper f (RTZipper t (c@RTZCrumb{..}:cs)) = go t rtzcIndex []
    where
      rtzcIndexMax = rtzcLength - 1

      go t' n itx
        | n == rtzcIndexMax = RTZipper t' $ c
          { rtzcIndex  = n
          , rtzcChilds = rtzcChilds V.// itx
          } : cs
        | otherwise = let n' = n + 1
          in go (f $ rtzcChilds `indexEx` n') n' $ (n, t'):itx

  modifyTreeZipper f tz = tz
    { rtzTree   = f $ rtzTree tz
    }

  setTreeZipper t tz = tz
    { rtzTree   = t
    }


-- | A zipper with path
--
-- Examples:
--
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.RankedTree.Label
-- >>> type ABCAlphabet = TaggedRankedAlphabet ['("A", 2), '("B", 1), '("C", 0)]
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> :{
-- treeABCSample :: RankedLabelledTree ABCAlphabet
-- treeABCSample = mkLabelledTree a
--   [ mkTree c []
--   , mkTree b [mkTree c []]
--   ]
-- :}
--
-- >>> treeABCZipper = toZipper @(RtPathZipper RTZipper) treeABCSample
-- >>> toTreeWithPath = toTree &&& rtPathList
-- >>> toTreeWithPath treeABCZipper
-- (A(C,B(C)),[])
-- >>> toTreeWithPath <$> zoomInRtZipper treeABCZipper
-- Just (C,[0])
-- >>> toTreeWithPath <$> (zoomInRtZipper >=> zoomRightRtZipper) treeABCZipper
-- Just (B(C),[1])
-- >>> :{
--   toTreeWithPath <$>
--   (   zoomInRtZipper
--   >=> zoomRightRtZipper
--   >=> zoomOutRtZipper
--   ) treeABCZipper
-- :}
-- Just (A(C,B(C)),[])
--
-- >>> :{
-- toTopTree
--   <$> setTreeZipper (mkTree a [mkTree c [], mkTree c []])
--   <$> zoomInRtZipper treeABCZipper
-- :}
-- Just A(A(C,C),B(C))
--
-- >>> toTreeWithPath <$> zoomOutRtZipper treeABCZipper
-- Nothing
-- >>> toTreeWithPath <$> zoomRightRtZipper treeABCZipper
-- Nothing
-- >>> toTreeWithPath <$> (zoomNextRightOutZipper (const True) <=< zoomInRtZipper) treeABCZipper
-- Just (C,[0])
-- >>> toTreeWithPath <$> (zoomNextRightOutZipper1 (const True) <=< zoomInRtZipper) treeABCZipper
-- Just (B(C),[1])
--
data RtPathZipper tz t l = RtPathZipper
  { rtPathList           :: [RankNumber]
  , rtPathInternalZipper :: tz t l
  } deriving (Eq, Ord, Show, Generic)

rtPathZipper :: forall tz t l. (RankedTreeZipper tz, RtConstraint t l)
  => t -> RtPathZipper tz t l
rtPathZipper = toZipper

_rtPathList :: Lens' (RtPathZipper tz t l) [RankNumber]
_rtPathList = lens rtPathList $ \p pl -> p { rtPathList = pl }

instance RankedTreeZipper tz => RankedTreeZipper (RtPathZipper tz) where
  toZipper t = RtPathZipper
    { rtPathList           = []
    , rtPathInternalZipper = toZipper t
    }
  toTree = toTree . rtPathInternalZipper

  zoomInIdxRtZipper i RtPathZipper{..}
    = zoomInIdxRtZipper i rtPathInternalZipper <&> \ntz -> RtPathZipper
      { rtPathList           = i:rtPathList
      , rtPathInternalZipper = ntz
      }

  zoomOutRtZipper RtPathZipper{..} = case rtPathList of
    []   -> Nothing
    _:pl -> zoomOutRtZipper rtPathInternalZipper <&> \ntz -> RtPathZipper
      { rtPathList           = pl
      , rtPathInternalZipper = ntz
      }

  zoomLeftRtZipper RtPathZipper{..} = case rtPathList of
    []   -> Nothing
    i:pl -> zoomLeftRtZipper rtPathInternalZipper <&> \ntz -> RtPathZipper
      { rtPathList           = (i - 1):pl
      , rtPathInternalZipper = ntz
      }

  zoomRightRtZipper RtPathZipper{..} = case rtPathList of
    []   -> Nothing
    i:pl -> zoomRightRtZipper rtPathInternalZipper <&> \ntz -> RtPathZipper
      { rtPathList           = (i + 1):pl
      , rtPathInternalZipper = ntz
      }

  modifyTreeZipper f p@RtPathZipper{..} = p
    { rtPathInternalZipper = modifyTreeZipper f rtPathInternalZipper
    }

  setTreeZipper t p@RtPathZipper{..} = p
    { rtPathInternalZipper = setTreeZipper t rtPathInternalZipper
    }
