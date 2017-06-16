module Data.Tree.RankedTree.Zipper
  ( RankedTreeZipper(..)

    -- RTZipper
  , RTZipper -- for non type family supports
  , rtZipper

    -- operators
  , zoomInIdxRtZipper
  , zoomTopRtZipper
  , toTopTree
  , getTreeLabel
  ) where

import ClassyPrelude

import Data.Tree.RankedTree

-- RTZipper

data RTZCrumb t l = RTZCrumb
  { rtzcLabel :: l
  , rtzcLeft  :: [t]
  , rtzcRight :: [t]
  } deriving (Show, Eq, Ord)

type RankedTreeCrumb t = RTZCrumb t (LabelType t)

fromTreeCrumb :: RankedTree t => RankedTreeCrumb t -> t -> t
fromTreeCrumb RTZCrumb{..} t = mkTree rtzcLabel rtzcChilds
  where
    rtzcChilds = go rtzcLeft (t:rtzcRight)

    go = foldr (:)

-- |
--
-- >>> treeABCZipper = rtZipper (TreeA TreeC (TreeB TreeC))
-- >>> toTree <$> zoomInRtZipper treeABCZipper
-- Just TreeC
--
-- >>> toTree <$> (zoomInRtZipper >=> zoomRightRtZipper) treeABCZipper
-- Just (TreeB TreeC)
--
-- >>> :{
--   toTree <$>
--   (   zoomInRtZipper
--   >=> zoomRightRtZipper
--   >=> zoomOutRtZipper
--   ) treeABCZipper
-- :}
-- Just (TreeA (TreeB TreeC) TreeC)
--
-- >>> toTree <$> zoomOutRtZipper treeABCZipper
-- Nothing
--
-- >>> toTree <$> zoomRightRtZipper treeABCZipper
-- Nothing
--
data RTZipper t l = RTZipper
  { rtzTree   :: t
  , rtzCrumbs :: [RTZCrumb t l]
  } deriving (Show, Eq, Ord)

rtZipper :: RankedTree t => t -> RtApply RTZipper t
rtZipper t = RTZipper
  { rtzTree   = t
  , rtzCrumbs = []
  }

-- operators

class RankedTreeZipper tz where
  toTree :: RankedTree t => RtApply tz t -> t

  zoomInRtZipper :: RankedTree t => RtApply tz t -> Maybe (RtApply tz t)
  zoomOutRtZipper :: RankedTree t => RtApply tz t -> Maybe (RtApply tz t)
  zoomLeftRtZipper :: RankedTree t => RtApply tz t -> Maybe (RtApply tz t)
  zoomRightRtZipper :: RankedTree t => RtApply tz t -> Maybe (RtApply tz t)
  modifyTreeZipper :: RankedTree t => (t -> t) -> RtApply tz t -> RtApply tz t

  setTreeZipper :: RankedTree t => t -> RtApply tz t -> RtApply tz t
  setTreeZipper t = modifyTreeZipper $ const t

  walkZipper :: RankedTree t => (RtApply tz t -> Maybe (RtApply tz t)) -> RtApply tz t -> RtApply tz t
  walkZipper f = go where
    go tz = case f tz of
      Nothing  -> tz
      Just ntz -> go ntz

  walkLeftZipper :: RankedTree t => (t -> t) -> RtApply tz t -> RtApply tz t
  walkLeftZipper f = walkZipper $ (modifyTreeZipper f <$>) . zoomLeftRtZipper

  walkRightZipper :: RankedTree t => (t -> t) -> RtApply tz t -> RtApply tz t
  walkRightZipper f = walkZipper $ (modifyTreeZipper f <$>) . zoomRightRtZipper


instance RankedTreeZipper RTZipper where
  toTree = rtzTree

  zoomInRtZipper (RTZipper t cs) = case treeChilds t of
    []       -> Nothing
    (tc:tcs) -> Just RTZipper
      { rtzTree   = tc
      , rtzCrumbs = RTZCrumb (treeLabel t) [] tcs : cs
      }

  zoomOutRtZipper (RTZipper _ [])     = Nothing
  zoomOutRtZipper (RTZipper t (c:cs)) = Just RTZipper
    { rtzTree   = fromTreeCrumb c t
    , rtzCrumbs = cs
    }

  zoomLeftRtZipper (RTZipper _ [])     = Nothing
  zoomLeftRtZipper (RTZipper t (c:cs)) = case rtzcLeft c of
    []       -> Nothing
    (tl:tls) -> Just RTZipper
      { rtzTree   = tl
      , rtzCrumbs = crumb tls : cs
      }
    where
      crumb ls = RTZCrumb (rtzcLabel c) ls (t : rtzcRight c)


  walkLeftZipper _ tz@(RTZipper _ [])  = tz
  walkLeftZipper f (RTZipper t (c:cs)) = go t (rtzcLeft c) (rtzcRight c)
    where
      go tl []        trs = RTZipper tl $ crumb trs : cs
      go tl (tl':tls) trs = go (f tl') tls (tl:trs)

      crumb = RTZCrumb (rtzcLabel c) []

  zoomRightRtZipper (RTZipper _ [])     = Nothing
  zoomRightRtZipper (RTZipper t (c:cs)) = case rtzcRight c of
    []       -> Nothing
    (tr:trs) -> Just RTZipper
      { rtzTree   = tr
      , rtzCrumbs = crumb trs : cs
      }
    where
      crumb = RTZCrumb (rtzcLabel c) (t : rtzcLeft c)

  walkRightZipper _ tz@(RTZipper _ [])  = tz
  walkRightZipper f (RTZipper t (c:cs)) = go t (rtzcLeft c) (rtzcRight c)
    where
      go tl tls []        = RTZipper (f tl) $ crumb tls : cs
      go tl tls (tl':trs) = go (f tl') (tl:tls) trs

      crumb tls = RTZCrumb (rtzcLabel c) tls []

  modifyTreeZipper f tz = RTZipper
    { rtzTree   = f $ rtzTree tz
    , rtzCrumbs = rtzCrumbs tz
    }

  setTreeZipper t tz = RTZipper
    { rtzTree   = t
    , rtzCrumbs = rtzCrumbs tz
    }

zoomInIdxRtZipper :: (RankedTree t, RankedTreeZipper tz) => Int -> RtApply tz t -> Maybe (RtApply tz t)
zoomInIdxRtZipper = go where
  go n | n < 1 = error "must a positive number"
  go 1 = zoomInRtZipper
  go n = zoomRightRtZipper <=< go (n - 1)

zoomTopRtZipper :: (RankedTree t, RankedTreeZipper tz) => RtApply tz t -> RtApply tz t
zoomTopRtZipper tz = maybe tz zoomTopRtZipper $ zoomOutRtZipper tz

toTopTree :: (RankedTree t, RankedTreeZipper tz) => RtApply tz t -> t
toTopTree = toTree . zoomTopRtZipper

getTreeLabel :: (RankedTree t, RankedTreeZipper tz) => RtApply tz t -> LabelType t
getTreeLabel = treeLabel . toTree
