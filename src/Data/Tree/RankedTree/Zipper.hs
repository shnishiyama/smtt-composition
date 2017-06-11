module Data.Tree.RankedTree.Zipper
  ( RankedTreeZipper
  , rtZipper
  , toTree
  , zoomInRtZipper
  , zoomOutRtZipper
  , zoomLeftRtZipper
  , walkLeftZipper
  , zoomRightRtZipper
  , walkRightZipper
  , modifyTreeZipper
  , setTreeZipper
  ) where

import ClassyPrelude

import Data.Tree.RankedTree

data RTZCrumb t l = RTZCrumb
  { rtzcLabel :: l
  , rtzcLeft  :: [t]
  , rtzcRight :: [t]
  } deriving (Show, Eq)

type RankedTreeCrumb t = RTZCrumb t (LabelType t)

fromTreeCrumb :: RankedTree t => RankedTreeCrumb t -> t -> t
fromTreeCrumb RTZCrumb{..} t = mkTree rtzcLabel rtzcChilds
  where
    rtzcChilds = go rtzcLeft (t:rtzcRight)

    go = foldl' $ flip (:)

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
  } deriving (Show, Eq)

type RankedTreeZipper t = RTZipper t (LabelType t)

rtZipper :: RankedTree t => t -> RankedTreeZipper t
rtZipper t = RTZipper
  { rtzTree   = t
  , rtzCrumbs = []
  }

toTree :: RankedTree t => RankedTreeZipper t -> t
toTree = rtzTree


zoomInRtZipper :: RankedTree t => RankedTreeZipper t -> Maybe (RankedTreeZipper t)
zoomInRtZipper (RTZipper t cs) = case treeChilds t of
  []       -> Nothing
  (tc:tcs) -> Just RTZipper
    { rtzTree   = tc
    , rtzCrumbs = toCrumb (treeLabel t) tcs : cs
    }
  where
    toCrumb l rs = RTZCrumb
      { rtzcLabel = l
      , rtzcLeft  = []
      , rtzcRight = rs
      }

zoomOutRtZipper :: RankedTree t => RankedTreeZipper t -> Maybe (RankedTreeZipper t)
zoomOutRtZipper (RTZipper _ [])     = Nothing
zoomOutRtZipper (RTZipper t (c:cs)) = Just RTZipper
  { rtzTree   = fromTreeCrumb c t
  , rtzCrumbs = cs
  }

zoomLeftRtZipper :: RankedTree t => RankedTreeZipper t -> Maybe (RankedTreeZipper t)
zoomLeftRtZipper (RTZipper _ [])     = Nothing
zoomLeftRtZipper (RTZipper t (c:cs)) = case rtzcLeft c of
  []       -> Nothing
  (tl:tls) -> Just RTZipper
    { rtzTree   = tl
    , rtzCrumbs = crumb tls : cs
    }
  where
    crumb ls = RTZCrumb (rtzcLabel c) ls (t : rtzcRight c)

walkLeftZipper :: RankedTree t
  => (t -> t) -> RankedTreeZipper t -> RankedTreeZipper t
walkLeftZipper _ tz@(RTZipper _ [])  = tz
walkLeftZipper f (RTZipper t (c:cs)) = go t (rtzcLeft c) (rtzcRight c)
  where
    go tl []        trs = RTZipper (f tl) $ crumb trs : cs
    go tl (tl':tls) trs = go (f tl') tls (tl:trs)

    crumb = RTZCrumb (rtzcLabel c) []

zoomRightRtZipper :: RankedTree t => RankedTreeZipper t -> Maybe (RankedTreeZipper t)
zoomRightRtZipper (RTZipper _ [])     = Nothing
zoomRightRtZipper (RTZipper t (c:cs)) = case rtzcRight c of
  []       -> Nothing
  (tr:trs) -> Just RTZipper
    { rtzTree   = tr
    , rtzCrumbs = crumb trs : cs
    }
  where
    crumb = RTZCrumb (rtzcLabel c) (t : rtzcLeft c)

walkRightZipper :: RankedTree t
  => (t -> t) -> RankedTreeZipper t -> RankedTreeZipper t
walkRightZipper _ tz@(RTZipper _ [])  = tz
walkRightZipper f (RTZipper t (c:cs)) = go t (rtzcLeft c) (rtzcRight c)
  where
    go tl tls []        = RTZipper (f tl) $ crumb tls : cs
    go tl tls (tl':trs) = go (f tl') (tl:tls) trs

    crumb tls = RTZCrumb (rtzcLabel c) tls []

modifyTreeZipper :: RankedTree t
  => (t -> t) -> RankedTreeZipper t -> RankedTreeZipper t
modifyTreeZipper f tz = RTZipper
  { rtzTree   = f $ rtzTree tz
  , rtzCrumbs = rtzCrumbs tz
  }

setTreeZipper :: RankedTree t
  => t -> RankedTreeZipper t -> RankedTreeZipper t
setTreeZipper t tz = RTZipper
  { rtzTree   = t
  , rtzCrumbs = rtzCrumbs tz
  }
