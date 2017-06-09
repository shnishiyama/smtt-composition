module Data.Tree.RankedTree.Zipper where

import ClassyPrelude

import Data.Tree.RankedTree

data RTZCrumb t l = RTZCrumb
  { rtzcLabel :: l
  , rtzcLeft  :: [t]
  , rtzcRight :: [t]
  } deriving (Show, Eq)

fromTreeCrumb :: RankedTree t => RTZCrumb t (LabelType t) -> t -> t
fromTreeCrumb RTZCrumb{..} t = mkTree rtzcLabel rtzcChilds
  where
    rtzcChilds = go rtzcLeft (t:rtzcRight)

    go = foldl' $ flip (:)

data RTZipper t l = RTZipper
  { rtzTree   :: t
  , rtzCrumbs :: [RTZCrumb t l]
  } deriving (Show, Eq)

type RankedTreeCrumb t = RTZCrumb t (LabelType t)
type RankedTreeZipper t = RTZipper t (LabelType t)

pattern IsTopTree :: t -> RankedTreeZipper t
pattern IsTopTree t = RTZipper t []

pattern IsDownTree :: t -> RankedTreeCrumb t -> [RankedTreeCrumb t] -> RankedTreeZipper t
pattern IsDownTree t c cs = RTZipper t (c:cs)

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
