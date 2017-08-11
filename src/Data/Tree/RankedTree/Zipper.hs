module Data.Tree.RankedTree.Zipper
  ( RankedTreeZipper(..)

    -- RTZipper
  , RTZipper -- for non type family supports
  , rtZipper

    -- operators
  , zoomTopRtZipper
  , toTopTree
  , getTreeLabel
  ) where

import ClassyPrelude hiding (length)
import qualified Data.Vector as V

import Data.Tree.RankedTree

-- RTZipper

data RTZCrumb t l = RTZCrumb
  { rtzcLabel  :: l
  , rtzcIndex  :: RankNumber
  , rtzcLength :: RankNumber
  , rtzcChilds :: NodeVec t
  } deriving (Show, Eq, Ord)

fromTreeCrumb :: RankedTree t => RtApply RTZCrumb t -> t -> t
fromTreeCrumb RTZCrumb{..} t = mkTreeUnchecked rtzcLabel rtzcChilds'
  where
    rtzcChilds' = rtzcChilds V.// [(rtzcIndex, t)]

-- | Common ranked tree zipper
--
-- Examples
--
-- >>> import Data.Tree.RankedTree.Instances
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
-- Just (TreeA TreeC (TreeB TreeC))
--
-- >>> toTopTree <$> setTreeZipper (TreeA TreeC TreeC) <$> zoomInRtZipper treeABCZipper
-- Just (TreeA (TreeA TreeC TreeC) (TreeB TreeC))
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
  toZipper :: RankedTree t => t -> RtApply tz t
  toTree :: RankedTree t => RtApply tz t -> t

  zoomInRtZipper :: RankedTree t => RtApply tz t -> Maybe (RtApply tz t)
  zoomInRtZipper = zoomInIdxRtZipper 0

  zoomOutRtZipper :: RankedTree t => RtApply tz t -> Maybe (RtApply tz t)

  zoomLeftRtZipper :: RankedTree t => RtApply tz t -> Maybe (RtApply tz t)

  zoomRightRtZipper :: RankedTree t => RtApply tz t -> Maybe (RtApply tz t)

  zoomInIdxRtZipper :: RankedTree t => RankNumber -> RtApply tz t -> Maybe (RtApply tz t)
  zoomInIdxRtZipper n
    | n < 0     = const Nothing
    | otherwise = go n zoomInRtZipper
    where
      go 0  f = f
      go n' f = go (n' - 1) (f >=> zoomLeftRtZipper)

  modifyTreeZipper :: RankedTree t => (t -> t) -> RtApply tz t -> RtApply tz t
  modifyTreeZipper f z = setTreeZipper (f $ toTree z) z

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
  toZipper = rtZipper
  toTree = rtzTree

  zoomInIdxRtZipper n (RTZipper t cs) = if n >= len
      then Nothing
      else Just RTZipper
        { rtzTree   = tcs ! n
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
      { rtzTree   = rtzcChilds ! nrtzcIndex
      , rtzCrumbs = c
        { rtzcIndex  = nrtzcIndex
        , rtzcChilds = nrtzcChilds
        } : cs
      }
      where
        nrtzcIndex = rtzcIndex - 1

        nrtzcChilds = rtzcChilds V.// [(rtzcIndex, t)]

  walkLeftZipper _ tz@(RTZipper _ [])  = tz
  walkLeftZipper f (RTZipper t (c@RTZCrumb{..}:cs)) = go t rtzcIndex []
    where
      go t' 0 itx = RTZipper t' $ c
        { rtzcIndex  = 0
        , rtzcChilds = rtzcChilds V.// itx
        } : cs
      go t' n itx = let n' = n - 1
        in go (f $ rtzcChilds ! n') n' $ (n, t'):itx

  zoomRightRtZipper (RTZipper _ []) = Nothing
  zoomRightRtZipper (RTZipper t (c@RTZCrumb{..}:cs))
    | rtzcIndex == rtzcLength - 1 = Nothing
    | otherwise                   = Just RTZipper
      { rtzTree   = rtzcChilds ! nrtzcIndex
      , rtzCrumbs = c
        { rtzcIndex  = nrtzcIndex
        , rtzcChilds = nrtzcChilds
        } : cs
      }
      where
        nrtzcIndex = rtzcIndex + 1

        nrtzcChilds = rtzcChilds V.// [(rtzcIndex, t)]

  walkRightZipper _ tz@(RTZipper _ [])  = tz
  walkRightZipper f (RTZipper t (c@RTZCrumb{..}:cs)) = go t rtzcIndex
    where
      rtzcLength' = rtzcLength - 1

      go t' n
        | n == rtzcLength' = RTZipper t' $
          c { rtzcIndex = rtzcLength' } : cs
        | otherwise        = let n' = n + 1
          in go (f $ rtzcChilds ! n') n'

  modifyTreeZipper f tz = tz
    { rtzTree   = f $ rtzTree tz
    }

  setTreeZipper t tz = tz
    { rtzTree   = t
    }

zoomTopRtZipper :: (RankedTree t, RankedTreeZipper tz) => RtApply tz t -> RtApply tz t
zoomTopRtZipper tz = maybe tz zoomTopRtZipper $ zoomOutRtZipper tz

toTopTree :: (RankedTree t, RankedTreeZipper tz) => RtApply tz t -> t
toTopTree = toTree . zoomTopRtZipper

getTreeLabel :: (RankedTree t, RankedTreeZipper tz) => RtApply tz t -> LabelType t
getTreeLabel = treeLabel . toTree
