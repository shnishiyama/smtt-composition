module Data.Tree.RankedTree.Label
  (
    -- common
    RankedTree (..)
  , RankedLabel (..)
  , RankedLabelledTree

    -- wrapper
  , RankedTreeLabel (..)

    -- ranked alphabet
  , RankedAlphabet (..)
  ) where

import           SattPrelude

import           Data.Tree.RankedTree

-- | Ranked Label Class
class RankedLabel l where
  labelRank :: l -> RankNumber


-- wrapper

newtype RankedTreeLabel t l = RankedTreeLabelWrapper
  { unwrapRankedTreeLabel :: l
  } deriving (Eq, Ord, Show, Generic)

instance RtConstraint t l => RankedLabel (RankedTreeLabel t l) where
  labelRank (RankedTreeLabelWrapper l) = treeLabelRank (TreeTag :: TreeTag t) l


-- ranked alphabet

data RankedAlphabet = RankedAlphabet
  { alphabetName :: String
  , alphabetRank :: RankNumber
  } deriving (Eq, Ord, Generic)

instance Show RankedAlphabet where
  show RankedAlphabet{..} = alphabetName <> "<" <> show alphabetRank <> ">"

instance RankedLabel RankedAlphabet where
  labelRank = alphabetRank


-- ranked labelled tree

data RankedLabelledTree a = RankedLabelledTree
  { _treeLabel  :: a
  , _treeChilds :: NodeVec (RankedLabelledTree a)
  } deriving (Generic)

instance (RankedLabel a, Eq a) => Eq (RankedLabelledTree a) where
  (==) = coerce ((==) @(WrappedRankedTree (RankedLabelledTree a) a))

instance (RankedLabel a, Ord a) => Ord (RankedLabelledTree a) where
  compare = coerce (compare @(WrappedRankedTree (RankedLabelledTree a) a))

instance (RankedLabel a, Show a) => Show (RankedLabelledTree a) where
  show = coerce (show @(WrappedRankedTree (RankedLabelledTree a) a))

instance RankedLabel a => RankedTree (RankedLabelledTree a) where
  type LabelType (RankedLabelledTree a) = a

  treeLabel = _treeLabel
  treeChilds = _treeChilds
  treeLabelRank _ = labelRank

  mkTreeUnchecked = RankedLabelledTree
