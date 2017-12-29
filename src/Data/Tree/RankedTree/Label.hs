{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Tree.RankedTree.Label
  (
    -- common
    RankedTree (..)
  , RankedLabel (..)
  , RankedLabelledTree
  , mkLabelledTree

    -- wrapper
  , RankedTreeLabel (..)

    -- ranked alphabet
  , RankedAlphabet (..)
  , TaggedRankedAlphabet
  , taggedRankedAlphabet
  , taggedLabel
  , untaggedRankedAlphabet
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
  labelRank (RankedTreeLabelWrapper l) = treeLabelRank (Proxy @t) l


-- ranked alphabet

data RankedAlphabet = RankedAlphabet
  { alphabetName :: String
  , alphabetRank :: RankNumber
  } deriving (Eq, Ord, Generic)

instance Hashable RankedAlphabet

instance Show RankedAlphabet where
  show RankedAlphabet{..} = alphabetName

instance RankedLabel RankedAlphabet where
  labelRank = alphabetRank


-- safe APIs

newtype TaggedRankedAlphabet (tag :: [(Symbol, Nat)]) = TaggedRankedAlphabet
  { untaggedRankedAlphabet :: RankedAlphabet
  } deriving (Eq, Ord, Generic)

instance Hashable (TaggedRankedAlphabet tag)

instance Show (TaggedRankedAlphabet tag) where
  show = coerce (show @RankedAlphabet)

instance RankedLabel (TaggedRankedAlphabet tag) where
  labelRank = coerce (labelRank @RankedAlphabet)

taggedRankedAlphabet :: forall symbol rank tag.
  (KnownSymbol symbol, KnownNat rank, Elem '(symbol, rank) tag ~ 'True)
  => Proxy '(symbol, rank) -> TaggedRankedAlphabet tag
taggedRankedAlphabet _ = TaggedRankedAlphabet $ RankedAlphabet
  { alphabetName = symbolVal (Proxy @symbol)
  , alphabetRank = fromInteger $ natVal (Proxy @rank)
  }

taggedLabel :: forall symbol rank tag.
  ( KnownSymbol symbol, KnownNat rank
  , Lookup symbol tag ~ 'Just rank
  , Elem '(symbol, rank) tag ~ 'True
  )
  => TaggedRankedAlphabet tag
taggedLabel = taggedRankedAlphabet $ Proxy @'(symbol, rank)

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

mkLabelledTree :: RankedLabel a => a -> NodeVec (RankedLabelledTree a) -> RankedLabelledTree a
mkLabelledTree = mkTree

instance RankedLabel a => RankedTree (RankedLabelledTree a) where
  type LabelType (RankedLabelledTree a) = a

  treeLabel = _treeLabel
  treeChilds = _treeChilds
  treeLabelRank _ = labelRank

  mkTreeUnchecked = RankedLabelledTree
