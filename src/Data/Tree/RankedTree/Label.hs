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
  , RankedAlphabet
  , pattern RankedAlphabet
  , rankedAlphabet

    -- safe apis
  , TaggedAlphabet ()
  , pattern TaggedAlphabet
  , taggedAlphabet
  , taggedLabel
  , untaggedAlphabet
  , TaggedRankedAlphabet ()
  , pattern TaggedRankedAlphabet
  , taggedRankedAlphabet
  , taggedRankedLabel
  , untaggedRankedAlphabet
  ) where

import           SattPrelude

import qualified Data.Promotion.Prelude as Typ
import qualified Data.Promotion.Prelude.List as Typ
import           Data.Tree.RankedTree

-- | A class of ranked labels
--
-- Conditions:
-- prop:skip> x /= y || labelRank x == labelRank y
--
class RankedLabel l where
  labelRank :: l -> RankNumber


-- wrapper

newtype RankedTreeLabel t l = RankedTreeLabelWrapper
  { unwrapRankedTreeLabel :: l
  } deriving (Eq, Ord, Show, Generic)

instance RtConstraint t l => RankedLabel (RankedTreeLabel t l) where
  labelRank (RankedTreeLabelWrapper l) = treeLabelRank (Proxy @t) l


-- ranked alphabet

data RankedAlphabet a = RankedAlphabetWrapper
  { alphabetLabel :: a
  , alphabetRank  :: RankNumber
  } deriving (Generic)

pattern RankedAlphabet :: a -> RankedAlphabet a
pattern RankedAlphabet x <- RankedAlphabetWrapper x _
{-# COMPLETE RankedAlphabet #-}

rankedAlphabet :: (a -> RankNumber) -> a -> RankedAlphabet a
rankedAlphabet f l = RankedAlphabetWrapper l (f l)

instance Eq a => Eq (RankedAlphabet a) where
  RankedAlphabet x == RankedAlphabet y = x == y

instance Ord a => Ord (RankedAlphabet a) where
  RankedAlphabet x `compare` RankedAlphabet y = x `compare` y

instance Hashable a => Hashable (RankedAlphabet a)

instance Show a => Show (RankedAlphabet a) where
  show (RankedAlphabet x) = show x

instance RankedLabel (RankedAlphabet a) where
  labelRank = alphabetRank


-- safe APIs

type MemberTaggedAlphabet symbol tag =
  ( KnownSymbol symbol
  , Typ.Elem symbol tag ~ 'True
  )

newtype TaggedAlphabet (tag :: [Symbol]) = TaggedAlphabetWrapper
  { untaggedAlphabet :: String
  } deriving (Eq, Ord, Generic)

instance Hashable (TaggedAlphabet tag)

instance Show (TaggedAlphabet tag) where
  show = untaggedAlphabet

viewTaggedAlphabet :: forall symbol tag. MemberTaggedAlphabet symbol tag
  => TaggedAlphabet tag -> Maybe (Proxy symbol)
viewTaggedAlphabet (TaggedAlphabetWrapper s)
  | symbolVal (Proxy @symbol) == s = Just Proxy
  | otherwise                      = Nothing

pattern TaggedAlphabet
  :: MemberTaggedAlphabet symbol tag
  => Proxy symbol -> TaggedAlphabet tag
pattern TaggedAlphabet x <- (viewTaggedAlphabet -> Just x)

taggedAlphabet :: MemberTaggedAlphabet symbol tag
  => Proxy symbol -> TaggedAlphabet tag
taggedAlphabet = TaggedAlphabetWrapper . symbolVal

taggedLabel :: forall symbol tag. MemberTaggedAlphabet symbol tag
  => TaggedAlphabet tag
taggedLabel = taggedAlphabet @symbol @tag Proxy

type family MapFst (l :: [(a, b)]) :: [a] where
  MapFst '[]       = '[]
  MapFst (x ': xs) = Typ.Fst x ': MapFst xs

type MemberTaggedRankedAlphabet symbol rank tag =
  ( KnownSymbol symbol, KnownNat rank
  , Typ.Lookup symbol tag ~ 'Just rank
  )

newtype TaggedRankedAlphabet (tag :: [(Symbol, Nat)]) = TaggedRankedAlphabetWrapper
  { _untaggedRankedAlphabet :: RankedAlphabet (TaggedAlphabet (Typ.Nub (MapFst tag)))
  } deriving (Eq, Ord, Generic)

instance Show (TaggedRankedAlphabet tag) where
  show (TaggedRankedAlphabetWrapper x) = show x

instance Hashable (TaggedRankedAlphabet tag)

instance RankedLabel (TaggedRankedAlphabet tag) where
  labelRank = coerce (labelRank @(RankedAlphabet (TaggedAlphabet (Typ.Nub (MapFst tag)))))

viewTaggedRankedAlphabet :: forall symbol rank tag. MemberTaggedRankedAlphabet symbol rank tag
  => TaggedRankedAlphabet tag -> Maybe (Proxy '(symbol, rank))
viewTaggedRankedAlphabet (TaggedRankedAlphabetWrapper (RankedAlphabet s))
  | symbolVal (Proxy @symbol) == coerce s = Just Proxy
  | otherwise                             = Nothing

pattern TaggedRankedAlphabet :: forall symbol rank tag. MemberTaggedRankedAlphabet symbol rank tag
  => Proxy '(symbol, rank) -> TaggedRankedAlphabet tag
pattern TaggedRankedAlphabet x <- (viewTaggedRankedAlphabet @symbol @rank @tag -> Just x)

taggedRankedAlphabet :: forall symbol rank tag. MemberTaggedRankedAlphabet symbol rank tag
  => Proxy '(symbol, rank) -> TaggedRankedAlphabet tag
taggedRankedAlphabet _ = TaggedRankedAlphabetWrapper $ RankedAlphabetWrapper
  { alphabetLabel = TaggedAlphabetWrapper $ symbolVal (Proxy @symbol)
  , alphabetRank  = fromInteger $ natVal (Proxy @rank)
  }

untaggedRankedAlphabet :: TaggedRankedAlphabet tag -> String
untaggedRankedAlphabet = untaggedAlphabet #. alphabetLabel .# _untaggedRankedAlphabet

taggedRankedLabel :: forall symbol rank tag. MemberTaggedRankedAlphabet symbol rank tag
  => TaggedRankedAlphabet tag
taggedRankedLabel = taggedRankedAlphabet @symbol @rank @tag Proxy


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
