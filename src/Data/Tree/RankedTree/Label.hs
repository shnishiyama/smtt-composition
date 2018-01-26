{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DerivingStrategies  #-}

module Data.Tree.RankedTree.Label
  (
    -- common
    RankedTree (..)
  , RankedLabel (..)
  , RankedLabelledTree
  , mkLabelledTree

    -- wrapper
  , RankedTreeLabel (..)
  , ConstRankedLabel (..)

    -- ranked alphabet
  , RankedAlphabet
  , pattern RankedAlphabet
  , rankedAlphabet

    -- safe apis
  , TaggedAlphabet ()
  , pattern TaggedAlphabet
  , taggedAlphabetUniverse
  , taggedAlphabet
  , taggedLabel
  , untaggedAlphabet
  , TaggedRankedAlphabet ()
  , pattern TaggedRankedAlphabet
  , taggedRankedAlphabetUniverse
  , taggedRankedAlphabet
  , taggedRankedLabel
  , untaggedRankedAlphabet
  ) where

import           SattPrelude

import qualified Data.Promotion.Prelude      as Typ
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
  }
  deriving (Eq, Ord, Enum, Bounded, Generic)
  deriving newtype Hashable

instance Show l => Show (RankedTreeLabel t l) where
  show (RankedTreeLabelWrapper l) = show l

instance RtConstraint t l => RankedLabel (RankedTreeLabel t l) where
  labelRank (RankedTreeLabelWrapper l) = treeLabelRank (Proxy @t) l


newtype ConstRankedLabel (n :: Nat) a = ConstRankedLabelWrapper
  { unwrapConstRankedLabel :: a
  }
  deriving (Eq, Ord, Enum, Bounded, Generic)
  deriving newtype Hashable

instance Show a => Show (ConstRankedLabel n a) where
  show (ConstRankedLabelWrapper l) = show l

instance KnownNat n => RankedLabel (ConstRankedLabel n a) where
  labelRank _ = fromInteger $ natVal (Proxy @n)


-- ranked alphabet

data RankedAlphabet a = RankedAlphabetWrapper
  { alphabetLabel :: a
  , alphabetRank  :: RankNumber
  } deriving (Generic, Hashable)

pattern RankedAlphabet :: a -> RankedAlphabet a
pattern RankedAlphabet x <- RankedAlphabetWrapper x _
{-# COMPLETE RankedAlphabet #-}

rankedAlphabet :: (a -> RankNumber) -> a -> RankedAlphabet a
rankedAlphabet f l = RankedAlphabetWrapper l (f l)

instance Eq a => Eq (RankedAlphabet a) where
  RankedAlphabet x == RankedAlphabet y = x == y

instance Ord a => Ord (RankedAlphabet a) where
  RankedAlphabet x `compare` RankedAlphabet y = x `compare` y

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
  }
  deriving (Eq, Ord, Generic)
  deriving newtype Hashable

class KnownTypTag (tag :: k) where
  type TypTagValue tag :: *

  typTagVal :: Proxy tag -> TypTagValue tag

instance KnownNat tag => KnownTypTag tag where
  type TypTagValue tag = Integer

  typTagVal = natVal

instance KnownSymbol tag => KnownTypTag tag where
  type TypTagValue tag = String

  typTagVal = symbolVal

instance KnownTypTag '[] where
  type TypTagValue '[] = ()

  typTagVal _ = ()

instance (KnownTypTag x, KnownTypTag xs) => KnownTypTag (x ': xs) where
  type TypTagValue (x ': xs) = (TypTagValue x, TypTagValue xs)

  typTagVal _ = (typTagVal $ Proxy @x, typTagVal $ Proxy @xs)

instance KnownTypTag '() where
  type TypTagValue '() = ()

  typTagVal _ = ()

instance (KnownTypTag x, KnownTypTag y) => KnownTypTag '(x, y) where
  type TypTagValue '(x, y) = (TypTagValue x, TypTagValue y)

  typTagVal _ = (typTagVal $ Proxy @x, typTagVal $ Proxy @y)

class FlattenTupleList a b where
  fromTupleToFlattenList :: a -> [b]

instance FlattenTupleList () a where
  fromTupleToFlattenList () = []

instance FlattenTupleList as a => FlattenTupleList (a, as) a where
  fromTupleToFlattenList (x, xs) = x:fromTupleToFlattenList xs

type UntaggedTypList tag t = (KnownTypTag tag, FlattenTupleList (TypTagValue tag) t)

untaggedTypList :: UntaggedTypList tag t => Proxy tag -> [t]
untaggedTypList = fromTupleToFlattenList . typTagVal

taggedAlphabetUniverse :: forall tag. UntaggedTypList tag String
  => Proxy (TaggedAlphabet tag) -> [TaggedAlphabet tag]
taggedAlphabetUniverse _ = coerce (untaggedTypList @tag Proxy :: [String])

coerceTailTaggedAlphabet :: TaggedAlphabet as -> TaggedAlphabet (a ': as)
coerceTailTaggedAlphabet x = TaggedAlphabetWrapper $ untaggedAlphabet x

instance (KnownSymbol a) => Enum (TaggedAlphabet (a ': '[])) where
  toEnum 0 = taggedAlphabet @a Proxy
  toEnum _ = error "bad argument"

  fromEnum _ = 0

instance (KnownSymbol a0, Enum (TaggedAlphabet (a1 ': as))) => Enum (TaggedAlphabet (a0 ': a1 ': as)) where
  toEnum 0 = taggedAlphabet @a0 Proxy
  toEnum i = coerceTailTaggedAlphabet $ toEnum $ i - 1

  fromEnum (TaggedAlphabet (Proxy :: Proxy a0)) = 0
  fromEnum a = fromEnum (TaggedAlphabetWrapper $ untaggedAlphabet a :: TaggedAlphabet (a1 ': as)) + 1

instance (KnownSymbol x) => Bounded (TaggedAlphabet (x ': '[])) where
  minBound = TaggedAlphabetWrapper $ symbolVal @x Proxy
  maxBound = minBound

instance (KnownSymbol x0, Bounded (TaggedAlphabet (x1 ': xs))) => Bounded (TaggedAlphabet (x0 ': (x1 ': xs))) where
  minBound = TaggedAlphabetWrapper $ symbolVal (Proxy @x0)
  maxBound = coerceTailTaggedAlphabet (maxBound :: TaggedAlphabet (x1 ': xs))

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

type FromTaggedRankedAlphabet tag = Typ.Nub (MapFst tag)

newtype TaggedRankedAlphabet (tag :: [(Symbol, Nat)]) = TaggedRankedAlphabetWrapper
  { _untaggedRankedAlphabet :: RankedAlphabet (TaggedAlphabet (FromTaggedRankedAlphabet tag))
  }
  deriving (Eq, Ord, Generic)
  deriving newtype Hashable

taggedRankedAlphabetUniverse :: forall tag.
  ( UntaggedTypList (FromTaggedRankedAlphabet tag) String
  , UntaggedTypList tag (String, Integer)
  )
  => Proxy (TaggedRankedAlphabet tag) -> [TaggedRankedAlphabet tag]
taggedRankedAlphabetUniverse _ = coerce
    [ RankedAlphabetWrapper x $ fromMaybe errorUnreachable $ lookup (coerce x) rm
    | x <- taggedAlphabetUniverse $ Proxy @(TaggedAlphabet (FromTaggedRankedAlphabet tag))
    ]
  where
    rm :: HashMap String RankNumber
    rm = mapFromList $ second fromInteger <$> untaggedTypList (Proxy @tag)

instance Show (TaggedRankedAlphabet tag) where
  show (TaggedRankedAlphabetWrapper x) = show x

instance RankedLabel (TaggedRankedAlphabet tag) where
  labelRank = coerce $ labelRank @(RankedAlphabet (TaggedAlphabet (FromTaggedRankedAlphabet tag)))

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


-- tree form

instance RankedLabel RankNumber where
  labelRank = id
