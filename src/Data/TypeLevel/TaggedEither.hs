{-# LANGUAGE FlexibleInstances #-}

module Data.TypeLevel.TaggedEither where

import           ClassyPrelude

import           GHC.Generics
import           Unsafe.Coerce
import           Data.Universe.Class

data EitherTag
  = LeftTag
  | RightTag
  deriving (Eq, Ord, Show, Enum, Bounded, Generic)

instance Hashable EitherTag

type LeftTaggedEither  = TaggedEither 'LeftTag
type RightTaggedEither = TaggedEither 'RightTag

data TaggedEither (tag :: EitherTag) a b where
  TaggedLeft  :: a -> LeftTaggedEither  a b
  TaggedRight :: b -> RightTaggedEither a b

deriving instance (Eq a, Eq b) => Eq (TaggedEither tag a b)
deriving instance (Ord a, Ord b) => Ord (TaggedEither tag a b)
deriving instance (Show a, Show b) => Show (TaggedEither tag a b)

instance Generic (TaggedEither tag a b) where
  type Rep (TaggedEither tag a b) = D1
    ('MetaData "TaggedEither" "Data.TypeLevel.TaggedEither" "satt-composition" 'False)
    (   C1 ('MetaCons "TaggedLeft" 'PrefixI 'False)
          (S1 ('MetaSel 'Nothing
            'NoSourceUnpackedness
            'NoSourceStrictness
            'DecidedStrict) (Rec0 a))
    :+: C1 ('MetaCons "TaggedRight" 'PrefixI 'False)
          (S1 ('MetaSel 'Nothing
            'NoSourceUnpackedness
            'NoSourceStrictness
            'DecidedStrict) (Rec0 b))
    )

  from (TaggedLeft  x) = M1 (L1 (M1 (M1 (K1 x))))
  from (TaggedRight x) = M1 (R1 (M1 (M1 (K1 x))))

  to (M1 (L1 (M1 (M1 (K1 x))))) = unsafeCoerce $ TaggedLeft  x
  to (M1 (R1 (M1 (M1 (K1 x))))) = unsafeCoerce $ TaggedRight x

instance (Hashable a, Hashable b) => Hashable (TaggedEither tag a b)

instance Universe a => Universe (TaggedEither 'LeftTag a b) where
  universe = [ TaggedLeft x | x <- universe ]

instance Universe b => Universe (TaggedEither 'RightTag a b) where
  universe = [ TaggedRight x | x <- universe ]

instance Finite a => Finite (TaggedEither 'LeftTag a b)
instance Finite b => Finite (TaggedEither 'RightTag a b)

instance Bifunctor (TaggedEither tag) where
  bimap f _ (TaggedLeft  x) = TaggedLeft $ f x
  bimap _ g (TaggedRight x) = TaggedRight $ g x


data TaggedEitherBox a b = forall tag. TaggedEitherBox (TaggedEither tag a b)

pattern TaggedLeftBox :: a -> TaggedEitherBox a b
pattern TaggedLeftBox  x = TaggedEitherBox (TaggedLeft  x)

pattern TaggedRightBox :: b -> TaggedEitherBox a b
pattern TaggedRightBox x = TaggedEitherBox (TaggedRight x)

{-# COMPLETE TaggedLeftBox, TaggedRightBox #-}

instance (Eq a, Eq b) => Eq (TaggedEitherBox a b) where
  TaggedLeftBox  x == TaggedLeftBox  y = x == y
  TaggedRightBox x == TaggedRightBox y = x == y
  _ == _ = False

instance (Ord a, Ord b) => Ord (TaggedEitherBox a b) where
  TaggedLeftBox  x `compare` TaggedLeftBox  y = x `compare` y
  TaggedRightBox x `compare` TaggedRightBox y = x `compare` y
  TaggedLeftBox  _ `compare` _ = LT
  _                `compare` _ = GT

instance (Show a, Show b) => Show (TaggedEitherBox a b) where
  show (TaggedLeftBox  x) = "TaggedLeftBox "  <> show x
  show (TaggedRightBox x) = "TaggedRightBox " <> show x

instance (Hashable a, Hashable b) => Hashable (TaggedEitherBox a b) where
  hashWithSalt s (TaggedEitherBox x) = s `hashWithSalt` x

instance (Universe a, Universe b) => Universe (TaggedEitherBox a b) where
  universe
    =  (TaggedEitherBox <$> (universe :: [LeftTaggedEither a b]))
    <> (TaggedEitherBox <$> (universe :: [RightTaggedEither a b]))

instance (Finite a, Finite b) => Finite (TaggedEitherBox a b)

instance Bifunctor TaggedEitherBox where
  bimap f g (TaggedEitherBox x) = TaggedEitherBox $ bimap f g x

taggedLeftBox :: a -> TaggedEitherBox a b
taggedLeftBox = TaggedEitherBox . TaggedLeft

taggedRightBox :: b -> TaggedEitherBox a b
taggedRightBox = TaggedEitherBox . TaggedRight

isTaggedLeft :: TaggedEitherBox a b -> Bool
isTaggedLeft (TaggedLeftBox _) = True
isTaggedLeft _                 = False

isTaggedRight :: TaggedEitherBox a b -> Bool
isTaggedRight (TaggedRightBox _) = True
isTaggedRight _                  = False

toEither :: TaggedEitherBox a b -> Either a b
toEither (TaggedLeftBox  x) = Left x
toEither (TaggedRightBox x) = Right x

fromEither :: Either a b -> TaggedEitherBox a b
fromEither (Left x)  = taggedLeftBox x
fromEither (Right x) = taggedRightBox x

taggedEither :: (a -> r) -> (b -> r) -> TaggedEitherBox a b -> r
taggedEither fl _ (TaggedLeftBox  x) = fl x
taggedEither _ fr (TaggedRightBox x) = fr x

taggedEitherMap :: (a -> b) -> (c -> d) -> TaggedEitherBox a c -> TaggedEitherBox b d
taggedEitherMap fl _ (TaggedLeftBox  x) = taggedLeftBox  $ fl x
taggedEitherMap _ fr (TaggedRightBox x) = taggedRightBox $ fr x
