module Data.TypeLevel.TaggedEither where

import ClassyPrelude

import Data.Pattern.Error

data EitherTag
  = LeftTag
  | RightTag
  deriving (Eq, Ord, Show, Enum, Bounded)

type LeftTaggedEither  = TaggedEither 'LeftTag
type RightTaggedEither = TaggedEither 'RightTag

data TaggedEither (tag :: EitherTag) a b where
  TaggedLeft  :: a -> LeftTaggedEither  a b
  TaggedRight :: b -> RightTaggedEither a b

deriving instance (Eq a, Eq b) => Eq (TaggedEither tag a b)
deriving instance (Ord a, Ord b) => Ord (TaggedEither tag a b)
deriving instance (Show a, Show b) => Show (TaggedEither tag a b)

data TaggedEitherBox a b = forall tag. TaggedEitherBox (TaggedEither tag a b)

pattern TaggedLeftBox :: a -> TaggedEitherBox a b
pattern TaggedLeftBox  x = TaggedEitherBox (TaggedLeft  x)

pattern TaggedRightBox :: b -> TaggedEitherBox a b
pattern TaggedRightBox x = TaggedEitherBox (TaggedRight x)

instance (Eq a, Eq b) => Eq (TaggedEitherBox a b) where
  x == y = toEither x == toEither y

instance (Ord a, Ord b) => Ord (TaggedEitherBox a b) where
  x `compare` y = toEither x `compare` toEither y

instance (Show a, Show b) => Show (TaggedEitherBox a b) where
  show (TaggedLeftBox  x) = "TaggedLeftBox "  <> show x
  show (TaggedRightBox x) = "TaggedRightBox " <> show x
  show _                    = unreachable

taggedLeftBox :: a -> TaggedEitherBox a b
taggedLeftBox = TaggedEitherBox . TaggedLeft

taggedRightBox :: b -> TaggedEitherBox a b
taggedRightBox = TaggedEitherBox . TaggedRight

toEither :: TaggedEitherBox a b -> Either a b
toEither (TaggedLeftBox  x) = Left x
toEither (TaggedRightBox x) = Right x
toEither _                    = unreachable

fromEither :: Either a b -> TaggedEitherBox a b
fromEither (Left x)  = taggedLeftBox x
fromEither (Right x) = taggedRightBox x
