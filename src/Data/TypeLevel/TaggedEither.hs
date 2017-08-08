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

instance Bifunctor (TaggedEither tag) where
  bimap f _ (TaggedLeft  x) = TaggedLeft $ f x
  bimap _ g (TaggedRight x) = TaggedRight $ g x


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

instance Bifunctor TaggedEitherBox where
  bimap f g (TaggedEitherBox x) = TaggedEitherBox $ bimap f g x

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

taggedEither :: (a -> r) -> (b -> r) -> TaggedEitherBox a b -> r
taggedEither fl _ (TaggedLeftBox  x) = fl x
taggedEither _ fr (TaggedRightBox x) = fr x
taggedEither _ _  _                  = unreachable

taggedEitherMap :: (a -> b) -> (c -> d) -> TaggedEitherBox a c -> TaggedEitherBox b d
taggedEitherMap fl _ (TaggedLeftBox  x) = taggedLeftBox  $ fl x
taggedEitherMap _ fr (TaggedRightBox x) = taggedRightBox $ fr x
taggedEitherMap _ _  _                  = unreachable
