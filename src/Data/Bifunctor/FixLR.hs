module Data.Bifunctor.FixLR where

import           SattPrelude

import qualified Text.Show   as S

newtype FixL p1 p2 = FixL
  { unFixL :: p1 (FixL p1 p2) (FixR p1 p2)
  } deriving (Generic)

newtype FixR p1 p2 = FixR
  { unFixR :: p2 (FixL p1 p2) (FixR p1 p2)
  } deriving (Generic)

instance (Eq2 p1, Eq2 p2) => Eq (FixL p1 p2) where
  FixL a == FixL b = eq2 a b

instance (Eq2 p1, Eq2 p2) => Eq (FixR p1 p2) where
  FixR a == FixR b = eq2 a b

instance (Ord2 p1, Ord2 p2) => Ord (FixL p1 p2) where
  FixL a `compare` FixL b = a `compare2` b

instance (Ord2 p1, Ord2 p2) => Ord (FixR p1 p2) where
  FixR a `compare` FixR b = a `compare2` b

instance (Show2 p1, Show2 p2) => Show (FixL p1 p2) where
  showsPrec d (FixL a) = S.showParen (d > appPrec)
      $ S.showString "FixL "
      . showsPrec2 (appPrec + 1) a
    where
      appPrec = 10

instance (Show2 p1, Show2 p2) => Show (FixR p1 p2) where
  showsPrec d (FixR a) = S.showParen (d > appPrec)
      $ S.showString "FixR "
      . showsPrec2 (appPrec + 1) a
    where
      appPrec = 10


infixr 6 :+|+:
data (p1 :+|+: p2) a b
  = BiInL (p1 a b)
  | BiInR (p2 a b)
  deriving (Eq, Ord, Show, Generic, Hashable)

instance (Eq2 p1, Eq2 p2) => Eq2 (p1 :+|+: p2) where
  liftEq2 f g (BiInL a) (BiInL b) = liftEq2 f g a b
  liftEq2 f g (BiInR a) (BiInR b) = liftEq2 f g a b
  liftEq2 _ _ _ _                 = False

instance (Ord2 p1, Ord2 p2) => Ord2 (p1 :+|+: p2) where
  liftCompare2 f g (BiInL a) (BiInL b) = liftCompare2 f g a b
  liftCompare2 f g (BiInR a) (BiInR b) = liftCompare2 f g a b
  liftCompare2 _ _ (BiInL _) _         = LT
  liftCompare2 _ _ _         (BiInL _) = GT

instance (Show2 p1, Show2 p2) => Show2 (p1 :+|+: p2) where
  liftShowsPrec2 f1 f2 g1 g2 d x = S.showParen (d > appPrec) $ case x of
      BiInL x' -> S.showString "BiInL " . liftShowsPrec2 f1 f2 g1 g2 (appPrec + 1) x'
      BiInR x' -> S.showString "BiInR " . liftShowsPrec2 f1 f2 g1 g2 (appPrec + 1) x'
    where
      appPrec = 10

instance (Bifunctor p1, Bifunctor p2) => Bifunctor (p1 :+|+: p2) where
  bimap f g (BiInL m) = BiInL $ bimap f g m
  bimap f g (BiInR m) = BiInR $ bimap f g m

instance (Bifoldable p1, Bifoldable p2) => Bifoldable (p1 :+|+: p2) where
  bifoldr f g x (BiInL m) = bifoldr f g x m
  bifoldr f g x (BiInR m) = bifoldr f g x m

  bifoldMap f g (BiInL m) = bifoldMap f g m
  bifoldMap f g (BiInR m) = bifoldMap f g m


class Subsume sub sup where
  inj :: sub a b -> sup a b
  proj :: sup a b -> Maybe (sub a b)

infixl 5 :<<:
type (:<<:) = Subsume


instance Subsume p p where
  inj = id
  proj = Just

instance Subsume p1 (p1 :+|+: p2) where
  inj = BiInL

  proj (BiInL x) = Just x
  proj _         = Nothing

instance (Subsume p1 p3) => Subsume p1 (p2 :+|+: p3) where
  inj = BiInR . inj

  proj (BiInR x) = proj x
  proj _         = Nothing


injectL :: (p :<<: p1) => p (FixL p1 p2) (FixR p1 p2) -> FixL p1 p2
injectL = FixL . inj

injectR :: (p :<<: p2) => p (FixL p1 p2) (FixR p1 p2) -> FixR p1 p2
injectR = FixR . inj

projectL :: (p :<<: p1) => FixL p1 p2 -> Maybe (p (FixL p1 p2) (FixR p1 p2))
projectL (FixL x) = proj x

projectR :: (p :<<: p2) => FixR p1 p2 -> Maybe (p (FixL p1 p2) (FixR p1 p2))
projectR (FixR x) = proj x


type BiFix p1 p2 = Either (FixL p1 p2) (FixR p1 p2)

pattern BiFixLeft :: FixL p1 p2 -> BiFix p1 p2
pattern BiFixLeft x = Left x

pattern BiFixRight :: FixR p1 p2 -> BiFix p1 p2
pattern BiFixRight x = Right x

{-# COMPLETE BiFixLeft, BiFixRight #-}

pattern BiFixL :: p1 (FixL p1 p2) (FixR p1 p2) -> BiFix p1 p2
pattern BiFixL x = BiFixLeft (FixL x)

pattern BiFixR :: p2 (FixL p1 p2) (FixR p1 p2) -> BiFix p1 p2
pattern BiFixR x = BiFixRight (FixR x)

{-# COMPLETE BiFixL, BiFixR #-}

type family BiFixLeft t where
  BiFixLeft (BiFix p1 p2) = FixL p1 p2

type family BiFixRight t where
  BiFixRight (BiFix p1 p2) = FixR p1 p2
