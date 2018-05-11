{-# LANGUAGE UndecidableInstances #-}

module SmttPrelude
  ( -- common
    module ClassyPrelude

    -- useful modules
  , module Control.Arrow
  , module Control.Exception.Safe
  , module Data.Bifoldable
  , module Data.Bitraversable
  , module Data.Either
  , module Data.Functor.Classes
  , module Data.Functor.Foldable
  , module Data.Hashable.Lifted
  , defaultLiftHashWithSalt2
  , module Data.Kind
  , module Lens.Micro
  , module Data.Void
  , absurd
  , module Data.Monoid

    -- useful components
  , Proxy(..)
  , Generic1
  , coerce
  , (#.)
  , (.#)
  , groom
  , ushow
  , groomPrint
  , uprint
  , bivoid
  , stimesEndo
  , throwErrorM
  , invert
  , errorVoid
  , errorUnreachable
  , Nat
  , Symbol
  , KnownNat
  , KnownSymbol
  , natVal
  , symbolVal

    -- derivings
  , deriveEq1
  , deriveEq2
  , deriveOrd1
  , deriveOrd2
  , deriveShow1
  , deriveShow2
  , deriveBifunctor
  , deriveBifoldable
  , deriveBitraversable
  ) where

import           ClassyPrelude

import           Control.Exception.Safe   (MonadThrow(..), throwM)
import           Control.Arrow            (Kleisli (..), returnA, (<<<), (>>>))
import           Data.Bifoldable
import           Data.Bitraversable
import           Data.Coerce
import           Data.Either              (isLeft, isRight)
import           Data.Functor.Classes
import           Data.Functor.Foldable    (Corecursive (..), Fix (..),
                                           Recursive (..))
import           Data.Hashable.Lifted
import           Data.Kind                (Type)
import           Data.Monoid              hiding ((<>))
import           Data.Profunctor.Unsafe
import           Data.Proxy
import           Data.Semigroup
import           Data.Singletons.TypeLits
import           Data.Void                hiding (absurd)
import           GHC.Generics             (Generic1)
import           Lens.Micro
import           Text.Groom
import           Text.Show.Unicode

import           Data.Bifunctor.TH
import           Data.Eq.Deriving
import           Data.Ord.Deriving
import           Text.Show.Deriving

import           GHC.Exception            (errorCallWithCallStackException)
import           GHC.Stack                (HasCallStack, callStack)

import           OrphanInstances          ()


throwErrorM :: (HasCallStack, MonadThrow m) => String -> m a
throwErrorM s = throwM $ errorCallWithCallStackException s callStack

bivoid :: Bifunctor f => f a b -> f () ()
bivoid = bimap (const ()) (const ())
{-# INLINE bivoid #-}

errorVoid :: a -> Void
errorVoid = error "error void"

errorUnreachable :: a
errorUnreachable = error "unreachable"

-- for GHC 8.2.x bug (https://ghc.haskell.org/trac/ghc/ticket/13990)
absurd :: Void -> a
absurd = error "absurd"

groomPrint :: Show a => a -> IO ()
groomPrint = putStrLn . pack . groom

-- | invert ordering
--
-- Properties:
-- prop> \(xs :: [Int]) -> sortBy (\a b -> invert $ a `compare` b) xs == reverse (sort xs)
--
invert :: Ordering -> Ordering
invert LT = GT
invert EQ = EQ
invert GT = LT

stimesEndo :: forall a b. Integral b => b -> (a -> a) -> (a -> a)
stimesEndo = coerce (stimesMonoid :: b -> Endo a -> Endo a)


data WithDictHashable a = WithDictHashable (Int -> a -> Int) a

instance Hashable (WithDictHashable a) where
  hashWithSalt i (WithDictHashable f x) = f i x


defaultLiftHashWithSalt2 :: (Hashable1 (p (WithDictHashable a)), Bifunctor p)
  => (Int -> a -> Int) -> (Int -> b -> Int) -> Int -> p a b -> Int
defaultLiftHashWithSalt2 f g i = hashWithSalt1 i
  . bimap (WithDictHashable f) (WithDictHashable g)
