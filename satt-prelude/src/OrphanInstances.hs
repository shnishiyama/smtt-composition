{-# OPTIONS_GHC -Wno-orphans #-}

module OrphanInstances where

import           ClassyPrelude

import qualified Data.Foldable         as Foldable
import           Data.Functor.Foldable
import           Data.Hashable.Lifted
import           Data.Vector           (Vector (..))
import           GHC.Generics          (Generic1)


deriving instance Generic (Fix f)

instance Hashable1 f => Hashable (Fix f) where
  hashWithSalt i (Fix x) = hashWithSalt1 i x

instance Hashable1 Vector where
  liftHashWithSalt = liftFoldableHashWithSalt

data SPInt = SP !Int !Int

liftFoldableHashWithSalt :: Foldable t => (Int -> a -> Int) -> Int -> t a -> Int
liftFoldableHashWithSalt h salt arr = finalise (Foldable.foldl' step (SP salt 0) arr)
  where
    finalise (SP s l) = hashWithSalt s l
    step (SP s l) x   = SP (h s x) (l + 1)
