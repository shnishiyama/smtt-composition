{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}

module Data.TFFoldable where

import GHC.Base hiding (foldr)
import GHC.Num (Num(..))

import Control.CoercionExt

import Data.Monoid
import Data.Foldable hiding (toList, length)
import qualified Data.Foldable as F

class TFFoldable t where
  type TFFoldElem t :: *

  {-# MINIMAL tfFoldMap | tfFoldr #-}

  tfFoldMap :: Monoid m => (TFFoldElem t -> m) -> t -> m
  {-# INLINE tfFoldMap #-}
  tfFoldMap f = tfFoldr (mappend . f) mempty

  tfFoldr :: (TFFoldElem t -> b -> b) -> b -> t -> b
  tfFoldr f z t = appEndo (tfFoldMap (Endo #. f) t) z

  tfFoldr' :: (TFFoldElem t -> b -> b) -> b -> t -> b
  tfFoldr' f z0 xs = tfFoldl f' id xs z0
    where f' k x z = k $! f x z

  tfFoldl :: (b -> TFFoldElem t -> b) -> b -> t -> b
  tfFoldl f z t = appEndo (getDual (tfFoldMap (Dual . Endo . flip f) t)) z

  tfFoldl' :: (b -> TFFoldElem t -> b) -> b -> t -> b
  tfFoldl' f z0 xs = tfFoldr f' id xs z0
    where f' x k z = k $! f z x

  toList :: t -> [TFFoldElem t]
  {-# INLINE toList #-}
  toList t = build $ \c n -> tfFoldr c n t

  length :: t -> Int
  length = tfFoldl' (\c _ -> c + 1) 0

newtype TFFoldableWrapper t = TFFoldableWrapper
  { unwrapTFFoldable :: t
  }

instance Foldable t => TFFoldable (TFFoldableWrapper (t a)) where
  type TFFoldElem (TFFoldableWrapper (t a)) = a

  tfFoldMap f = foldMap f . coerceReduction
  tfFoldr f s = foldr f s . coerceReduction
  tfFoldl f s = foldl f s . coerceReduction
  tfFoldr' f s = foldr' f s . coerceReduction
  tfFoldl' f s = foldl' f s . coerceReduction
  toList = F.toList . coerceReduction
  length = F.length . coerceReduction
