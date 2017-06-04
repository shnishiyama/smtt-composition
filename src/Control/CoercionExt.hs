module Control.CoercionExt
  ( module Data.Coerce
  , (#.)
  , coerceReduction
  ) where

import Data.Coerce


infixr 9 #.

-- | Function coercion
(#.) :: Coercible b c => (b -> c) -> (a -> b) -> (a -> c)
(#.) _f = coerce

coerceReduction :: Coercible (c a) a => c a -> a
coerceReduction = coerce
