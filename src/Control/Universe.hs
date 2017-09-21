module Control.Universe where

import ClassyPrelude

import           Data.Universe.Class
import qualified Data.HashMap.Strict as HM

fromTotalFunction  :: (Eq k, Hashable k, Finite k) => (k -> v) -> HM.HashMap k v
fromTotalFunction f = HM.fromList [ (x, f x) | x <- universeF ]
