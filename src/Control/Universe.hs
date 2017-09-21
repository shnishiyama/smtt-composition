module Control.Universe where

import           ClassyPrelude

import qualified Data.HashMap.Strict as HM
import           Data.Universe.Class

fromTotalFunction  :: (Eq k, Hashable k, Finite k) => (k -> v) -> HM.HashMap k v
fromTotalFunction f = HM.fromList [ (x, f x) | x <- universeF ]
