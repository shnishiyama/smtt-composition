module Data.Tree.Trans.Class
  ( TreeTransducer (..)
  , RankedTree (..)
  ) where

import           SmttPrelude

import           Data.Tree.RankedTree

class (RankedTree ta, RankedTree tb) => TreeTransducer t ta tb | t -> ta, t -> tb where
  treeTrans :: MonadThrow m => t -> ta -> m tb
