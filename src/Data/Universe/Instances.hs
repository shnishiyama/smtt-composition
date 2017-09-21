{-# OPTIONS_GHC -Wno-orphans #-}

module Data.Universe.Instances where

import           ClassyPrelude

import           Data.Universe.Class
import           Data.Void

instance Universe Void where
  universe = []

instance Finite Void


instance (Universe a, Universe b) => Universe (a, b) where
  universe = [ (x, y) | x <- universe, y <- universe ]

instance (Finite a, Finite b) => Finite (a, b)


instance Universe Int
instance Finite Int
