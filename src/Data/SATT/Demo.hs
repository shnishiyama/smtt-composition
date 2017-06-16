module Data.SATT.Demo
  ( RankedTree
  , TreeTransducer(..)
  , AttrTreeTrans
  , InfixOpTree(..)
  , PostfixOpTree(..)
  , infixToPostfixTransducer
  , infixOpTreeSample
  ) where

import Data.Tree.RankedTree
import Data.Tree.RankedTree.Transducer
import Data.SATT.ATT

infixOpTreeSample :: InfixOpTree
infixOpTreeSample = InfixMulti InfixTwo (InfixPlus InfixOne InfixTwo)
