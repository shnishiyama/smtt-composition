module Data.SATT.Demo
  ( RankedTree
  , TreeTransducer(..)
  , AttrTreeTrans
  , StackAttrTreeTrans
  , buildAttReductionSteps
  , buildSattReductionSteps

    -- att to satt
  , fromAttrTreeTrans

    -- samples
  , InfixOpTree(..)
  , PostfixOpTree(..)
  , infixToPostfixTransducer
  , postfixToInfixTransducer
  , infixOpTreeSample
  , postfixOpTreeSample
  ) where

import ClassyPrelude

import Data.Tree.RankedTree
import Data.Tree.RankedTree.Transducer
import Data.SATT.ATT
import Data.SATT.SATT

infixOpTreeSample :: InfixOpTree
infixOpTreeSample = InfixMulti InfixTwo (InfixPlus InfixOne InfixTwo)

postfixOpTreeSample :: PostfixOpTree
postfixOpTreeSample = PostfixTwo . PostfixOne . PostfixTwo . PostfixPlus . PostfixMulti $ PostfixEnd
