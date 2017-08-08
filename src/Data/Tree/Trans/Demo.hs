module Data.SATT.Demo
  (
    -- ranked tree
    RankedTree
  , toRankedTreeWithoutInitial
  , toRankedTreeWithInitial
  , TreeTransducer(..)

    -- att
  , AttrTreeTrans
  , buildAttReductionSteps'
  , initialAttReductionState

    -- composition of atts
  , composeAtts

    -- satt
  , StackAttrTreeTrans
  , buildSattReductionSteps

    -- composition of att and satt
  , composeSatts

    -- att to satt
  , fromAttrTreeTrans

    -- samples
  , InfixOpTree(..)
  , PostfixOpTree(..)
  , identityTransducer
  , orderExchangeTransducer
  , infixToPostfixTransducer
  , postfixToInfixTransducer
  , infixOpTreeSample
  , postfixOpTreeSample
  ) where

import ClassyPrelude

import Data.Tree.RankedTree
import Data.Tree.RankedTree.Transducer
import Data.SATT.ATT
import Data.SATT.ATT.Compose
import Data.SATT.SATT
import Data.SATT.SATT.Compose

-- | Demo Examples
--
-- Transducers:
--
-- >>> treeTrans (fromAttrTreeTrans infixToPostfixTransducer) infixOpTreeSample
-- "two"("one"("two"("plus"("multi"("$")))))
--
-- >>> treeTrans postfixToInfixTransducer postfixOpTreeSample
-- "multi"("two","plus"("one","two"))
--
-- Composing transducers:
--
-- >>> treeTrans (orderExchangeTransducer `composeSatts` fromAttrTreeTrans orderExchangeTransducer) infixOpTreeSample
-- "multi"("two","plus"("one","two"))
--
-- >>> treeTrans (infixToPostfixTransducer `composeSatts` fromAttrTreeTrans orderExchangeTransducer) infixOpTreeSample
-- "two"("one"("plus"("two"("multi"("$")))))
--
-- >>> treeTrans (orderExchangeTransducer `composeSatts` postfixToInfixTransducer) postfixOpTreeSample
-- "multi"("plus"("two","one"),"two")
--
-- skip: treeTrans (infixToPostfixTransducer `composeSatts` postfixToInfixTransducer) postfixOpTreeSample
-- "multi"("two","plus"("two","one"))
--

infixOpTreeSample :: InfixOpTree
infixOpTreeSample = InfixMulti InfixTwo (InfixPlus InfixOne InfixTwo)

postfixOpTreeSample :: PostfixOpTree
postfixOpTreeSample = PostfixTwo . PostfixOne . PostfixTwo . PostfixPlus . PostfixMulti $ PostfixEnd
