module Data.Tree.Trans.Demo
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

import           ClassyPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Instances
import           Data.Tree.Trans.ATT
import           Data.Tree.Trans.ATT.Compose
import           Data.Tree.Trans.ATT.Instances
import           Data.Tree.Trans.Class
import           Data.Tree.Trans.SATT
import           Data.Tree.Trans.SATT.Compose
import           Data.Tree.Trans.SATT.Instances

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
