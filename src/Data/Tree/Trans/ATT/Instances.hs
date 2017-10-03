{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.ATT.Instances where

import           ClassyPrelude

import           Data.Pattern.Error
import           Data.Universe.Class
import           Data.Universe.Instances        ()
import qualified Data.Vector                    as V
import           Data.Void

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Instances
import           Data.Tree.Trans.ATT


data SynAttrUnit = SynAttrUnit
  deriving (Eq, Ord, Enum, Bounded, Generic)

pattern A0 :: InputAttr SynAttrUnit inh
pattern A0 = SynAttr SynAttrUnit

instance Hashable SynAttrUnit
instance Universe SynAttrUnit
instance Finite SynAttrUnit

instance Show SynAttrUnit where
  show _ = "a0"


data InhAttrUnit = InhAttrUnit
  deriving (Eq, Ord, Enum, Bounded, Generic)

pattern A1 :: RankNumber -> InputAttr syn InhAttrUnit
pattern A1 i = InhAttr InhAttrUnit i

instance Hashable InhAttrUnit
instance Universe InhAttrUnit
instance Finite InhAttrUnit

instance Show InhAttrUnit where
  show _ = "a1"


{-# COMPLETE A0, A1 #-}

-- | The identity attributed tree transducer
--
-- Examples:
--
-- >>> import Data.Tree.Trans.Class
-- >>> treeTrans identityTransducer $ InfixMulti InfixTwo (InfixPlus InfixOne InfixTwo)
-- multi(two, plus(one, two))
--
identityTransducer :: forall t. (FiniteInputRankedTree t) => FiniteAttrTreeTrans SynAttrUnit Void t t
identityTransducer = FinAttrTreeTrans
    { finInitialAttr   = minBound
    , finReductionRule = fromFunctionBase rule
    }
  where
    a0 = SynAttrUnit

    rule A0 InitialLabel        = synAttrSide a0 0
    rule A0 (RankedTreeLabel l) = LabelSide l $
      V.generate (treeLabelRank (treeTag @t) l) (synAttrSide a0)

    rule _ _ = unreachable


-- | the exchange transducer for ranked tree order
--
-- Examples:
--
-- >>> import Data.Tree.Trans.Class
-- >>> treeTrans orderExchangeTransducer $ InfixMulti InfixTwo (InfixPlus InfixOne InfixTwo)
-- multi(plus(two, one), two)
--
orderExchangeTransducer :: forall t. (FiniteInputRankedTree t) => FiniteAttrTreeTrans SynAttrUnit Void t t
orderExchangeTransducer = FinAttrTreeTrans
    { finInitialAttr   = minBound
    , finReductionRule = fromFunctionBase rule
    }
  where
    a0 = synAttrSide SynAttrUnit

    rule A0 InitialLabel        = a0 0
    rule A0 (RankedTreeLabel l) =
      let k = treeLabelRank (treeTag @t) l
      in LabelSide l $ V.generate k $ a0 . (k - 1 -)

    rule _ _ = unreachable


-- | a transducer from infix operators to postfix operators
--
-- Examples:
--
-- >>> import Data.Tree.Trans.Class
-- >>> treeTrans infixToPostfixTransducer $ InfixMulti InfixTwo (InfixPlus InfixOne InfixTwo)
-- two(one(two(plus(multi($)))))
--
infixToPostfixTransducer :: FiniteAttrTreeTrans SynAttrUnit InhAttrUnit InfixOpTree PostfixOpTree
infixToPostfixTransducer = FinAttrTreeTrans
    { finInitialAttr   = minBound
    , finReductionRule = fromFunctionBase rule
    }
  where
    a0 = synAttrSide SynAttrUnit
    a1 = inhAttrSide InhAttrUnit

    one   a = LabelSide PostfixOneLabel   [a]
    two   a = LabelSide PostfixTwoLabel   [a]
    plus  a = LabelSide PostfixPlusLabel  [a]
    multi a = LabelSide PostfixMultiLabel [a]
    end     = LabelSide PostfixEndLabel   []

    rule A0     InitialLabel                      = a0 0
    rule (A1 0) InitialLabel                      = end

    rule A0     (RankedTreeLabel InfixOneLabel)   = one a1
    rule A0     (RankedTreeLabel InfixTwoLabel)   = two a1

    rule A0     (RankedTreeLabel InfixPlusLabel)  = a0 0
    rule (A1 0) (RankedTreeLabel InfixPlusLabel)  = a0 1
    rule (A1 1) (RankedTreeLabel InfixPlusLabel)  = plus a1

    rule A0     (RankedTreeLabel InfixMultiLabel) = a0 0
    rule (A1 0) (RankedTreeLabel InfixMultiLabel) = a0 1
    rule (A1 1) (RankedTreeLabel InfixMultiLabel) = multi a1

    rule _ _                                      = unreachable
