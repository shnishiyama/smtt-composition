{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.ATT.Instances where

import           ClassyPrelude

import Data.Pattern.Error
import           Data.Universe.Class
import           Data.Universe.Instances
import qualified Data.Vector                    as V

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Instances
import           Data.Tree.Trans.ATT


data SynAttrUnit = SynAttrUnit
  deriving (Eq, Ord, Enum, Bounded)

pattern A0 :: InputAttr SynAttrUnit inh
pattern A0 = SynAttr SynAttrUnit

instance Universe SynAttrUnit
instance Finite SynAttrUnit

instance Show SynAttrUnit where
  show _ = "a0"


data InhAttrUnit = InhAttrUnit
  deriving (Eq, Ord, Enum, Bounded)

pattern A1 :: RankNumber -> InputAttr syn InhAttrUnit
pattern A1 i = InhAttr InhAttrUnit i

instance Universe InhAttrUnit
instance Finite InhAttrUnit

instance Show InhAttrUnit where
  show _ = "a1"


{-# COMPLETE A0, A1 #-}

-- | the identity attributed tree transducer
--
-- Examples:
--
-- >>> import Data.Tree.Trans.Class
-- >>> treeTrans identityTransducer $ InfixMulti InfixTwo (InfixPlus InfixOne InfixTwo)
-- "multi"("two","plus"("one","two"))
--
identityTransducer :: forall t. (RankedTree t) => AttrTreeTrans SynAttrUnit EmptyType t t
identityTransducer = AttrTreeTrans
    { initialAttr   = minBound
    , reductionRule = rule
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
-- "multi"("plus"("two","one"),"two")
--
orderExchangeTransducer :: forall t. (RankedTree t) => AttrTreeTrans SynAttrUnit EmptyType t t
orderExchangeTransducer = AttrTreeTrans
    { initialAttr   = minBound
    , reductionRule = rule
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
-- "two"("one"("two"("plus"("multi"("$")))))
--
infixToPostfixTransducer :: AttrTreeTrans SynAttrUnit InhAttrUnit InfixOpTree PostfixOpTree
infixToPostfixTransducer = AttrTreeTrans
    { initialAttr   = minBound
    , reductionRule = rule
    }
  where
    a0 = synAttrSide SynAttrUnit
    a1 = inhAttrSide InhAttrUnit

    one   a = LabelSide "one"   [a]
    two   a = LabelSide "two"   [a]
    plus  a = LabelSide "plus"  [a]
    multi a = LabelSide "multi" [a]
    end     = LabelSide "$"     []

    rule A0     InitialLabel              = a0 0
    rule (A1 0) InitialLabel              = end

    rule A0     (RankedTreeLabel "one")   = one a1
    rule A0     (RankedTreeLabel "two")   = two a1

    rule A0     (RankedTreeLabel "plus")  = a0 0
    rule (A1 0) (RankedTreeLabel "plus")  = a0 1
    rule (A1 1) (RankedTreeLabel "plus")  = plus a1

    rule A0     (RankedTreeLabel "multi") = a0 0
    rule (A1 0) (RankedTreeLabel "multi") = a0 1
    rule (A1 1) (RankedTreeLabel "multi") = multi a1

    rule A0     l = error $ "unsupported label: " <> show l
    rule (A1 i) l = error $ "unsupported label: (" <> show i <> "," <> show l <> ")"
