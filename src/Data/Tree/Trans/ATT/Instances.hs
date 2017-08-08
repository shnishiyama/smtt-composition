{-# LANGUAGE OverloadedLists   #-}

module Data.Tree.Trans.ATT.Instances where

import ClassyPrelude
import Data.Universe.Class
import Data.Universe.Instances
import Data.Tree.RankedTree
import Data.Tree.Trans.ATT
import qualified Data.Vector as V
import Data.Pattern.Error


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


identityTransducer :: forall t. (RankedTree t) => AttrTreeTrans SynAttrUnit EmptyType t t
identityTransducer = AttrTreeTrans
    { initialAttr   = a0
    , reductionRule = rule
    }
  where
    a0 = SynAttrUnit

    rule A0 InitialLabel        = synAttrSide a0 0
    rule A0 (RankedTreeLabel l) = LabelSide l $
      V.generate (treeLabelRank (treeTag :: TreeTag t) l) (synAttrSide a0)

    rule _ _ = error "unsupported operation"

orderExchangeTransducer :: forall t. (RankedTree t) => AttrTreeTrans SynAttrUnit EmptyType t t
orderExchangeTransducer = AttrTreeTrans
    { initialAttr   = a0
    , reductionRule = rule
    }
  where
    a0 = SynAttrUnit

    rule A0 InitialLabel        = synAttrSide a0 0
    rule A0 (RankedTreeLabel l) =
      let k = treeLabelRank (treeTag :: TreeTag t) l
      in LabelSide l $ V.generate k $ synAttrSide a0 . (k - 1 -)

    rule _ _ = error "unsupported operation"

infixToPostfixTransducer :: AttrTreeTrans SynAttrUnit InhAttrUnit InfixOpTree PostfixOpTree
infixToPostfixTransducer = AttrTreeTrans
    { initialAttr   = a0
    , reductionRule = rule
    }
  where
    a0 = SynAttrUnit
    a1 = InhAttrUnit

    one   a = LabelSide "one"   [a]
    two   a = LabelSide "two"   [a]
    plus  a = LabelSide "plus"  [a]
    multi a = LabelSide "multi" [a]
    end     = LabelSide "$"     []

    rule A0 InitialLabel              = synAttrSide a0 0
    rule A0 (RankedTreeLabel "one")   = one $ inhAttrSide a1
    rule A0 (RankedTreeLabel "two")   = two $ inhAttrSide a1
    rule A0 (RankedTreeLabel "plus")  = synAttrSide a0 0
    rule A0 (RankedTreeLabel "multi") = synAttrSide a0 0
    rule A0 l                         = error $ "unsupported label: " <> show l

    rule (A1 0) InitialLabel              = end
    rule (A1 0) (RankedTreeLabel "plus")  = synAttrSide a0 1
    rule (A1 1) (RankedTreeLabel "plus")  = plus $ inhAttrSide a1
    rule (A1 0) (RankedTreeLabel "multi") = synAttrSide a0 1
    rule (A1 1) (RankedTreeLabel "multi") = multi $ inhAttrSide a1
    rule (A1 i) l                         = error $ "unsupported label: (" <> show i <> "," <> show l <> ")"

    rule _ _ = unreachable
