{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.SATT.Instances
  (
    -- from att to satt
    fromAttrTreeTrans

    -- attribute instances
  , SynAttrUnit(..)
  , pattern A0
  , InhAttrUnit(..)
  , pattern A1
  , StSynAttrUnit(..)
  , pattern S0
  , StInhAttrUnit(..)
  , pattern S1

    -- postfix to infix
  , postfixToInfixTransducer
  ) where

import           ClassyPrelude

import           Data.Pattern.Error
import           Data.Universe.Class
import           Data.Universe.Instances

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Instances
import qualified Data.Tree.Trans.ATT            as ATT
import           Data.Tree.Trans.ATT.Instances  (InhAttrUnit (..),
                                                 SynAttrUnit (..))
import           Data.Tree.Trans.SATT

-- instances

fromAttrTreeTrans :: forall syn inh ta tb.
  ATT.AttrTreeTrans syn inh ta tb -> StackAttrTreeTrans syn inh EmptyType EmptyType ta tb
fromAttrTreeTrans trans = StackAttrTreeTrans
  { initialAttr   = ATT.initialAttr trans
  , reductionRule = rule
  }
  where
    toOutputAttr (ATT.AttrSide a)     = AttrSide (taggedOut a)
    toOutputAttr (ATT.LabelSide l ts) = LabelSide l $ toOutputAttr <$> ts

    rule :: SattRuleType tag syn inh EmptyType EmptyType ta tb
    rule (TaggedOut a) = toOutputAttr . ATT.reductionRule trans a
    rule _             = error "not supported stack attributes"


pattern A0 :: () => tag ~ OutAttrTag => InputAttr tag SynAttrUnit inh stsyn stinh
pattern A0 = SynAttr SynAttrUnit

pattern A1 :: () => tag ~ OutAttrTag => RankNumber -> InputAttr tag syn InhAttrUnit stsyn stinh
pattern A1 i = InhAttr InhAttrUnit i

data StSynAttrUnit = StSynAttrUnit
  deriving (Eq, Ord, Enum, Bounded)

pattern S0 :: () => tag ~ StkAttrTag => InputAttr tag syn inh StSynAttrUnit stinh
pattern S0 = StSynAttr StSynAttrUnit

instance Universe StSynAttrUnit
instance Finite StSynAttrUnit

instance Show StSynAttrUnit where
  show _ = "s0"

data StInhAttrUnit = StInhAttrUnit
  deriving (Eq, Ord, Enum, Bounded)

pattern S1 :: () => tag ~ StkAttrTag => RankNumber -> InputAttr tag syn inh stsyn StInhAttrUnit
pattern S1 i = StInhAttr StInhAttrUnit i

instance Universe StInhAttrUnit
instance Finite StInhAttrUnit

instance Show StInhAttrUnit where
  show _ = "s1"


-- | a transducer from postfix operators to infix operators
--
-- Examples:
--
-- >>> import Data.Tree.Trans.Class
-- >>> treeTrans postfixToInfixTransducer $ PostfixTwo $ PostfixOne $ PostfixTwo $ PostfixPlus $ PostfixMulti $ PostfixEnd
-- "multi"("two","plus"("one","two"))
-- >>> lengthTree $ treeTrans postfixToInfixTransducer $ PostfixMulti $ PostfixPlus $ PostfixEnd
-- *** Exception: The input tree transducer is illegal.
-- CallStack (from HasCallStack):
-- ...
--
postfixToInfixTransducer :: StackAttrTreeTrans SynAttrUnit EmptyType EmptyType StInhAttrUnit PostfixOpTree InfixOpTree
postfixToInfixTransducer = StackAttrTreeTrans
  { initialAttr   = minBound
  , reductionRule = rule
  }
  where
    a0 = synAttrSide SynAttrUnit
    s1 = stinhAttrSide StInhAttrUnit

    one         = LabelSide "one"   []
    two         = LabelSide "two"   []
    plus  t1 t2 = LabelSide "plus"  [t1, t2]
    multi t1 t2 = LabelSide "multi" [t1, t2]

    rule :: SattRuleType tag SynAttrUnit EmptyType EmptyType StInhAttrUnit PostfixOpTree InfixOpTree

    rule A0     InitialLabel            = a0 0
    rule (S1 0) InitialLabel            = StackEmptySide

    rule A0     (RankedTreeLabel "one") = a0 0
    rule (S1 0) (RankedTreeLabel "one") = StackConsSide one s1

    rule A0     (RankedTreeLabel "two") = a0 0
    rule (S1 0) (RankedTreeLabel "two") = StackConsSide two s1

    rule A0     (RankedTreeLabel "plus") = a0 0
    rule (S1 0) (RankedTreeLabel "plus") = StackConsSide
      (plus
        (StackHeadSide (StackTailSide s1))
        (StackHeadSide s1))
      (StackTailSide
        (StackTailSide s1))

    rule A0     (RankedTreeLabel "multi") = a0 0
    rule (S1 0) (RankedTreeLabel "multi") = StackConsSide
      (multi
        (StackHeadSide (StackTailSide s1))
        (StackHeadSide s1))
      (StackTailSide
        (StackTailSide s1))

    rule A0 (RankedTreeLabel "$") = StackHeadSide s1

    rule A0     l = error $ "unsupported label: " <> show l
    rule (S1 i) l = error $ "unsupported label: (" <> show i <> "," <> show l <> ")"
    rule _ _ = unreachable
