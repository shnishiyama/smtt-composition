{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.ATT.Instances where

import           SattPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.ATT
import qualified Data.Vector                as V

identityTransducer :: forall t l.
  ( RtConstraint t l
  , Eq l, Hashable l
  )
  => HashSet l -> AttributedTreeTransducer () Void t l t l
identityTransducer ls = fromMaybe (error "unreachable") $ buildAtt
  ()
  [ (Synthesized (), SynAttrSide () 0)]
  [ (Synthesized (), l, AttLabelSide l $ V.generate (treeLabelRank (Proxy @t) l) (SynAttrSide ()))
  | l <- setToList ls
  ]

type InputSampleAlphabet = TaggedRankedAlphabet
  ['("A", 2), '("B", 1), '("C", 0)]

type OutputSampleAlphabet = TaggedRankedAlphabet
  ['("D", 2), '("E", 1), '("F", 0)]

type SynSampleAttr = TaggedAlphabet
  ["a0", "a1"]

type InhSampleAttr = TaggedAlphabet
  ["b0", "b1"]

type SampleAtt = AttTransducer
  SynSampleAttr
  InhSampleAttr
  (RankedLabelledTree InputSampleAlphabet)
  (RankedLabelledTree OutputSampleAlphabet)

-- | A sample attributed tree transducer
--
-- Sample:
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> treeTrans sampleAtt inputSampleTree
-- D(F,F)
--
sampleAtt :: SampleAtt
sampleAtt = fromMaybe (error "unreachable") $ buildAtt
    a0
    [ (Synthesized (), SynAttrSide a0 0)
    , (Inherited   b0, AttLabelSide f [])
    , (Inherited   b1, AttLabelSide f [])
    ]
    [ (Synthesized a0,    a, SynAttrSide a0 0)
    , (Inherited (b0, 0), a, SynAttrSide a1 1)
    , (Inherited (b0, 1), a, InhAttrSide b0)
    , (Synthesized a0,    b, AttLabelSide e [InhAttrSide b0])
    , (Inherited (b0, 0), b, InhAttrSide b0)
    , (Synthesized a0,    c, InhAttrSide b0)
    , (Synthesized a1,    a, InhAttrSide b1)
    , (Inherited (b1, 0), a, SynAttrSide a1 1)
    , (Inherited (b1, 1), a, InhAttrSide b1)
    , (Synthesized a1,    b, SynAttrSide a1 0)
    , (Inherited (b1, 0), b, AttLabelSide d [SynAttrSide a0 0, InhAttrSide b1])
    , (Synthesized a1,    c, InhAttrSide b1)
    ]
  where
    a0 = taggedLabel @"a0"
    a1 = taggedLabel @"a1"
    b0 = taggedLabel @"b0"
    b1 = taggedLabel @"b1"

    a = taggedRankedLabel @"A"
    b = taggedRankedLabel @"B"
    c = taggedRankedLabel @"C"
    d = taggedRankedLabel @"D"
    e = taggedRankedLabel @"E"
    f = taggedRankedLabel @"F"


type InfixOpAlphabet = TaggedRankedAlphabet
  ['("one", 0), '("two", 0), '("plus", 2), '("multi", 2)]

type PostfixOpAlphabet = TaggedRankedAlphabet
  ['("one", 1), '("two", 1), '("plus", 1), '("multi", 1), '("end", 0)]

type SynItoPAttr = TaggedAlphabet
  '["a0"]

type InhItoPAttr = TaggedAlphabet
  '["a1"]

type InfixToPostfixAtt = AttTransducer
  SynItoPAttr
  InhItoPAttr
  (RankedLabelledTree InfixOpAlphabet)
  (RankedLabelledTree PostfixOpAlphabet)

-- | An attributed tree transducer converting infix to postfix
--
-- Sample:
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.Trans.Class
-- >>> iOne   = taggedRankedLabel @"one"
-- >>> iTwo   = taggedRankedLabel @"two"
-- >>> iPlus  = taggedRankedLabel @"plus"
-- >>> iMulti = taggedRankedLabel @"multi"
-- >>> inputInfixTree = mkTree iMulti [mkTree iTwo [], mkTree iPlus [mkTree iOne [], mkTree iTwo []]]
-- >>> treeTrans infixToPostfixAtt inputInfixTree
-- two(one(two(plus(multi(end)))))
--
infixToPostfixAtt :: InfixToPostfixAtt
infixToPostfixAtt = fromMaybe (error "unreachable") $ buildAtt
    a0
    [ (Synthesized (), SynAttrSide a0 0)
    , (Inherited   a1, AttLabelSide pEnd [])
    ]
    [ (Synthesized a0,    iOne,   AttLabelSide pOne [InhAttrSide a1])
    , (Synthesized a0,    iTwo,   AttLabelSide pTwo [InhAttrSide a1])
    , (Synthesized a0,    iPlus,  SynAttrSide a0 0)
    , (Inherited (a1, 0), iPlus,  SynAttrSide a0 1)
    , (Inherited (a1, 1), iPlus,  AttLabelSide pPlus [InhAttrSide a1])
    , (Synthesized a0,    iMulti, SynAttrSide a0 0)
    , (Inherited (a1, 0), iMulti, SynAttrSide a0 1)
    , (Inherited (a1, 1), iMulti, AttLabelSide pMulti [InhAttrSide a1])
    ]
  where
    a0 = taggedLabel @"a0"
    a1 = taggedLabel @"a1"

    iOne   = taggedRankedLabel @"one"
    iTwo   = taggedRankedLabel @"two"
    iPlus  = taggedRankedLabel @"plus"
    iMulti = taggedRankedLabel @"multi"

    pOne   = taggedRankedLabel @"one"
    pTwo   = taggedRankedLabel @"two"
    pPlus  = taggedRankedLabel @"plus"
    pMulti = taggedRankedLabel @"multi"
    pEnd   = taggedRankedLabel @"end"
