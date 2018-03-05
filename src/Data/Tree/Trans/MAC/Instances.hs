{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.MAC.Instances where

import           SattPrelude

import           Data.Tree.RankedTree.Instances
import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.MAC

type SampleStateAlphabet = TaggedRankedAlphabet
  ['("f0", 2), '("f1", 2)]

type SampleMtt = MttTransducer
  SampleStateAlphabet
  InputSampleTree OutputSampleTree

-- | A sample macro tree transducer
--
-- Sample:
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> treeTrans sampleMtt inputSampleTree
-- D(F,F)
--
sampleMtt :: SampleMtt
sampleMtt = fromMaybe errorUnreachable $ buildMtt
    (MttState f0 0 [MttLabelSide f []])
    [ (f0, a, MttState f0 0 [MttState f1 1 [MttContext 0]])
    , (f0, b, MttLabelSide e [MttContext 0])
    , (f0, c, MttContext 0)
    , (f1, a, MttContext 0)
    , (f1, b, MttState f1 0 [MttLabelSide d [MttState f0 0 [MttContext 0], MttContext 0]])
    , (f1, c, MttContext 0)
    ]
  where
    f0 = taggedRankedLabel @"f0"
    f1 = taggedRankedLabel @"f1"

    a = taggedRankedLabel @"A"
    b = taggedRankedLabel @"B"
    c = taggedRankedLabel @"C"
    d = taggedRankedLabel @"D"
    e = taggedRankedLabel @"E"
    f = taggedRankedLabel @"F"


type ItoPStateAlphabet = TaggedRankedAlphabet
  '[ '("f0", 2)]

type InfixToPostfixSmtt = MttTransducer
  ItoPStateAlphabet
  InfixOpTree PostfixOpTree

-- | A macro tree transducer to postfix tree from infix tree
--
-- Sample:
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.Trans.Class
-- >>> iOne   = taggedRankedLabel @"one"
-- >>> iTwo   = taggedRankedLabel @"two"
-- >>> iPlus  = taggedRankedLabel @"plus"
-- >>> iMulti = taggedRankedLabel @"multi"
-- >>> inputInfixTree = mkTree iMulti [mkTree iTwo [], mkTree iPlus [mkTree iOne [], mkTree iTwo []]]
-- >>> treeTrans infixToPostfixMtt inputInfixTree
-- two(one(two(plus(multi(end)))))
--
infixToPostfixMtt :: InfixToPostfixSmtt
infixToPostfixMtt = fromMaybe errorUnreachable $ buildMtt
    (MttState f0 0 [MttLabelSide pEnd []])
    [ (f0, iOne, MttLabelSide pOne [MttContext 0])
    , (f0, iTwo, MttLabelSide pTwo [MttContext 0])
    , (f0, iPlus, MttState f0 0 [MttState f0 1 [MttLabelSide pPlus [MttContext 0]]])
    , (f0, iMulti, MttState f0 0 [MttState f0 1 [MttLabelSide pMulti [MttContext 0]]])
    ]
  where
    f0 = taggedRankedLabel @"f0"

    iOne   = taggedRankedLabel @"one"
    iTwo   = taggedRankedLabel @"two"
    iPlus  = taggedRankedLabel @"plus"
    iMulti = taggedRankedLabel @"multi"

    pOne   = taggedRankedLabel @"one"
    pTwo   = taggedRankedLabel @"two"
    pPlus  = taggedRankedLabel @"plus"
    pMulti = taggedRankedLabel @"multi"
    pEnd   = taggedRankedLabel @"end"


type I2PrStateAlphabet = TaggedRankedAlphabet
  '[ '("f0", 2)]

type InfixToPrefixSmtt = MttTransducer
  I2PrStateAlphabet
  InfixOpTree PrefixOpTree

-- | A macro tree transducer to prefix tree from infix tree
--
-- Sample:
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.Trans.Class
-- >>> iOne   = taggedRankedLabel @"one"
-- >>> iTwo   = taggedRankedLabel @"two"
-- >>> iPlus  = taggedRankedLabel @"plus"
-- >>> iMulti = taggedRankedLabel @"multi"
-- >>> inputInfixTree = mkTree iMulti [mkTree iTwo [], mkTree iPlus [mkTree iOne [], mkTree iTwo []]]
-- >>> treeTrans infixToPrefixMtt inputInfixTree
-- multi(two(plus(one(two(end)))))
--
infixToPrefixMtt :: InfixToPrefixSmtt
infixToPrefixMtt = fromMaybe errorUnreachable $ buildMtt
    (MttState f0 0 [MttLabelSide pEnd []])
    [ (f0, iOne, MttLabelSide pOne [MttContext 0])
    , (f0, iTwo, MttLabelSide pTwo [MttContext 0])
    , (f0, iPlus, MttLabelSide pPlus [MttState f0 0 [MttState f0 1 [MttContext 0]]])
    , (f0, iMulti, MttLabelSide pMulti [MttState f0 0 [MttState f0 1 [MttContext 0]]])
    ]
  where
    f0 = taggedRankedLabel @"f0"

    iOne   = taggedRankedLabel @"one"
    iTwo   = taggedRankedLabel @"two"
    iPlus  = taggedRankedLabel @"plus"
    iMulti = taggedRankedLabel @"multi"

    pOne   = taggedRankedLabel @"one"
    pTwo   = taggedRankedLabel @"two"
    pPlus  = taggedRankedLabel @"plus"
    pMulti = taggedRankedLabel @"multi"
    pEnd   = taggedRankedLabel @"end"


type MiniInfixToPostfixMtt = MttTransducer
  ItoPStateAlphabet
  MiniInfixOpTree MiniPostfixOpTree

miniInfixToPostfixMtt :: MiniInfixToPostfixMtt
miniInfixToPostfixMtt = fromMaybe errorUnreachable $ buildMtt
    (MttState f0 0 [MttLabelSide pEnd []])
    [ (f0, iOne, MttLabelSide pOne [MttContext 0])
    , (f0, iPlus, MttState f0 0 [MttState f0 1 [MttLabelSide pPlus [MttContext 0]]])
    ]
  where
    f0 = taggedRankedLabel @"f0"

    iOne   = taggedRankedLabel @"one"
    iPlus  = taggedRankedLabel @"plus"

    pOne   = taggedRankedLabel @"one"
    pPlus  = taggedRankedLabel @"plus"
    pEnd   = taggedRankedLabel @"end"


type TwoCounterStateAlphabet = TaggedRankedAlphabet
  '[ '("f0", 2)]

type TwoCounterMtt = MttTransducer
  TwoCounterStateAlphabet
  InfixOpTree NatNum

twoCounterMtt :: TwoCounterMtt
twoCounterMtt = fromMaybe errorUnreachable $ buildMtt
    (MttState f0 0 [MttLabelSide False []])
    [ (f0, iOne, MttContext 0)
    , (f0, iTwo, MttLabelSide True [MttContext 0])
    , (f0, iPlus, MttState f0 0 [MttState f0 1 [MttContext 0]])
    , (f0, iMulti, MttState f0 0 [MttState f0 1 [MttContext 0]])
    ]
  where
    f0 = taggedRankedLabel @"f0"

    iOne   = taggedRankedLabel @"one"
    iTwo   = taggedRankedLabel @"two"
    iPlus  = taggedRankedLabel @"plus"
    iMulti = taggedRankedLabel @"multi"


type ReverseStateAlphabet = TaggedRankedAlphabet
  '[ '("f0", 2)]

type ReverseMtt = MttTransducer
  ReverseStateAlphabet
  PostfixOpTree PostfixOpTree

reverseMtt :: ReverseMtt
reverseMtt = fromMaybe errorUnreachable $ buildMtt
    (MttState f0 0 [MttLabelSide pEnd []])
    [ (f0, pOne, MttState f0 0 [MttLabelSide pOne [MttContext 0]])
    , (f0, pTwo, MttState f0 0 [MttLabelSide pTwo [MttContext 0]])
    , (f0, pMulti, MttState f0 0 [MttLabelSide pMulti [MttContext 0]])
    , (f0, pPlus, MttState f0 0 [MttLabelSide pPlus [MttContext 0]])
    , (f0, pEnd, MttContext 0)
    ]
  where
    f0 = taggedRankedLabel @"f0"

    pOne   = taggedRankedLabel @"one"
    pTwo   = taggedRankedLabel @"two"
    pPlus  = taggedRankedLabel @"plus"
    pMulti = taggedRankedLabel @"multi"
    pEnd   = taggedRankedLabel @"end"


type FlatStateAlphabet = TaggedRankedAlphabet
  '[ '("f0", 2)]

type FlatRightSideMtt = MttTransducer
  FlatStateAlphabet
  InfixOpTree PostfixOpTree

flatRightSideMtt :: FlatRightSideMtt
flatRightSideMtt = fromMaybe errorUnreachable $ buildMtt
    (MttState f0 0 [MttLabelSide pEnd []])
    [ (f0, iOne, MttLabelSide pOne [MttContext 0])
    , (f0, iTwo, MttLabelSide pTwo [MttContext 0])
    , (f0, iMulti, MttState f0 0 [MttLabelSide pMulti [MttContext 0]])
    , (f0, iPlus,  MttState f0 0 [MttLabelSide pPlus  [MttContext 0]])
    ]
  where
    f0 = taggedRankedLabel @"f0"

    pOne   = taggedRankedLabel @"one"
    pTwo   = taggedRankedLabel @"two"
    pPlus  = taggedRankedLabel @"plus"
    pMulti = taggedRankedLabel @"multi"
    pEnd   = taggedRankedLabel @"end"

    iOne   = taggedRankedLabel @"one"
    iTwo   = taggedRankedLabel @"two"
    iPlus  = taggedRankedLabel @"plus"
    iMulti = taggedRankedLabel @"multi"
