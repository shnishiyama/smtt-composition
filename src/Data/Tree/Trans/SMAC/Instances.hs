{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.SMAC.Instances where

import           SattPrelude

import           Data.Tree.RankedTree.Instances
import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.SMAC

type SampleStateAlphabet = TaggedRankedAlphabet
  ['("f0", 2), '("f1", 2)]

type SampleSmtt = SmttTransducer
  SampleStateAlphabet
  InputSampleTree OutputSampleTree

-- | A sample stack macro tree transducer
--
-- Sample:
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> treeTrans sampleSmtt inputSampleTree
-- D(F,F)
--
sampleSmtt :: SampleSmtt
sampleSmtt = fromMaybe errorUnreachable $ buildSmtt
    (SmttState f0 0 [SmttStackCons (SmttLabelSide f []) SmttStackEmpty])
    [ (f0, a, SmttState f0 0 [SmttState f1 1 [SmttContext 0]])
    , (f0, b, SmttStackCons (SmttLabelSide e [SmttStackHead $ SmttContext 0]) SmttStackEmpty)
    , (f0, c, SmttContext 0)
    , (f1, a, SmttContext 0)
    , (f1, b, SmttState f1 0
        [ SmttStackCons
          (SmttLabelSide d
            [ SmttStackHead $ SmttState f0 0 [SmttContext 0]
            , SmttStackHead $ SmttContext 0
            ])
          SmttStackEmpty
        ])
    , (f1, c, SmttContext 0)
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


type PtoIStateAlphabet = TaggedRankedAlphabet
  '[ '("f0", 2)]

type PostfixToInfixSmtt = SmttTransducer
  PtoIStateAlphabet
  PostfixOpTree InfixOpTree

-- | A stack macro tree transducer to infix tree from postfix tree
--
-- Sample:
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.Trans.Class
-- >>> pOne   = taggedRankedLabel @"one"
-- >>> pTwo   = taggedRankedLabel @"two"
-- >>> pPlus  = taggedRankedLabel @"plus"
-- >>> pMulti = taggedRankedLabel @"multi"
-- >>> pEnd   = taggedRankedLabel @"end"
-- >>> :{
-- inputPostfixTree = mkTree pTwo [mkTree pOne [mkTree pTwo
--   [mkTree pPlus [mkTree pMulti [mkTree pEnd []]]]
--   ]]
-- :}
--
-- >>> treeTrans postfixToInfixSmtt inputPostfixTree
-- multi(two,plus(one,two))
--
postfixToInfixSmtt :: PostfixToInfixSmtt
postfixToInfixSmtt = fromMaybe errorUnreachable $ buildSmtt
    (SmttState f0 0 [SmttStackEmpty])
    [ (f0, pOne, SmttState f0 0 [SmttStackCons (SmttLabelSide iOne []) (SmttContext 0)])
    , (f0, pTwo, SmttState f0 0 [SmttStackCons (SmttLabelSide iTwo []) (SmttContext 0)])
    , (f0, pPlus, SmttState f0 0
      [ SmttStackCons
        (SmttLabelSide iPlus
          [ SmttStackHead $ SmttStackTail $ SmttContext 0
          , SmttStackHead $ SmttContext 0
          ])
        (SmttStackTail $ SmttStackTail $ SmttContext 0)
      ])
    , (f0, pMulti, SmttState f0 0
      [ SmttStackCons
        (SmttLabelSide iMulti
          [ SmttStackHead $ SmttStackTail $ SmttContext 0
          , SmttStackHead $ SmttContext 0
          ])
        (SmttStackTail $ SmttStackTail $ SmttContext 0)
      ])
    , (f0, pEnd, SmttContext 0)
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
