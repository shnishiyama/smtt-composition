{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.SMAC.Instances where

import           SattPrelude

import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.SMAC

type InputSampleAlphabet = TaggedRankedAlphabet
  ['("A", 2), '("B", 1), '("C", 0)]

type OutputSampleAlphabet = TaggedRankedAlphabet
  ['("D", 2), '("E", 1), '("F", 0)]

type SampleStateAlphabet = TaggedRankedAlphabet
  ['("f0", 2), '("f1", 2)]

type SampleSmtt = SmttTransducer
  SampleStateAlphabet
  (RankedLabelledTree InputSampleAlphabet)
  (RankedLabelledTree OutputSampleAlphabet)

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
          (SmttLabelSide d [SmttStackHead $ SmttState f0 0 [SmttContext 0], SmttContext 0])
          SmttStackEmpty
        ])
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
