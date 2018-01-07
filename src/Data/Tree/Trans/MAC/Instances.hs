{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.MAC.Instances where

import           SattPrelude

import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.MAC

type InputSampleAlphabet = TaggedRankedAlphabet
  ['("A", 2), '("B", 1), '("C", 0)]

type OutputSampleAlphabet = TaggedRankedAlphabet
  ['("D", 2), '("E", 1), '("F", 0)]

type SampleStateAlphabet = TaggedRankedAlphabet
  ['("f0", 2), '("f1", 2)]

type SampleMtt = MttTransducer
  SampleStateAlphabet
  (RankedLabelledTree InputSampleAlphabet)
  (RankedLabelledTree OutputSampleAlphabet)

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
