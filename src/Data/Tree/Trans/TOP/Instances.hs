{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.TOP.Instances where

import           SattPrelude

import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.TOP

type InputSampleAlphabet = TaggedRankedAlphabet
  ['("A", 2), '("B", 1), '("C", 0)]

type OutputSampleAlphabet = TaggedRankedAlphabet
  ['("D", 2), '("E", 1), '("F", 0)]

type SampleStateAlphabet = TaggedAlphabet
  ["f0", "f1"]

type SampleTdtt = TdttTransducer
  SampleStateAlphabet
  (RankedLabelledTree InputSampleAlphabet)
  (RankedLabelledTree OutputSampleAlphabet)

-- | A sample top-down tree transducer
--
-- Sample:
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> treeTrans sampleTdtt inputSampleTree
-- D(F,E(F))
--
sampleTdtt :: SampleTdtt
sampleTdtt = fromMaybe (error "unreachable") $ buildTdtt
    (tdttState f0 0)
    [ (f0, a, TdttLabelSide d [tdttState f1 0, tdttState f0 1])
    , (f0, b, TdttLabelSide e [tdttState f0 0])
    , (f0, c, TdttLabelSide f [])
    , (f1, a, tdttState f0 0)
    , (f1, b, TdttLabelSide d [tdttState f0 0, tdttState f1 0])
    , (f1, c, TdttLabelSide f [])
    ]
  where
    f0 = taggedLabel @"f0"
    f1 = taggedLabel @"f1"

    a = taggedRankedLabel @"A"
    b = taggedRankedLabel @"B"
    c = taggedRankedLabel @"C"
    d = taggedRankedLabel @"D"
    e = taggedRankedLabel @"E"
    f = taggedRankedLabel @"F"
