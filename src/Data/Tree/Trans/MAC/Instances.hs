{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.MAC.Instances where

import SattPrelude

import Data.Tree.RankedTree.Label
import Data.Tree.Trans.MAC

type InputSampleAlphabet = TaggedRankedAlphabet
  ['("A", 2), '("B", 1), '("C", 0)]

type OutputSampleAlphabet = TaggedRankedAlphabet
  ['("D", 2), '("E", 1), '("F", 0)]

type SampleStateAlphabet = TaggedRankedAlphabet
  ['("f1", 2), '("f2", 2)]

type SampleMtt = MttTransducer
  SampleStateAlphabet
  (RankedLabelledTree InputSampleAlphabet)
  (RankedLabelledTree OutputSampleAlphabet)

sampleMtt :: SampleMtt
sampleMtt = fromMaybe (error "unreachable") $ buildMtt
    (MttState f1 0 [MttLabelSide f []])
    [ (f1, a, MttState f1 0 [MttState f2 1 [MttContext 0]])
    , (f1, b, MttLabelSide e [MttContext 0])
    , (f1, c, MttContext 0)
    , (f2, a, MttContext 0)
    , (f2, b, MttState f2 0 [MttLabelSide d [MttState f1 0 [MttContext 0], MttContext 0]])
    , (f2, c, MttContext 0)
    ]
  where
    f1 = taggedLabel @"f1"
    f2 = taggedLabel @"f2"

    a = taggedLabel @"A"
    b = taggedLabel @"B"
    c = taggedLabel @"C"
    d = taggedLabel @"D"
    e = taggedLabel @"E"
    f = taggedLabel @"F"
