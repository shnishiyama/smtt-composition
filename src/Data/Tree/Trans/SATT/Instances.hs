{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.SATT.Instances where

import           SattPrelude

import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.SATT

type InputSampleAlphabet = TaggedRankedAlphabet
  ['("A", 2), '("B", 1), '("C", 0)]

type OutputSampleAlphabet = TaggedRankedAlphabet
  ['("D", 2), '("E", 1), '("F", 0)]

type SynSampleAttr = TaggedAlphabet
  ["a0", "a1"]

type InhSampleAttr = TaggedAlphabet
  ["b0", "b1"]

type SampleSatt = SattTransducer
  SynSampleAttr
  InhSampleAttr
  (RankedLabelledTree InputSampleAlphabet)
  (RankedLabelledTree OutputSampleAlphabet)

-- | A sample stack attributed tree transducer
--
-- Sample:
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> treeTrans sampleSatt inputSampleTree
-- D(F,F)
-- >>> treeTrans (toStandardForm sampleSatt) inputSampleTree
-- D(F,F)
--
sampleSatt :: SampleSatt
sampleSatt = fromMaybe (error "unreachable") $ buildSatt
    a0
    [ (Synthesized (), SynAttrSide a0 0)
    , (Inherited   b0, SattStackCons
        (SattLabelSide f [])
        SattStackEmpty
      )
    , (Inherited   b1, SattStackCons
        (SattLabelSide f [])
        SattStackEmpty
      )
    ]
    [ (Synthesized a0,    a, SynAttrSide a0 0)
    , (Inherited (b0, 0), a, SynAttrSide a1 1)
    , (Inherited (b0, 1), a, InhAttrSide b0)
    , (Synthesized a0,    b, SattStackTail
        (SattStackCons
          SattStackBottom
          (SattStackCons
            (SattLabelSide e
              [ SattStackHead $ InhAttrSide b0
              ])
            SattStackEmpty
          )
        )
      )
    , (Inherited (b0, 0), b, InhAttrSide b0)
    , (Synthesized a0,    c, InhAttrSide b0)
    , (Synthesized a1,    a, InhAttrSide b1)
    , (Inherited (b1, 0), a, SynAttrSide a1 1)
    , (Inherited (b1, 1), a, InhAttrSide b1)
    , (Synthesized a1,    b, SynAttrSide a1 0)
    , (Inherited (b1, 0), b, SattStackCons
        (SattLabelSide d
          [ SattStackHead $ SynAttrSide a0 0
          , SattStackHead $ InhAttrSide b1
          ])
        (SattStackCons
          SattStackBottom
          SattStackEmpty
        )
      )
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
