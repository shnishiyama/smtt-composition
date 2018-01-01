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

type SynSampleAttr = TaggedAlphabet
  ["a0", "a1"]

type InhSampleAttr = TaggedAlphabet
  ["b0", "b1"]

type InputSampleAlphabet = TaggedRankedAlphabet
  ['("A", 2), '("B", 1), '("C", 0)]

type OutputSampleAlphabet = TaggedRankedAlphabet
  ['("D", 2), '("E", 1), '("F", 0)]

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
