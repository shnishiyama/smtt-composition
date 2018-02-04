{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.TOP.Instances where

import           SattPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Instances
import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.TOP
import qualified Data.Vector                as V

identityTransducer :: forall t l.
  ( RtConstraint t l
  , Eq l, Hashable l
  )
  => HashSet l -> TopDownTreeTransducer () t l t l
identityTransducer ls = fromMaybe errorUnreachable $ buildTdtt
  (tdttState () 0)
  [ ((), l, TdttLabelSide l $ V.generate r (tdttState ()))
  | l <- setToList ls
  , let r = treeLabelRank (Proxy @t) l
  ]

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
sampleTdtt = fromMaybe errorUnreachable $ buildTdtt
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


type DepthStateAlphabet = TaggedAlphabet
  '[ "f0" ]

type DepthRightSideTdtt = TdttTransducer
  DepthStateAlphabet
  InfixOpTree NatNum

-- | A depth counter for right side
--
-- Sample:
-- >>> :set -XOverloadedLists
-- >>> import Data.Tree.Trans.Class
-- >>> iOne   = taggedRankedLabel @"one"
-- >>> iTwo   = taggedRankedLabel @"two"
-- >>> iPlus  = taggedRankedLabel @"plus"
-- >>> iMulti = taggedRankedLabel @"multi"
-- >>> :{
-- inputInfixTree = mkTree iMulti [mkTree iTwo [], mkTree iPlus [mkTree iOne [], mkTree iTwo []]]
-- :}
--
-- >>> treeTrans depthRightSideTdtt inputInfixTree
-- Succ (Succ Zero)
--
depthRightSideTdtt :: DepthRightSideTdtt
depthRightSideTdtt = fromMaybe errorUnreachable $ buildTdtt
    (tdttState f0 0)
    [ (f0, iPlus,  TdttLabelSide True [tdttState f0 0])
    , (f0, iMulti, TdttLabelSide True [tdttState f0 0])
    , (f0, iOne,   TdttLabelSide True [TdttLabelSide False []])
    , (f0, iTwo,   TdttLabelSide True [TdttLabelSide False []])
    ]
  where
    f0 = taggedLabel @"f0"

    iOne   = taggedRankedLabel @"one"
    iTwo   = taggedRankedLabel @"two"
    iPlus  = taggedRankedLabel @"plus"
    iMulti = taggedRankedLabel @"multi"
