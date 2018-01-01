{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           SattPrelude

import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.ATT.Instances
import           Data.Tree.Trans.Class
import           Data.Tree.Trans.Compose.Desc

main :: IO ()
main = do
    t1 <- treeTrans (composeAtts sampleAtt identOutputTrans) inputSampleTree
    print t1
    t2 <- treeTrans (composeAtts identInputTrans sampleAtt) inputSampleTree
    print t2
  where
    a = taggedRankedLabel @"A"
    b = taggedRankedLabel @"B"
    c = taggedRankedLabel @"C"

    inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]

    identInputTrans = identityTransducer @(RankedLabelledTree InputSampleAlphabet)
      $ setFromList $ taggedRankedAlphabetUniverse Proxy
    identOutputTrans = identityTransducer @(RankedLabelledTree OutputSampleAlphabet)
      $ setFromList $ taggedRankedAlphabetUniverse Proxy
