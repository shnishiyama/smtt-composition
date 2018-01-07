{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           SattPrelude

import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.Class
import           Data.Tree.Trans.Compose.Desc
import           Data.Tree.Trans.Decompose.MttToAtt
import           Data.Tree.Trans.MAC.Instances
import qualified Data.Tree.Trans.TOP                as TOP

main :: IO ()
main = do
    t1 <- treeTrans sampleMtt inputSampleTree
    print t1
    let (trans1, trans2) = decomposeMtt sampleMtt
    attTrans <- composeAtts (TOP.toAttributedTreeTransducer trans1) trans2
    t2 <- treeTrans attTrans inputSampleTree
    print t2
  where
    a = taggedRankedLabel @"A"; b = taggedRankedLabel @"B"; c = taggedRankedLabel @"C"; inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
