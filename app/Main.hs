{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Main where

import           SattPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Instances
import           Data.Tree.RankedTree.Label
import qualified Data.Tree.Trans.ATT                     as ATT
import           Data.Tree.Trans.ATT.Instances           as ATT
import           Data.Tree.Trans.Class
import           Data.Tree.Trans.Compose.ExtendDesc
import           Data.Tree.Trans.Compose.ExtendVoigt2004
import           Data.Tree.Trans.Decompose.SmttToSatt
import           Data.Tree.Trans.MAC.Instances
import qualified Data.Tree.Trans.SATT                    as SATT
import           Data.Tree.Trans.SATT.Instances          as SATT
import qualified Data.Tree.Trans.SMAC                    as SMAC
import           Data.Tree.Trans.SMAC.Instances
import qualified Data.Tree.Trans.TOP                     as TOP
import           Data.Tree.Trans.TOP.Instances           as TOP

main :: IO ()
main = do
    let traUniverse = setFromList $ taggedRankedAlphabetUniverse Proxy
    let identInputTrans = identitySatt @InputSampleTree traUniverse
    identSampleTrans <- composeSattAndAtt identInputTrans ATT.sampleAtt
    print <=< treeTrans identSampleTrans $ inputSampleTree

    trans <- composeSmttNCAndMttWSU postfixToInfixSmtt infixToPostfixMtt
    print trans

    putStrLn "------ reduction steps ------"
    let reds = SMAC.runSmttReductionWithHistory trans . SMAC.toInitialReductionState trans $ inputPostfixTree
    forM_ reds groomPrint

    putStrLn "------ non satt-composition ------"
    (preTdtt, trans1Satt) <- decomposeSmttNC postfixToInfixSmtt
    trans2Att <- fromMttWSUToAtt infixToPostfixMtt
    t1 <- treeTrans trans2Att <=< treeTrans trans1Satt <=< treeTrans preTdtt $ inputPostfixTree
    print t1

    putStrLn "------ with satt-composition ------"
    t2 <- treeTrans trans inputPostfixTree
    print t2
  where
    a = taggedRankedLabel @"A"; b = taggedRankedLabel @"B"; c = taggedRankedLabel @"C"; inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
    pOne = taggedRankedLabel @"one";pTwo = taggedRankedLabel @"two";pPlus = taggedRankedLabel @"plus";pMulti = taggedRankedLabel @"multi";pEnd = taggedRankedLabel @"end";inputPostfixTree = mkTree pTwo [mkTree pOne [ mkTree pTwo [mkTree pPlus [mkTree pMulti [mkTree pEnd []]]]]]

    identitySatt :: (RankedTree ta, Eq (LabelType ta), Hashable (LabelType ta))
      => HashSet (LabelType ta) -> SATT.SattTransducer () Void ta ta
    identitySatt = SATT.toStackAttributedTreeTransducer . identityAtt

    identityAtt :: (RankedTree ta, Eq (LabelType ta), Hashable (LabelType ta))
      => HashSet (LabelType ta) -> ATT.AttTransducer () Void ta ta
    identityAtt = TOP.toAttributedTreeTransducer . TOP.identityTransducer
