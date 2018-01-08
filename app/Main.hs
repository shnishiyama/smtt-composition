{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           SattPrelude

import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.Class
import           Data.Tree.Trans.Compose.ExtendVoigt2004
import           Data.Tree.Trans.Decompose.SmttToSatt
import           Data.Tree.Trans.SMAC.Instances
import           Data.Tree.Trans.MAC.Instances
import qualified Data.Tree.Trans.SMAC as SMAC

main :: IO ()
main = do
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
    -- a = taggedRankedLabel @"A"; b = taggedRankedLabel @"B"; c = taggedRankedLabel @"C"; inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
    pOne = taggedRankedLabel @"one";pTwo = taggedRankedLabel @"two";pPlus = taggedRankedLabel @"plus";pMulti = taggedRankedLabel @"multi";pEnd = taggedRankedLabel @"end";inputPostfixTree = mkTree pTwo [mkTree pOne [ mkTree pTwo [mkTree pPlus [mkTree pMulti [mkTree pEnd []]]]]]
