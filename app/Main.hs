{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}

module Main where

import           SattPrelude

import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.Class
import           Data.Tree.Trans.Compose.ExtendVoigt2004
import           Data.Tree.Trans.SMAC.Instances
import           Data.Tree.Trans.MAC.Instances

main :: IO ()
main = do
    trans <- composeSmttNCAndMttWSU postfixToInfixSmtt infixToPostfixMtt
    t <- treeTrans trans inputPostfixTree
    print t
  where
    -- a = taggedRankedLabel @"A"; b = taggedRankedLabel @"B"; c = taggedRankedLabel @"C"; inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
    pOne = taggedRankedLabel @"one";pTwo = taggedRankedLabel @"two";pPlus = taggedRankedLabel @"plus";pMulti = taggedRankedLabel @"multi";pEnd = taggedRankedLabel @"end";inputPostfixTree = mkTree pTwo [mkTree pOne [ mkTree pTwo [mkTree pPlus [mkTree pMulti [mkTree pEnd []]]]]]
