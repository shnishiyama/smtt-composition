{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -Wno-unused-imports #-}

module Main where

import           SattPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Instances
import           Data.Tree.RankedTree.Label
import           Data.Tree.RankedTree.Zipper
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
    let inputInfixTree = buildTree (51 :: Int)
    print inputInfixTree
    inputPostfixTree <- treeTrans infixToPostfixMtt inputInfixTree

    trans <- composeSmttNCAndMttWSU postfixToInfixSmtt twoCounterMtt
    print trans

    print <=< treeTrans trans $ inputPostfixTree
    print <=< treeTrans twoCounterMtt <=< treeTrans postfixToInfixSmtt $ inputPostfixTree
  where
    iOne = taggedRankedLabel @"one"
    iTwo = taggedRankedLabel @"two"
    iPlus = taggedRankedLabel @"plus"
    iMulti = taggedRankedLabel @"multi"

    buildTree n
      | n <= 0 || n `mod` 2 == 0 = error "negative or even number"
      | otherwise                = buildTree' True $ n `div` 2

    buildTree' True  0 = mkTree iOne []
    buildTree' False 0 = mkTree iTwo []
    buildTree' True  n = mkTree iPlus
      [ buildTree' False $ n `div` 3
      , buildTree' True $ n - (n `div` 3) - 1
      ]
    buildTree' False n = mkTree iMulti
      [ buildTree' True  $ n `div` 2
      , buildTree' False $ n - (n `div` 2) - 1
      ]
