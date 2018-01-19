{-# LANGUAGE OverloadedLists   #-}
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
import           Text.PrettyPrint.Classy

main :: IO ()
main = do
    let inputTree = buildTree (3 :: Int)
    print inputTree

    trans <- composeSmttNCAndMttWSU sampleExpSmtt infixToPostfixMtt
    putDocLn $ pretty trans

    print <=< treeTrans trans $ inputTree
    print <=< treeTrans infixToPostfixMtt <=< treeTrans sampleExpSmtt $ inputTree
  where
    buildTree 1 = mkTree False []
    buildTree n = mkTree True [buildTree $ n - 1]
