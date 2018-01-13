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
    (preTdtt, trans1Satt) <- decomposeSmttNC miniPostfixToInfixSmtt
    trans2Att <- fromMttWSUToAtt twoCounterMtt
    postSatt <- composeSattAndAtt trans1Satt trans2Att
    let postSmtt = SATT.toStackMacroTreeTransducer postSatt
    t <- treeTrans preTdtt inputPostfixTree

    groomPrint $ fmap SATT.prettyShowReductionState $ SATT.runSattReductionWithHistory postSatt $ SATT.toInitialReductionState @RTZipper postSatt t
    putStrLn "------"
    groomPrint $ fmap SMAC.prettyShowReductionState $ SMAC.runSmttReductionWithHistory postSmtt $ SMAC.toInitialReductionState postSmtt t
  where
    pOne = taggedRankedLabel @"one"; pPlus = taggedRankedLabel @"plus"; pEnd = taggedRankedLabel @"end"; inputPostfixTree = mkTree pOne [mkTree pOne [mkTree pPlus [mkTree pEnd []]]]
