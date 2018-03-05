{-# LANGUAGE OverloadedLists #-}

module TreeTrans.Compose.ExtendVoigt04Spec where

import           SattPrelude
import           Test.Hspec

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Instances
import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.Class
import           Data.Tree.Trans.Compose.ExtendVoigt2004
import qualified Data.Tree.Trans.TOP                     as TOP
import           Data.Tree.Trans.TOP.Instances
import           Data.Tree.Trans.MAC.Instances
import qualified Data.Tree.Trans.SMAC                    as SMAC
import           Data.Tree.Trans.SMAC.Instances


spec :: Spec
spec = do
  describe "composeSmttNCAndMttWSU" $ do
    it "should be equal to original semantics for i2pr/rev" $ do
      let inputInfixTree = buildTree (51 :: Int)

      trans <- composeSmttNCAndMttWSU (SMAC.toStackMacroTreeTransducer infixToPrefixMtt) reverseMtt

      t1 <- treeTrans trans inputInfixTree
      t2 <- treeTrans infixToPrefixMtt >=> treeTrans reverseMtt $ inputInfixTree

      t1 `shouldBe` t2

    it "should be equal to original semantics for itop/rev" $ do
      let inputInfixTree = buildTree (51 :: Int)

      trans <- composeSmttNCAndMttWSU (SMAC.toStackMacroTreeTransducer infixToPostfixMtt) reverseMtt

      t1 <- treeTrans trans inputInfixTree
      t2 <- treeTrans infixToPostfixMtt >=> treeTrans reverseMtt $ inputInfixTree

      t1 `shouldBe` t2

    it "should be equal to original semantics for ptoi/counter" $ do
      let inputInfixTree = buildTree (51 :: Int)
      inputPostfixTree <- treeTrans infixToPostfixMtt inputInfixTree

      trans <- composeSmttNCAndMttWSU postfixToInfixSmtt twoCounterMtt

      t1 <- treeTrans trans inputPostfixTree
      t2 <- treeTrans twoCounterMtt <=< treeTrans postfixToInfixSmtt $ inputPostfixTree

      t1 `shouldBe` t2

    it "should be equal to original semantics for ptoi/itop" $ do
      let inputInfixTree = buildTree (51 :: Int)
      inputPostfixTree <- treeTrans infixToPostfixMtt inputInfixTree

      trans <- composeSmttNCAndMttWSU postfixToInfixSmtt infixToPostfixMtt

      t1 <- treeTrans trans inputPostfixTree
      t2 <- treeTrans infixToPostfixMtt <=< treeTrans postfixToInfixSmtt $ inputPostfixTree

      t1 `shouldBe` t2
      t1 `shouldBe` inputPostfixTree

    it "should be equal to original semantics for po2i/i2pr" $ do
      let inputInfixTree = buildTree (51 :: Int)
      inputPostfixTree <- treeTrans infixToPostfixMtt inputInfixTree

      trans <- composeSmttNCAndMttWSU postfixToInfixSmtt infixToPrefixMtt

      t1 <- treeTrans trans inputPostfixTree
      t2 <- treeTrans postfixToInfixSmtt >=> treeTrans infixToPrefixMtt $ inputPostfixTree

      t1 `shouldBe` t2

    it "should be equal to original semantics for pr2i/i2pr" $ do
      let inputInfixTree = buildTree (51 :: Int)
      inputPrefixTree <- treeTrans infixToPrefixMtt inputInfixTree

      trans <- composeSmttNCAndMttWSU prefixToInfixSmtt infixToPrefixMtt

      t1 <- treeTrans trans inputPrefixTree
      t2 <- treeTrans prefixToInfixSmtt >=> treeTrans infixToPrefixMtt $ inputPrefixTree

      t1 `shouldBe` t2
      t1 `shouldBe` inputPrefixTree

    it "should be equal to original semantics for pr2i/i2po" $ do
      let inputInfixTree = buildTree (51 :: Int)
      inputPrefixTree <- treeTrans infixToPrefixMtt inputInfixTree

      trans <- composeSmttNCAndMttWSU prefixToInfixSmtt infixToPostfixMtt

      t1 <- treeTrans trans inputPrefixTree
      t2 <- treeTrans prefixToInfixSmtt >=> treeTrans infixToPostfixMtt $ inputPrefixTree

      t1 `shouldBe` t2

    it "should be equal to original semantics for ptoi/depth" $ do
      let inputInfixTree = buildTree (51 :: Int)
      inputPostfixTree <- treeTrans infixToPostfixMtt inputInfixTree

      trans <- composeSmttNCAndMttWSU postfixToInfixSmtt (TOP.toMacroTreeTransducer depthRightSideTdtt)

      t1 <- treeTrans trans inputPostfixTree
      t2 <- treeTrans depthRightSideTdtt <=< treeTrans postfixToInfixSmtt $ inputPostfixTree

      t1 `shouldBe` t2

    it "should be equal to original semantics for mirror/depth" $ do
      let inputInfixTree = buildTree (51 :: Int)

      trans <- composeSmttNCAndMttWSU
        (SMAC.toStackMacroTreeTransducer $ TOP.toMacroTreeTransducer mirrorTdtt)
        (TOP.toMacroTreeTransducer depthRightSideTdtt)

      t1 <- treeTrans trans inputInfixTree
      t2 <- treeTrans mirrorTdtt >=> treeTrans depthRightSideTdtt $ inputInfixTree

      t1 `shouldBe` t2

buildTree :: Int -> InfixOpTree
buildTree n
  | n <= 0 || n `mod` 2 == 0 = error "negative or even number"
  | otherwise                = go True $ n `div` 2
  where
    iOne = taggedRankedLabel @"one"
    iTwo = taggedRankedLabel @"two"
    iPlus = taggedRankedLabel @"plus"
    iMulti = taggedRankedLabel @"multi"

    go True  0 = mkTree iOne []
    go False 0 = mkTree iTwo []
    go True  m = mkTree iPlus
      [ go False $ m `div` 3
      , go True $ m - (m `div` 3) - 1
      ]
    go False m = mkTree iMulti
      [ go True  $ m `div` 2
      , go False $ m - (m `div` 2) - 1
      ]
