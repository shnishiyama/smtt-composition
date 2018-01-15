{-# LANGUAGE OverloadedLists #-}

module TreeTrans.Compose.ExtendVoigt04Spec where

import           SattPrelude
import           Test.Hspec

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Instances
import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.Class
import           Data.Tree.Trans.Compose.ExtendVoigt2004
import           Data.Tree.Trans.MAC.Instances
import           Data.Tree.Trans.SMAC.Instances


spec :: Spec
spec = do
  describe "composeSmttNCAndMttWSU" $ do
    it "should be equal to original semantics" $ do
      let inputInfixTree = buildTree (51 :: Int)
      inputPostfixTree <- treeTrans infixToPostfixMtt inputInfixTree

      trans <- composeSmttNCAndMttWSU postfixToInfixSmtt twoCounterMtt

      t1 <- treeTrans trans inputPostfixTree
      t2 <- treeTrans twoCounterMtt <=< treeTrans postfixToInfixSmtt $ inputPostfixTree

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
