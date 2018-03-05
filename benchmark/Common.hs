{-# OPTIONS_GHC -Wno-unused-imports #-}

module Main where

import           SattPrelude
import           Test.Hspec

import           Fusion
import           Samples.Instances
import           Samples.TermOpParser
import           Samples.Fusions

main :: IO ()
main = hspec spec

shouldBeDoing :: a -> TestCase a -> Expectation
shouldBeDoing x (TestCase f1 f2) = f1 x `shouldBe` f2 x

data TestCase a where
  TestCase :: (Show b, Eq b) => (a -> b) -> (a -> b) -> TestCase a

spec :: Spec
spec = do
  describe "fusions" $ do
    it "preserve original semantics" $ do
      let inputInfixOpTree = evalRandomState 0 $ buildInfixOpTree $ 2 * 25 + 1
      traverse_ (shouldBeDoing inputInfixOpTree)
        [ TestCase (i2pr >>> reversePop) i2prRev
        ]

      let inputPostfixOpTree = i2po inputInfixOpTree
      traverse_ (shouldBeDoing inputPostfixOpTree)
        [ TestCase (po2i >>> twoCounter) po2iTwocounter
        , TestCase (po2i >>> i2pr) po2iI2pr
        , TestCase (po2i >>> depthRightSide) po2iDepth
        , TestCase (po2i >>> flatRightSide) po2iFlat
        ]

      let inputPrefixOpTree = i2pr inputInfixOpTree
      traverse_ (shouldBeDoing inputPrefixOpTree)
        [ TestCase (pr2i >>> i2pr) pr2iI2pr
        ]
