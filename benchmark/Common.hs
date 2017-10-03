module Main where

import           Criterion.Main
import Control.DeepSeq

import Data.Tree.RankedTree.Instances
import Data.Tree.Trans.Class
import Data.Tree.Trans.ATT.Instances
-- import Data.Tree.Trans.SATT.Instances
import Data.Tree.Trans.ATT.Compose
-- import Data.Tree.Trans.SATT.Compose

mkInfixOpTreeSample :: Int -> InfixOpTree
mkInfixOpTreeSample 1 = InfixOne
mkInfixOpTreeSample 2 = InfixPlus InfixOne InfixTwo
mkInfixOpTreeSample n = InfixMulti (mkInfixOpTreeSample (n `div` 3)) (mkInfixOpTreeSample (n - (n `div` 3)))

mkPostfixOpTreeSample :: Int -> PostfixOpTree
mkPostfixOpTreeSample = treeTrans infixToPostfixTransducer . mkInfixOpTreeSample

main :: IO ()
main = do
  let !infixOpTreeSamples = force [ (c, mkInfixOpTreeSample c) | c <- [100, 500, 1000, 5000, 10000] ]
  let !postfixOpTreeSamples = force [ (c, mkPostfixOpTreeSample c) | c <- [100, 500, 1000, 5000, 10000] ]
  let !infixOpTreeSample = mkInfixOpTreeSample 10000
  let !compositedTransducer = identityTransducer `composeAtts` infixToPostfixTransducer
  defaultMain
    [ bgroup "att node counts"
      [ bench (show c) $ whnf (treeTrans infixToPostfixTransducer) t | (c, t) <- infixOpTreeSamples ]
    {-, bgroup "satt node counts"
      [ bench (show c) $ whnf (treeTrans postfixToInfixTransducer) t | (c, t) <- postfixOpTreeSamples ]-}
    , bgroup "compare compositions"
        [ bench "non-composition" $ whnf (treeTrans identityTransducer . treeTrans infixToPostfixTransducer) infixOpTreeSample
        , bench "composition" $ whnf (treeTrans compositedTransducer) infixOpTreeSample
        ]
    , bgroup "att-comp attribute counts"
        [ bench "id-itop" $ whnf (uncurry composeAtts) (identityTransducer, infixToPostfixTransducer)
        , bench "itop-exch" $ whnf (uncurry composeAtts) (infixToPostfixTransducer, orderExchangeTransducer)
        , bench "id-exch" $ whnf (uncurry composeAtts) (identityTransducer @InfixOpTree, identityTransducer)
        ]
    ]
