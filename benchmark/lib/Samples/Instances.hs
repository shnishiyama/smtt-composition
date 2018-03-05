{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Samples.Instances where

import           Prelude

import           Samples.TermOpParser

{-# ANN module "HLint: ignore" #-}


-- |
-- Original:
-- >>> putStrLn $ encodeHaskellFromMtt "depthRightSide" (TOP.toMacroTreeTransducer depthRightSideTdtt)
--
depthRightSide :: ITerm -> Int
depthRightSide = initial
  where
    initial u0 = i_f0_0 u0

    i_f0_0 (IMult u0 u1) = succ (i_f0_0 u1)

    i_f0_0 (IOne) = succ zero

    i_f0_0 (IPlus u0 u1) = succ (i_f0_0 u1)

    i_f0_0 (ITwo) = succ zero

    succ = (+ 1)
    zero = 0


-- |
-- Original:
-- >>> putStrLn $ encodeHaskellFromMtt "flatRightSide" flatRightSideMtt
--
flatRightSide :: ITerm -> PTerm
flatRightSide = initial
  where
    initial u0 = i_f0_0 u0 (end)

    i_f0_0 (IMult u0 u1) y0 = i_f0_0 u0 (multi y0)

    i_f0_0 (IOne) y0 = one y0

    i_f0_0 (IPlus u0 u1) y0 = i_f0_0 u0 (plus y0)

    i_f0_0 (ITwo) y0 = two y0

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


-- |
-- Original:
-- >>> putStrLn $ encodeHaskellFromMtt "flatRightSide" flatRightSideMtt
--
reversePop :: PostTerm -> PrefTerm
reversePop = initial
  where
    initial u0 = i_f0_0 u0 (end)

    i_f0_0 (PEnd) y0 = y0

    i_f0_0 (PMult u0) y0 = i_f0_0 u0 (multi y0)

    i_f0_0 (POne u0) y0 = i_f0_0 u0 (one y0)

    i_f0_0 (PPlus u0) y0 = i_f0_0 u0 (plus y0)

    i_f0_0 (PTwo u0) y0 = i_f0_0 u0 (two y0)

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


-- |
-- Original:
-- >>> putStrLn $ encodeHaskellFromMtt "twoCounter" twoCounterMtt
--
twoCounter :: ITerm -> Int
twoCounter = initial
  where
    initial u0 = i_f0_0 u0 (zero)

    i_f0_0 (IMult u0 u1) y0 = i_f0_0 u0 (i_f0_0 u1 y0)

    i_f0_0 (IOne) y0 = y0

    i_f0_0 (IPlus u0 u1) y0 = i_f0_0 u0 (i_f0_0 u1 y0)

    i_f0_0 (ITwo) y0 = succ y0

    succ = (+ 1)
    zero = 0
