module Samples.TermOpParser where

import           SmttPrelude

import           Data.Stack

{-# ANN module "HLint: ignore" #-}


data PTerm
  = PMult PTerm
  | PPlus PTerm
  | POne  PTerm
  | PTwo  PTerm
  | PEnd
  deriving (Eq, Ord, Show, Generic, NFData)

type PrefTerm = PTerm
type PostTerm = PTerm

data ITerm
  = IMult ITerm ITerm
  | IPlus ITerm ITerm
  | IOne
  | ITwo
  deriving (Eq, Ord, Show, Generic, NFData)


-- |
-- Original:
-- >>> putStrLn $ encodeHaskellFromSmtt "po2i" postfixToInfixSmtt
--
po2i :: PostTerm -> ITerm
po2i = stackHead . initial
  where
    initial u0 = i_f0_0 u0 stackEmpty

    i_f0_0 (PEnd) y0 = y0

    i_f0_0 (PMult u0) y0 = i_f0_0 u0 (stackCons (multi (stackHead (stackTail y0)) (stackHead y0)) (stackTail (stackTail y0)))

    i_f0_0 (POne u0) y0 = i_f0_0 u0 (stackCons (one) y0)

    i_f0_0 (PPlus u0) y0 = i_f0_0 u0 (stackCons (plus (stackHead (stackTail y0)) (stackHead y0)) (stackTail (stackTail y0)))

    i_f0_0 (PTwo u0) y0 = i_f0_0 u0 (stackCons (two) y0)

    one   = IOne
    two   = ITwo
    multi = IMult
    plus  = IPlus


-- |
-- Original:
-- >>> putStrLn $ encodeHaskellFromSmtt "pr2i" prefixToInfixSmtt
--
pr2i :: PrefTerm -> ITerm
pr2i = stackHead . initial
  where
    initial u0 = i_f0_0 u0

    i_f0_0 (PEnd) = stackEmpty

    i_f0_0 (PMult u0) = stackCons (multi (stackHead (i_f0_0 u0)) (stackHead (stackTail (i_f0_0 u0)))) (stackTail (stackTail (i_f0_0 u0)))

    i_f0_0 (POne u0) = stackCons (one) (i_f0_0 u0)

    i_f0_0 (PPlus u0) = stackCons (plus (stackHead (i_f0_0 u0)) (stackHead (stackTail (i_f0_0 u0)))) (stackTail (stackTail (i_f0_0 u0)))

    i_f0_0 (PTwo u0) = stackCons (two) (i_f0_0 u0)

    one   = IOne
    two   = ITwo
    multi = IMult
    plus  = IPlus


-- |
-- Original:
-- >>> putStrLn $ encodeHaskellFromMtt "i2po" infixToPostfixMtt
--
i2po :: ITerm -> PostTerm
i2po = initial
  where
    initial u0 = i_f0_0 u0 (end)

    i_f0_0 (IMult u0 u1) y0 = i_f0_0 u0 (i_f0_0 u1 (multi y0))

    i_f0_0 (IOne) y0 = one y0

    i_f0_0 (IPlus u0 u1) y0 = i_f0_0 u0 (i_f0_0 u1 (plus y0))

    i_f0_0 (ITwo) y0 = two y0

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


-- |
-- Original:
-- >>> putStrLn $ encodeHaskellFromMtt "i2pr" infixToPrefixMtt
--
i2pr :: ITerm -> PostTerm
i2pr = initial
  where
    initial u0 = i_f0_0 u0 (end)

    i_f0_0 (IMult u0 u1) y0 = multi (i_f0_0 u0 (i_f0_0 u1 y0))

    i_f0_0 (IOne) y0 = one y0

    i_f0_0 (IPlus u0 u1) y0 = plus (i_f0_0 u0 (i_f0_0 u1 y0))

    i_f0_0 (ITwo) y0 = two y0

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus
