{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}

module Samples.Fusions where

import           Prelude

import           Data.Stack
import           Samples.TermOpParser

{-# ANN module "HLint: ignore" #-}


i2poRev :: ITerm -> PostTerm
i2poRev = initial
  where
    initial u0 = i__f0______f0_______1 u0 (end) u0_y2
      where
        u0_y2 = i__f0__0__f0_0____0 u0 (end) u0_y2

    i__f0__0__f0_0____0 (IMult u0 u1) y1 y2 = multi (i__f0__0__f0_0____0 u1 u1_y1 y2)
      where
        u1_y1 = i__f0__0__f0_0____0 u0 y1 u0_y2
        u0_y2 = i__f0__0__f0_0____0 u1 u1_y1 y2

    i__f0__0__f0_0____0 (IOne) y1 y2 = one y1

    i__f0__0__f0_0____0 (IPlus u0 u1) y1 y2 = plus (i__f0__0__f0_0____0 u1 u1_y1 y2)
      where
        u1_y1 = i__f0__0__f0_0____0 u0 y1 u0_y2
        u0_y2 = i__f0__0__f0_0____0 u1 u1_y1 y2

    i__f0__0__f0_0____0 (ITwo) y1 y2 = two y1

    i__f0______f0_______1 (IMult u0 u1) y1 y2 = i__f0______f0_______1 u0 y1 u0_y2
      where
        u0_y2 = i__f0______f0_______1 u1 u1_y1 y2
        u1_y1 = i__f0______f0_______1 u0 y1 u0_y2

    i__f0______f0_______1 (IOne) y1 y2 = y2

    i__f0______f0_______1 (IPlus u0 u1) y1 y2 = i__f0______f0_______1 u0 y1 u0_y2
      where
        u0_y2 = i__f0______f0_______1 u1 u1_y1 y2
        u1_y1 = i__f0______f0_______1 u0 y1 u0_y2

    i__f0______f0_______1 (ITwo) y1 y2 = y2

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


-- |
--
-- Original:
-- >>> putStrLn =<< encodeHaskellFromSmtt "i2poRevOrig" <$> composeSmttNCAndMttWSU (SMAC.toStackMacroTreeTransducer infixToPostfixMtt) reverseMtt
--
i2poRevOrig :: ITerm -> PostTerm
i2poRevOrig = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty (stackCons (end) stackEmpty) (stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty (stackCons (end) stackEmpty) (stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty (stackCons (end) stackEmpty) stackEmpty)) stackEmpty))) stackEmpty))) stackEmpty

    i__f0__0__f0_0____0 (IMult u0 u1) y0 y1 y2 = stackCons (multi (stackHead (i__f0__0__f0_0____0 u1 stackEmpty (i__f0__0__f0_0____0 u0 stackEmpty y1 (i__f0______f0_______1 u1 stackEmpty (i__f0__0__f0_0____0 u0 stackEmpty y1 (i__f0______f0_______1 u1 stackEmpty stackEmpty (stackCons (stackHead y2) stackEmpty))) (stackCons (stackHead y2) stackEmpty))) (stackCons (stackHead y2) stackEmpty)))) stackEmpty

    i__f0__0__f0_0____0 (IOne) y0 y1 y2 = stackCons (one (stackHead y1)) stackEmpty

    i__f0__0__f0_0____0 (IPlus u0 u1) y0 y1 y2 = stackCons (plus (stackHead (i__f0__0__f0_0____0 u1 stackEmpty (i__f0__0__f0_0____0 u0 stackEmpty y1 (i__f0______f0_______1 u1 stackEmpty (i__f0__0__f0_0____0 u0 stackEmpty y1 (i__f0______f0_______1 u1 stackEmpty stackEmpty (stackCons (stackHead y2) stackEmpty))) (stackCons (stackHead y2) stackEmpty))) (stackCons (stackHead y2) stackEmpty)))) stackEmpty

    i__f0__0__f0_0____0 (ITwo) y0 y1 y2 = stackCons (two (stackHead y1)) stackEmpty

    i__f0______f0_______1 (IMult u0 u1) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (i__f0______f0_______1 u1 stackEmpty (i__f0__0__f0_0____0 u0 stackEmpty y1 (i__f0______f0_______1 u1 stackEmpty (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty) (stackCons (stackHead y2) stackEmpty))) (stackCons (stackHead y2) stackEmpty))

    i__f0______f0_______1 (IOne) y0 y1 y2 = stackCons (stackHead y2) stackEmpty

    i__f0______f0_______1 (IPlus u0 u1) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (i__f0______f0_______1 u1 stackEmpty (i__f0__0__f0_0____0 u0 stackEmpty y1 (i__f0______f0_______1 u1 stackEmpty (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty) (stackCons (stackHead y2) stackEmpty))) (stackCons (stackHead y2) stackEmpty))

    i__f0______f0_______1 (ITwo) y0 y1 y2 = stackCons (stackHead y2) stackEmpty

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


po2iTwocounter :: PostTerm -> Int
po2iTwocounter = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 (PEnd) y2 = stackCons (zero) stackEmpty

    i__f0__0__f0_0____0 (PMult u0) y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 (stackTail y2))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____0 u0 (stackTail y2))))

    i__f0__0__f0_0____0 (POne u0) y2 = stackTail (i__f0__0__f0_0____0 u0 (stackCons (stackHead (i__f0__0__f0_0____0 u0 (stackCons(stackHead (i__f0__0__f0_0____0 u0 (stackCons stackBottom y2))) y2))) y2))

    i__f0__0__f0_0____0 (PPlus u0) y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 (stackTail y2))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____0 u0 (stackTail y2))))

    i__f0__0__f0_0____0 (PTwo u0) y2 = stackTail (i__f0__0__f0_0____0 u0 (stackCons (succ (stackHead (i__f0__0__f0_0____0 u0 (stackCons (succ (stackHead (i__f0__0__f0_0____0 u0 (stackCons (succ stackBottom) y2)))) y2)))) y2))

    i__f0______f0_______1 (PEnd) y2 = y2

    i__f0______f0_______1 (PMult u0) y2 = i__f0______f0_______1 u0 (stackTail y2)

    i__f0______f0_______1 (POne u0) y2 = i__f0______f0_______1 u0 (stackCons (stackHead (i__f0__0__f0_0____0 u0 (stackCons (stackHead (i__f0__0__f0_0____0 u0 (stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty)) y2))) y2))) y2)

    i__f0______f0_______1 (PPlus u0) y2 = i__f0______f0_______1 u0 (stackTail y2)

    i__f0______f0_______1 (PTwo u0) y2 = i__f0______f0_______1 u0 (stackCons (succ (stackHead (i__f0__0__f0_0____0 u0 (stackCons (succ (stackHead (i__f0__0__f0_0____0 u0 (stackCons (succ (stackHead (i__f0__0__f0_0____0 u0 stackEmpty))) y2)))) y2)))) y2)

    succ = (+ 1)
    zero = 0


-- |
-- Original:
-- >>> putStrLn =<< encodeHaskellFromSmtt "po2iTwocounterOrig" <$> composeSmttNCAndMttWSU postfixToInfixSmtt twoCounterMtt
--
po2iTwocounterOrig :: PostTerm -> Int
po2iTwocounterOrig = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty (stackCons (zero) stackEmpty) stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 (PEnd) y0 y1 y2 = y1

    i__f0__0__f0_0____0 (PMult u0) y0 y1 y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2))))

    i__f0__0__f0_0____0 (POne u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons(stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons stackBottom y2))) y2))) y2))

    i__f0__0__f0_0____0 (PPlus u0) y0 y1 y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2))))

    i__f0__0__f0_0____0 (PTwo u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ stackBottom) y2)))) y2)))) y2))

    i__f0______f0_______1 (PEnd) y0 y1 y2 = y2

    i__f0______f0_______1 (PMult u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackTail y2)

    i__f0______f0_______1 (POne u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty)) y2))) y2))) y2)

    i__f0______f0_______1 (PPlus u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackTail y2)

    i__f0______f0_______1 (PTwo u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (succ (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)

    succ = (+ 1)
    zero = 0


pr2iI2pr :: PrefTerm -> PrefTerm
pr2iI2pr = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______0 u0 (stackCons (end) stackEmpty) stackEmpty)) stackEmpty

    i__f0______f0_______0 (PEnd) y1 y2 = stackEmpty

    i__f0______f0_______0 (PMult u0) y1 y2 = stackCons (multi (stackHead (i__f0______f0_______0 u0 (stackCons (stackHead (stackTail (i__f0______f0_______0 u0 (stackCons stackBottom (stackCons (stackHead y1) stackEmpty)) stackEmpty))) stackEmpty) stackEmpty))) (stackTail (stackTail (i__f0______f0_______0 u0 (stackCons stackBottom (stackCons stackBottom (stackTail y1))) stackEmpty)))

    i__f0______f0_______0 (POne u0) y1 y2 = stackCons (one (stackHead y1)) (i__f0______f0_______0 u0 (stackTail y1) stackEmpty)

    i__f0______f0_______0 (PPlus u0) y1 y2 = stackCons (plus (stackHead (i__f0______f0_______0 u0 (stackCons (stackHead (stackTail (i__f0______f0_______0 u0 (stackCons stackBottom (stackCons (stackHead y1) stackEmpty)) stackEmpty))) stackEmpty) stackEmpty))) (stackTail (stackTail (i__f0______f0_______0 u0 (stackCons stackBottom (stackCons stackBottom (stackTail y1))) stackEmpty)))

    i__f0______f0_______0 (PTwo u0) y1 y2 = stackCons (two (stackHead y1)) (i__f0______f0_______0 u0 (stackTail y1) stackEmpty)

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


-- |
-- Original:
-- >>> putStrLn =<< encodeHaskellFromSmtt "pr2iI2prOrig" <$> composeSmttNCAndMttWSU prefixToInfixSmtt infixToPrefixMtt
--
pr2iI2prOrig :: PrefTerm -> PrefTerm
pr2iI2prOrig = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______0 u0 (stackCons (end) stackEmpty) stackEmpty)) stackEmpty

    i__f0______f0_______0 (PEnd) y1 y2 = stackEmpty

    i__f0______f0_______0 (PMult u0) y1 y2 = stackCons (multi (stackHead (i__f0______f0_______0 u0 (stackCons (stackHead (stackTail (i__f0______f0_______0 u0 (stackCons stackBottom (stackCons (stackHead y1) stackEmpty)) stackEmpty))) stackEmpty) stackEmpty))) (stackTail (stackTail (i__f0______f0_______0 u0 (stackCons stackBottom (stackCons stackBottom (stackTail y1))) stackEmpty)))

    i__f0______f0_______0 (POne u0) y1 y2 = stackCons (one (stackHead y1)) (i__f0______f0_______0 u0 (stackTail y1) stackEmpty)

    i__f0______f0_______0 (PPlus u0) y1 y2 = stackCons (plus (stackHead (i__f0______f0_______0 u0 (stackCons (stackHead (stackTail (i__f0______f0_______0 u0 (stackCons stackBottom (stackCons (stackHead y1) stackEmpty)) stackEmpty))) stackEmpty) stackEmpty))) (stackTail (stackTail (i__f0______f0_______0 u0 (stackCons stackBottom (stackCons stackBottom (stackTail y1))) stackEmpty)))

    i__f0______f0_______0 (PTwo u0) y1 y2 = stackCons (two (stackHead y1)) (i__f0______f0_______0 u0 (stackTail y1) stackEmpty)

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


po2iI2prOpt :: PostTerm -> PrefTerm
po2iI2prOpt = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 (PEnd) y2 = stackCons (end) stackEmpty

    i__f0__0__f0_0____0 (PMult u0) y2 = stackCons (stackHead i_0_u0) (stackCons (stackHead y2) (stackTail i_0_u0))
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (multi (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0__0__f0_0____0 (POne u0) y2 = stackTail i_0_u0
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (one (stackHead i_0_u0)) y2)

    i__f0__0__f0_0____0 (PPlus u0) y2 = stackCons (stackHead i_0_u0) (stackCons (stackHead y2) (stackTail i_0_u0))
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (plus (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0__0__f0_0____0 (PTwo u0) y2 = stackTail i_0_u0
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (two (stackHead i_0_u0)) y2)

    i__f0______f0_______1 (PEnd) y2 = y2

    i__f0______f0_______1 (PMult u0) y2 = i__f0______f0_______1 u0 (stackCons (multi (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0______f0_______1 (POne u0) y2 = i_1_u0
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (one (stackHead i_0_u0)) y2)
        i_1_u0 = i__f0______f0_______1 u0 (stackCons (one (stackHead i_0_u0)) y2)

    i__f0______f0_______1 (PPlus u0) y2 = i__f0______f0_______1 u0 (stackCons (plus (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0______f0_______1 (PTwo u0) y2 = i_1_u0
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (two (stackHead i_0_u0)) y2)
        i_1_u0 = i__f0______f0_______1 u0 (stackCons (two (stackHead i_0_u0)) y2)

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


po2iI2pr :: PostTerm -> PrefTerm
po2iI2pr = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 (PEnd) y2 = stackCons (end) stackEmpty

    i__f0__0__f0_0____0 (PMult u0) y2 = stackCons (stackHead i_0_u0) (stackCons (stackHead y2) (stackTail i_0_u0))
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (multi (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0__0__f0_0____0 (POne u0) y2 = stackTail i_0_u0
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (one (stackHead i_0_u0)) y2)

    i__f0__0__f0_0____0 (PPlus u0) y2 = stackCons (stackHead i_0_u0) (stackCons (stackHead y2) (stackTail i_0_u0))
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (plus (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0__0__f0_0____0 (PTwo u0) y2 = stackTail i_0_u0
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (two (stackHead i_0_u0)) y2)

    i__f0______f0_______1 (PEnd) y2 = y2

    i__f0______f0_______1 (PMult u0) y2 = i__f0______f0_______1 u0 (stackCons (multi (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0______f0_______1 (POne u0) y2 = i_1_u0
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (one (stackHead i_0_u0)) y2)
        i_1_u0 = i__f0______f0_______1 u0 (stackCons (one (stackHead i_0_u0)) y2)

    i__f0______f0_______1 (PPlus u0) y2 = i__f0______f0_______1 u0 (stackCons (plus (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0______f0_______1 (PTwo u0) y2 = i_1_u0
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackCons (two (stackHead i_0_u0)) y2)
        i_1_u0 = i__f0______f0_______1 u0 (stackCons (two (stackHead i_0_u0)) y2)

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


-- |
-- Original:
-- >>> putStrLn =<< encodeHaskellFromSmtt "po2iI2prOrig" <$> composeSmttNCAndMttWSU postfixToInfixSmtt infixToPrefixMtt
--
po2iI2prOrig :: PostTerm -> PrefTerm
po2iI2prOrig = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty (stackCons (end) stackEmpty) stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 (PEnd) y0 y1 y2 = y1

    i__f0__0__f0_0____0 (PMult u0) y0 y1 y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (multi (stackHead (stackTail y2))) (stackTail (stackTail y2))))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (multi (stackHead (stackTail y2))) (stackTail (stackTail y2))))))

    i__f0__0__f0_0____0 (POne u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one stackBottom) y2)))) y2)))) y2))

    i__f0__0__f0_0____0 (PPlus u0) y0 y1 y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (plus (stackHead (stackTail y2))) (stackTail (stackTail y2))))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (plus (stackHead (stackTail y2))) (stackTail (stackTail y2))))))

    i__f0__0__f0_0____0 (PTwo u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two stackBottom) y2)))) y2)))) y2))

    i__f0______f0_______1 (PEnd) y0 y1 y2 = y2

    i__f0______f0_______1 (PMult u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (multi (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0______f0_______1 (POne u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)

    i__f0______f0_______1 (PPlus u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (plus (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0______f0_______1 (PTwo u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


po2iDepth :: PostTerm -> Int
po2iDepth = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 (PEnd) y2 = stackEmpty

    i__f0__0__f0_0____0 (PMult u0) y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2))))) (stackCons stackBottom (stackTail (i__f0__0__f0_0____0 u0 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2))))))

    i__f0__0__f0_0____0 (POne u0) y2 = stackTail (i__f0__0__f0_0____0 u0 (stackCons (succ (zero)) y2))

    i__f0__0__f0_0____0 (PPlus u0) y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2))))) (stackCons stackBottom (stackTail (i__f0__0__f0_0____0 u0 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2))))))

    i__f0__0__f0_0____0 (PTwo u0) y2 = stackTail (i__f0__0__f0_0____0 u0 (stackCons (succ (zero)) y2))

    i__f0______f0_______1 (PEnd) y2 = y2

    i__f0______f0_______1 (PMult u0) y2 = i__f0______f0_______1 u0 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2)))

    i__f0______f0_______1 (POne u0) y2 = i__f0______f0_______1 u0 (stackCons (succ (zero)) y2)

    i__f0______f0_______1 (PPlus u0) y2 = i__f0______f0_______1 u0 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2)))

    i__f0______f0_______1 (PTwo u0) y2 = i__f0______f0_______1 u0 (stackCons (succ (zero)) y2)

    succ = (+ 1)
    zero = 0


-- |
--
-- >>> putStrLn =<< encodeHaskellFromSmac "ptoiDepth" <$> composeSmttNCAndMttWSU postfixToInfixSmtt (toMacroTreeTransducer depthRightSideTdtt)
--
po2iDepthOrig :: PostTerm -> Int
po2iDepthOrig = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty stackEmpty stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 (PEnd) y0 y1 y2 = y1

    i__f0__0__f0_0____0 (PMult u0) y0 y1 y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2))))) (stackCons stackBottom (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2))))))

    i__f0__0__f0_0____0 (POne u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ (zero)) y2))

    i__f0__0__f0_0____0 (PPlus u0) y0 y1 y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2))))) (stackCons stackBottom (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2))))))

    i__f0__0__f0_0____0 (PTwo u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (succ (zero)) y2))

    i__f0______f0_______1 (PEnd) y0 y1 y2 = y2

    i__f0______f0_______1 (PMult u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2)))

    i__f0______f0_______1 (POne u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (succ (zero)) y2)

    i__f0______f0_______1 (PPlus u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (succ (stackHead y2)) (stackTail (stackTail y2)))

    i__f0______f0_______1 (PTwo u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (succ (zero)) y2)

    succ = (+ 1)
    zero = 0


po2iFlat :: PostTerm -> PostTerm
po2iFlat = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 (PEnd) y2 = stackCons (end) stackEmpty

    i__f0__0__f0_0____0 (PMult u0) y2 = stackCons stackBottom (stackCons (multi (stackHead i_0_u0)) (stackTail i_0_u0))
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackTail y2)

    i__f0__0__f0_0____0 (POne u0) y2 = stackTail (i__f0__0__f0_0____0 u0 u0_y2)
      where
        u0_y2 = stackCons (one (stackHead (i__f0__0__f0_0____0 u0 u0_y2))) y2

    i__f0__0__f0_0____0 (PPlus u0) y2 = stackCons stackBottom (stackCons (plus (stackHead i_0_u0)) (stackTail i_0_u0))
      where
        i_0_u0 = i__f0__0__f0_0____0 u0 (stackTail y2)

    i__f0__0__f0_0____0 (PTwo u0) y2 = stackTail (i__f0__0__f0_0____0 u0 u0_y2)
      where
        u0_y2 = stackCons (two (stackHead (i__f0__0__f0_0____0 u0 u0_y2))) y2

    i__f0______f0_______1 (PEnd) y2 = y2

    i__f0______f0_______1 (PMult u0) y2 = i__f0______f0_______1 u0 (stackTail y2)

    i__f0______f0_______1 (POne u0) y2 = i__f0______f0_______1 u0 u0_y2
      where
        u0_y2 = stackCons (one (stackHead (i__f0__0__f0_0____0 u0 u0_y2))) y2

    i__f0______f0_______1 (PPlus u0) y2 = i__f0______f0_______1 u0 (stackTail y2)

    i__f0______f0_______1 (PTwo u0) y2 = i__f0______f0_______1 u0 u0_y2
      where
        u0_y2 = stackCons (two (stackHead (i__f0__0__f0_0____0 u0 u0_y2))) y2

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus


-- |
-- >>> putStrLn =<< encodeHaskellFromSmtt "po2iFlatOrig" <$> composeSmttNCAndMttWSU postfixToInfixSmtt flatRightSideMtt
--
po2iFlatOrig :: PostTerm -> PostTerm
po2iFlatOrig = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty (stackCons (end) stackEmpty) stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 (PEnd) y0 y1 y2 = y1

    i__f0__0__f0_0____0 (PMult u0) y0 y1 y2 = stackCons stackBottom (stackCons (multi (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2)))) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2))))

    i__f0__0__f0_0____0 (POne u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one stackBottom) y2)))) y2)))) y2))

    i__f0__0__f0_0____0 (PPlus u0) y0 y1 y2 = stackCons stackBottom (stackCons (plus (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2)))) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2))))

    i__f0__0__f0_0____0 (PTwo u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two stackBottom) y2)))) y2)))) y2))

    i__f0______f0_______1 (PEnd) y0 y1 y2 = y2

    i__f0______f0_______1 (PMult u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackTail y2)

    i__f0______f0_______1 (POne u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)

    i__f0______f0_______1 (PPlus u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackTail y2)

    i__f0______f0_______1 (PTwo u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)

    end   = PEnd
    one   = POne
    two   = PTwo
    multi = PMult
    plus  = PPlus
