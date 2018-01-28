module Samples.PostfixOpParser where

import           SattPrelude

import           Data.Stack


data PostfixOpTree
  = PostfixMultiNode PostfixOpTree
  | PostfixPlusNode  PostfixOpTree
  | PostfixOneNode   PostfixOpTree
  | PostfixTwoNode   PostfixOpTree
  | PostfixEndNode
  deriving (Eq, Ord, Show, Generic, NFData)


data InfixOpTree
  = InfixMultiNode InfixOpTree InfixOpTree
  | InfixPlusNode  InfixOpTree InfixOpTree
  | InfixOneNode
  | InfixTwoNode
  deriving (Eq, Ord, Show, Generic, NFData)


-- |
-- Original:
-- >>> putStrLn $ encodeHaskellFromSmac "ptoi" postfixToInfixSmtt
--
ptoi :: PostfixOpTree -> InfixOpTree
ptoi = stackHead . initial
  where
    initial u0 = i_f0_000000 u0 stackEmpty

    i_f0_000000 (PostfixPlusNode u0) y0 = i_f0_000000 u0
      (stackCons (InfixPlusNode (stackHead (stackTail y0)) (stackHead y0))
        (stackTail (stackTail y0)))

    i_f0_000000 (PostfixMultiNode u0) y0 = i_f0_000000 u0
      (stackCons (InfixMultiNode (stackHead (stackTail y0)) (stackHead y0))
        (stackTail (stackTail y0)))

    i_f0_000000 PostfixEndNode y0 = y0

    i_f0_000000 (PostfixTwoNode u0) y0 = i_f0_000000 u0 (stackCons InfixTwoNode y0)

    i_f0_000000 (PostfixOneNode u0) y0 = i_f0_000000 u0 (stackCons InfixOneNode y0)


itop :: InfixOpTree -> PostfixOpTree
itop t = f0 t PostfixEndNode
  where
    f0 InfixOneNode           y0 = PostfixOneNode y0
    f0 InfixTwoNode           y0 = PostfixTwoNode y0
    f0 (InfixMultiNode u0 u1) y0 = f0 u0 (f0 u1 (PostfixMultiNode y0))
    f0 (InfixPlusNode u0 u1)  y0 = f0 u0 (f0 u1 (PostfixPlusNode y0))
