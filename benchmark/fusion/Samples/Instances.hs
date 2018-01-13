{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}
{-# ANN module "HLint: ignore" #-}

module Samples.Instances where

import           Prelude

import           Data.Stack
import           Samples.PostfixOpParser


reversePop :: PostfixOpTree -> PostfixOpTree
reversePop t = f0 t PostfixEndNode
  where
    f0 (PostfixPlusNode  u0) y0 = f0 u0 (PostfixPlusNode y0)
    f0 (PostfixMultiNode u0) y0 = f0 u0 (PostfixMultiNode y0)
    f0 (PostfixOneNode   u0) y0 = f0 u0 (PostfixOneNode y0)
    f0 (PostfixTwoNode   u0) y0 = f0 u0 (PostfixTwoNode y0)
    f0 PostfixEndNode        y0 = y0


itopReversePop :: InfixOpTree -> PostfixOpTree
itopReversePop = initial
  where
    initial u0 = f0_s_f0_s u0 PostfixEndNode (f0_0_f0_0 u0 PostfixEndNode undefined)

    f0_s_f0_s InfixOneNode y1 y2 = y2
    f0_s_f0_s InfixTwoNode y1 y2 = y2
    f0_s_f0_s (InfixPlusNode  u0 u1) y1 y2 = f0_s_f0_s u0 u0_y0 u0_y1
      where
        u0_y0 = y1
        u0_y1 = f0_s_f0_s u1 u1_y0 u1_y1

        u1_y0 = f0_0_f0_0 u0 u0_y1 u0_y1
        u1_y1 = y2
    f0_s_f0_s (InfixMultiNode u0 u1) y1 y2 = f0_s_f0_s u0 u0_y0 u0_y1
      where
        u0_y0 = y1
        u0_y1 = f0_s_f0_s u1 u1_y0 u1_y1

        u1_y0 = f0_0_f0_0 u0 u0_y1 u0_y1
        u1_y1 = y2

    f0_0_f0_0 (InfixMultiNode u0 u1) y1 y2 = PostfixMultiNode
      (f0_0_f0_0 u1
        (f0_0_f0_0 u0 y1 (f0_s_f0_s u1 undefined y2))
        y2)
    f0_0_f0_0 (InfixPlusNode  u0 u1) y1 y2 = PostfixPlusNode
      (f0_0_f0_0 u1
        (f0_0_f0_0 u0 y1 (f0_s_f0_s u1 undefined y2))
        y2)
    f0_0_f0_0 InfixOneNode y1 y2 = PostfixOneNode y1
    f0_0_f0_0 InfixTwoNode y1 y2 = PostfixTwoNode y1


-- |
--
-- Original:
-- StackMacroTreeTransducer
--   { smttStates = [ComposedSmttState f0 (0,(f0,0)),ComposedSmttState f0 ((),(f0,()))]
--   , smttInitialExpr = Cons
--     ( Head
--        ( ComposedSmttStatef0 ((),(f0,()))
--          ( u0
--          , Empty
--          , Cons(end(), Empty)
--          , Cons(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,Cons(end(), Empty),Empty)), Empty)
--          )
--        )
--     , Empty
--     )
--   , smttTransRules =
--     [ (ComposedSmttState f0 (1,(f0,0)),two) -> Empty
--     , (ComposedSmttState f0 (1,(f0,0)),one) -> Empty
--     , (ComposedSmttState f0 (1,(f0,0)),multi) -> Empty
--     , (ComposedSmttState f0 (1,(f0,0)),plus) -> Empty
--     , (ComposedSmttState f0 (0,(f0,0)),multi) -> Cons(multi(Head(ComposedSmttState f0 (0,(f0,0))(u1,Empty,ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,ComposedSmttState f0 ((),(f0,()))(u1,Empty,Empty,Cons(Head(y2), Empty))),Cons(Head(y2), Empty)))), Empty)
--     , (ComposedSmttState f0 (0,(f0,0)),plus) -> Cons(plus(Head(ComposedSmttState f0 (0,(f0,0))(u1,Empty,ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,ComposedSmttState f0 ((),(f0,()))(u1,Empty,Empty,Cons(Head(y2), Empty))),Cons(Head(y2), Empty)))), Empty)
--     , (ComposedSmttState f0 (0,(f0,0)),one) -> Cons(one(Head(y1)), Empty)
--     , (ComposedSmttState f0 (0,(f0,0)),two) -> Cons(two(Head(y1)), Empty)
--     , (ComposedSmttState f0 ((),(f0,())),one) -> Cons(Head(y2), Empty)
--     , (ComposedSmttState f0 ((),(f0,())),plus) -> ComposedSmttState f0 ((),(f0,()))(u0,Empty,y1,ComposedSmttState f0 ((),(f0,()))(u1,Empty,ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Empty),Cons(Head(y2), Empty)))
--     , (ComposedSmttState f0 ((),(f0,())),two) -> Cons(Head(y2), Empty)
--     , (ComposedSmttState f0 ((),(f0,())),multi) -> ComposedSmttState f0 ((),(f0,()))(u0,Empty,y1,ComposedSmttState f0 ((),(f0,()))(u1,Empty,ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Empty),Cons(Head(y2), Empty)))
--     ]
--   , }
itopReversePopOrig :: InfixOpTree -> PostfixOpTree
itopReversePopOrig = stackHead . initial
  where
    initial u0 = stackCons
      (stackHead
        (f0_s_f0_s
          u0
          stackEmpty
          (stackCons PostfixEndNode stackEmpty)
          (stackCons (stackHead (f0_0_f0_0 u0 stackEmpty (stackCons PostfixEndNode stackEmpty) stackEmpty)) stackEmpty)
        )
      )
      stackEmpty

    f0_1_f0_0 InfixOneNode           y0 y1 y2 = stackEmpty
    f0_1_f0_0 InfixTwoNode           y0 y1 y2 = stackEmpty
    f0_1_f0_0 (InfixPlusNode  u0 u1) y0 y1 y2 = stackEmpty
    f0_1_f0_0 (InfixMultiNode u0 u1) y0 y1 y2 = stackEmpty

    f0_0_f0_0 InfixOneNode           y0 y1 y2 = stackCons (PostfixOneNode (stackHead y1)) stackEmpty
    f0_0_f0_0 InfixTwoNode           y0 y1 y2 = stackCons (PostfixTwoNode (stackHead y1)) stackEmpty
    f0_0_f0_0 (InfixMultiNode u0 u1) y0 y1 y2 = stackCons
      (PostfixMultiNode (stackHead (f0_0_f0_0
        u1
        stackEmpty
        (f0_0_f0_0 u0 stackEmpty y1
          (f0_s_f0_s u1 stackEmpty stackEmpty (stackCons (stackHead y2) stackEmpty))
        )
        (stackCons (stackHead y2) stackEmpty)
      )))
      stackEmpty
    f0_0_f0_0 (InfixPlusNode u0 u1) y0 y1 y2 = stackCons
      (PostfixPlusNode (stackHead (f0_0_f0_0
        u1
        stackEmpty
        (f0_0_f0_0 u0 stackEmpty y1
          (f0_s_f0_s u1 stackEmpty stackEmpty (stackCons (stackHead y2) stackEmpty))
        )
        (stackCons (stackHead y2) stackEmpty)
      )))
      stackEmpty

    f0_s_f0_s InfixOneNode           y0 y1 y2 = stackCons (stackHead y2) stackEmpty
    f0_s_f0_s InfixTwoNode           y0 y1 y2 = stackCons (stackHead y2) stackEmpty
    f0_s_f0_s (InfixPlusNode  u0 u1) y0 y1 y2 = f0_s_f0_s u0 stackEmpty y1
      (f0_s_f0_s u1 stackEmpty (f0_0_f0_0 u0 stackEmpty y1 stackEmpty) (stackCons (stackHead y2) stackEmpty))
    f0_s_f0_s (InfixMultiNode u0 u1) y0 y1 y2 = f0_s_f0_s u0 stackEmpty y1
      (f0_s_f0_s u1 stackEmpty (f0_0_f0_0 u0 stackEmpty y1 stackEmpty) (stackCons (stackHead y2) stackEmpty))
