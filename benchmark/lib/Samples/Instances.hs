{-# OPTIONS_GHC -Wno-unused-matches #-}
{-# OPTIONS_GHC -Wno-unused-local-binds #-}

module Samples.Instances where

import           Prelude

import           Data.Stack
import           Samples.PostfixOpParser

{-# ANN module "HLint: ignore" #-}


depthRightSide :: InfixOpTree -> Int
depthRightSide = initial
  where
    initial u0 = f0 u0

    f0 (InfixPlusNode  u0 u1) = (+ 1) (f0 u1)
    f0 (InfixMultiNode u0 u1) = (+ 1) (f0 u1)
    f0 InfixOneNode           = (+ 1) 0
    f0 InfixTwoNode           = (+ 1) 0


flatRightSide :: InfixOpTree -> PostfixOpTree
flatRightSide = initial
  where
    initial u0 = f0 u0 PostfixEndNode

    f0 (InfixPlusNode  u0 u1) y0 = PostfixPlusNode  (f0 u1 (PostfixPlusNode y0))
    f0 (InfixMultiNode u0 u1) y0 = PostfixMultiNode (f0 u1 (PostfixMultiNode y0))
    f0 InfixOneNode           y0 = PostfixOneNode y0
    f0 InfixTwoNode           y0 = PostfixTwoNode y0


reversePop :: PostfixOpTree -> PostfixOpTree
reversePop = initial
  where
    initial u0 = f0 u0 PostfixEndNode

    f0 (PostfixPlusNode  u0) y0 = f0 u0 (PostfixPlusNode y0)
    f0 (PostfixMultiNode u0) y0 = f0 u0 (PostfixMultiNode y0)
    f0 (PostfixOneNode   u0) y0 = f0 u0 (PostfixOneNode y0)
    f0 (PostfixTwoNode   u0) y0 = f0 u0 (PostfixTwoNode y0)
    f0 PostfixEndNode        y0 = y0


itopReversePop :: InfixOpTree -> PostfixOpTree
itopReversePop = initial
  where
    initial u0 = f0_s_f0_s u0 u0_y0 u0_y1
      where
        u0_y0 = PostfixEndNode
        u0_y1 = f0_0_f0_0 u0 u0_y0 u0_y1

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
        (f0_0_f0_0 u1 u1_y0 u1_y1)
      where
        u0_y0 = y1
        u0_y1 = f0_s_f0_s u1 u1_y0 u1_y1

        u1_y0 = f0_0_f0_0 u0 u0_y0 u0_y1
        u1_y1 = y2
    f0_0_f0_0 (InfixPlusNode  u0 u1) y1 y2 = PostfixPlusNode
        (f0_0_f0_0 u1 u1_y0 u1_y1)
      where
        u0_y0 = y1
        u0_y1 = f0_s_f0_s u1 u1_y0 u1_y1

        u1_y0 = f0_0_f0_0 u0 u0_y0 u0_y1
        u1_y1 = y2
    f0_0_f0_0 InfixOneNode y1 y2 = PostfixOneNode y1
    f0_0_f0_0 InfixTwoNode y1 y2 = PostfixTwoNode y1


-- |
--
-- Original:
-- StackMacroTreeTransducer
--   { smttStates =
--     [ComposedSmttState f0 (0,(f0,0))
--     ,ComposedSmttState f0 ((),(f0,()))
--     ]
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
--     [ (ComposedSmttState f0 (0,(f0,0)),multi) -> Cons(multi(Head(ComposedSmttState f0 (0,(f0,0))(u1,Empty,ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,ComposedSmttState f0 ((),(f0,()))(u1,Empty,Empty,Cons(Head(y2), Empty))),Cons(Head(y2), Empty)))), Empty)
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


twoCounter :: InfixOpTree -> Int
twoCounter = initial
  where
    initial u0 = f0 u0 0

    f0 InfixOneNode  y0          = y0
    f0 InfixTwoNode  y0          = (+ 1) y0
    f0 (InfixPlusNode  u0 u1) y0 = f0 u0 (f0 u1 y0)
    f0 (InfixMultiNode u0 u1) y0 = f0 u0 (f0 u1 y0)

ptoiTwoCounter :: PostfixOpTree -> Int
ptoiTwoCounter = stackHead . initial
  where
    initial u0 = stackCons (stackHead (f0_s_f0_s u0 u0_y2)) stackEmpty
      where
        u0_y2 = stackEmpty

    f0_s_f0_s PostfixEndNode        y2 = y2
    f0_s_f0_s (PostfixMultiNode u0) y2 = f0_s_f0_s u0 u0_y2
      where
        u0_y2 = stackTail y2
    f0_s_f0_s (PostfixPlusNode  u0) y2 = f0_s_f0_s u0 u0_y2
      where
        u0_y2 = stackTail y2
    f0_s_f0_s (PostfixOneNode   u0) y2 = f0_s_f0_s u0 u0_y2
      where
        u0_y2 = stackCons (stackHead (f0_0_f0_0 u0 u0_y2)) y2
    f0_s_f0_s (PostfixTwoNode   u0) y2 = f0_s_f0_s u0 u0_y2
      where
        u0_y2 = stackCons ((+ 1) (stackHead (f0_0_f0_0 u0 u0_y2))) y2

    f0_0_f0_0 PostfixEndNode        y2 = stackCons 0 stackEmpty
    f0_0_f0_0 (PostfixMultiNode u0) y2 =
        stackCons (stackHead f0_0_f0_0_u0)
          (stackCons (stackHead y2)
            (stackTail f0_0_f0_0_u0)
          )
      where
        f0_0_f0_0_u0 = f0_0_f0_0 u0 u0_y2

        u0_y2 = stackTail y2
    f0_0_f0_0 (PostfixPlusNode  u0) y2 =
        stackCons (stackHead f0_0_f0_0_u0)
          (stackCons (stackHead y2)
            (stackTail f0_0_f0_0_u0)
          )
      where
        f0_0_f0_0_u0 = f0_0_f0_0 u0 u0_y2

        u0_y2 = stackTail y2
    f0_0_f0_0 (PostfixOneNode  u0) y2 = stackTail f0_0_f0_0_u0
      where
        f0_0_f0_0_u0 = f0_0_f0_0 u0 u0_y2

        u0_y2 = stackCons (stackHead f0_0_f0_0_u0) y2
    f0_0_f0_0 (PostfixTwoNode  u0) y2 = stackTail f0_0_f0_0_u0
      where
        f0_0_f0_0_u0 = f0_0_f0_0 u0 u0_y2

        u0_y2 = stackCons ((+ 1) (stackHead f0_0_f0_0_u0)) y2


-- |
-- StackMacroTreeTransducer
--   {smttStates =
--     [ComposedSmttState f0 (0,(f0,0))
--     ,ComposedSmttState f0 ((),(f0,()))
--     ]
--   ,smttInitialExpr = Cons(Head(ComposedSmttState f0 ((),(f0,()))(u0,Empty,Cons(False(), Empty),Empty)), Empty)
--   ,smttTransRules =
--     [ComposedSmttState f0 ((),(f0,())) (end) -> y2
--     ,ComposedSmttState f0 (0,(f0,0)) (end) -> y1
--     ,ComposedSmttState f0 ((),(f0,())) (multi) -> ComposedSmttState f0 ((),(f0,()))(u0,Empty,y1,Cons(Head(Tail(y2)), Tail(Tail(y2))))
--     ,ComposedSmttState f0 (0,(f0,0)) (multi) -> Cons(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(Head(Tail(y2)), Tail(Tail(y2))))), Cons(Head(y2), Tail(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(Head(Tail(y2)), Tail(Tail(y2)))))))
--     ,ComposedSmttState f0 ((),(f0,())) (one) -> ComposedSmttState f0 ((),(f0,()))(u0,Empty,y1,Cons(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Empty)), y2))), y2))),y2))
--     ,ComposedSmttState f0 (0,(f0,0)) (one) -> Tail(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(_|_, y2))), y2))), y2)))
--     ,ComposedSmttState f0 ((),(f0,())) (plus) -> ComposedSmttState f0 ((),(f0,()))(u0,Empty,y1,Cons(Head(Tail(y2)), Tail(Tail(y2))))
--     ,ComposedSmttState f0 (0,(f0,0)) (plus) -> Cons(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(Head(Tail(y2)), Tail(Tail(y2))))), Cons(Head(y2), Tail(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(Head(Tail(y2)), Tail(Tail(y2)))))))
--     ,ComposedSmttState f0 ((),(f0,())) (two) -> ComposedSmttState f0 ((),(f0,()))(u0,Empty,y1,Cons(True(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(True(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(True(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Empty))), y2)))), y2)))), y2))
--     ,ComposedSmttState f0 (0,(f0,0)) (two) -> Tail(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(True(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(True(Head(ComposedSmttState f0 (0,(f0,0))(u0,Empty,y1,Cons(True(_|_), y2)))), y2)))), y2)))
--     ]
--   }
ptoiTwocounterOrig :: PostfixOpTree -> Int
ptoiTwocounterOrig = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______000001 u0 stackEmpty (stackCons 0 stackEmpty) stackEmpty)) stackEmpty

    i__f0__0__f0_0____000000 PostfixEndNode y0 y1 y2 = y1

    i__f0__0__f0_0____000000 (PostfixMultiNode u0) y0 y1 y2 = stackCons (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackTail y2))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackTail y2))))

    i__f0__0__f0_0____000000 (PostfixOneNode u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackCons (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackCons (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackCons stackBottom y2))) y2))) y2))

    i__f0__0__f0_0____000000 (PostfixPlusNode u0) y0 y1 y2 = stackCons (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackTail y2))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackTail y2))))

    i__f0__0__f0_0____000000 (PostfixTwoNode u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackCons ((+ 1) (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackCons ((+ 1) (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackCons ((+ 1) stackBottom) y2)))) y2)))) y2))

    i__f0______f0_______000001 PostfixEndNode y0 y1 y2 = y2

    i__f0______f0_______000001 (PostfixMultiNode u0) y0 y1 y2 = i__f0______f0_______000001 u0 stackEmpty y1 (stackTail y2)

    i__f0______f0_______000001 (PostfixOneNode u0) y0 y1 y2 = i__f0______f0_______000001 u0 stackEmpty y1 (stackCons (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackCons (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackCons (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 stackEmpty)) y2))) y2))) y2)

    i__f0______f0_______000001 (PostfixPlusNode u0) y0 y1 y2 = i__f0______f0_______000001 u0 stackEmpty y1 (stackTail y2)

    i__f0______f0_______000001 (PostfixTwoNode u0) y0 y1 y2 = i__f0______f0_______000001 u0 stackEmpty y1 (stackCons ((+ 1) (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackCons ((+ 1) (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 (stackCons ((+ 1) (stackHead (i__f0__0__f0_0____000000 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)


ptoiItopWalk :: PostfixOpTree -> PostfixOpTree
ptoiItopWalk = stackHead . initial
  where
    initial u0 = stackCons (stackHead (f0_s_f0_s u0 [])) stackEmpty

    f0_s_f0_s t s = let s' = t:s in case t of
      PostfixEndNode      -> y2 s
      PostfixMultiNode u0 -> f0_s_f0_s u0 s'
      PostfixPlusNode  u0 -> f0_s_f0_s u0 s'
      PostfixOneNode   u0 -> f0_s_f0_s u0 s'
      PostfixTwoNode   u0 -> f0_s_f0_s u0 s'

    f0_0_f0_0 t s = let s' = t:s in case t of
      PostfixEndNode      -> y1 s
      PostfixMultiNode u0 ->
        let
          f0_0_f0_0_u0 = f0_0_f0_0 u0 s'
        in stackCons (PostfixMultiNode (stackHead f0_0_f0_0_u0))
          (stackCons (stackHead (y2 s))
            (stackTail f0_0_f0_0_u0))
      PostfixPlusNode u0 ->
        let
          f0_0_f0_0_u0 = f0_0_f0_0 u0 s'
        in stackCons (PostfixPlusNode (stackHead f0_0_f0_0_u0))
          (stackCons (stackHead (y2 s))
            (stackTail f0_0_f0_0_u0))
      PostfixOneNode   u0 -> stackTail (f0_0_f0_0 u0 s')
      PostfixTwoNode   u0 -> stackTail (f0_0_f0_0 u0 s')

    y1 []    = stackCons PostfixEndNode stackEmpty
    y1 (t:s) = case t of
      PostfixEndNode      -> stackEmpty
      PostfixMultiNode u0 -> y1 s
      PostfixPlusNode  u0 -> y1 s
      PostfixOneNode   u0 -> y1 s
      PostfixTwoNode   u0 -> y1 s

    y2 []       = stackEmpty
    y2 s'@(t:s) = case t of
      PostfixEndNode      -> stackEmpty
      PostfixMultiNode u0 -> stackTail (y2 s)
      PostfixPlusNode  u0 -> stackTail (y2 s)
      PostfixOneNode   u0 -> stackCons (PostfixOneNode (stackHead (f0_0_f0_0 u0 s'))) (y2 s)
      PostfixTwoNode   u0 -> stackCons (PostfixTwoNode (stackHead (f0_0_f0_0 u0 s'))) (y2 s)


ptoiItop :: PostfixOpTree -> PostfixOpTree
ptoiItop = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i_1 u0 stackEmpty)) stackEmpty

    i_0 PostfixEndNode y2 = stackCons (end) stackEmpty

    i_0 (PostfixMultiNode u0) y2 = stackCons (multi (stackHead i_0_u0)) (stackCons (stackHead y2) (stackTail i_0_u0))
      where
        i_0_u0 = i_0 u0 (stackTail y2)

    i_0 (PostfixOneNode u0) y2 = stackTail i_0_u0
      where
        i_0_u0 = i_0 u0 (stackCons (one (stackHead i_0_u0)) y2)

    i_0 (PostfixPlusNode u0) y2 = stackCons (plus (stackHead i_0_u0)) (stackCons (stackHead y2) (stackTail i_0_u0))
      where
        i_0_u0 = i_0 u0 (stackTail y2)

    i_0 (PostfixTwoNode u0) y2 = stackTail i_0_u0
      where
        i_0_u0 = i_0 u0 (stackCons (one (stackHead i_0_u0)) y2)

    i_1 PostfixEndNode y2 = y2

    i_1 (PostfixMultiNode u0) y2 = i_1 u0 (stackTail y2)

    i_1 (PostfixOneNode u0) y2 = i_1 u0 (stackCons (one (stackHead (i_0 u0 (stackCons (one (stackHead (i_0 u0 (stackCons (one (stackHead (i_0 u0 stackEmpty))) y2)))) y2)))) y2)

    i_1 (PostfixPlusNode u0) y2 = i_1 u0 (stackTail y2)

    i_1 (PostfixTwoNode u0) y2 = i_1 u0 (stackCons (two (stackHead (i_0 u0 (stackCons (two (stackHead (i_0 u0 (stackCons (two (stackHead (i_0 u0 stackEmpty))) y2)))) y2)))) y2)

    end = PostfixEndNode
    one = PostfixOneNode
    two = PostfixTwoNode
    plus = PostfixPlusNode
    multi = PostfixMultiNode

-- |
-- Original:
-- >>> putStrLn =<< encodeHaskellFromSmac "ptoiItopOrig" <$> composeSmttNCAndMttWSU postfixToInfixSmtt infixToPostfixMtt
-- ptoiItopOrig = stackHead . initial
--  where
--    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty (stackCons (end) stackEmpty) stackEmpty)) stackEmpty
--
--    i__f0__0__f0_0____0 (end) y0 y1 y2 = y1
--
--    i__f0__0__f0_0____0 (multi u0) y0 y1 y2 = stackCons (multi (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2)))) (stackCons (stackHead y2)(stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2))))
--
--    i__f0__0__f0_0____0 (one u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one stackBottom) y2)))) y2)))) y2))
--
--    i__f0__0__f0_0____0 (plus u0) y0 y1 y2 = stackCons (plus (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2)))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2))))
--
--    i__f0__0__f0_0____0 (two u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two stackBottom) y2)))) y2)))) y2))
--
--    i__f0______f0_______1 (end) y0 y1 y2 = y2
--
--    i__f0______f0_______1 (multi u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackTail y2)
--
--    i__f0______f0_______1 (one u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)
--
--    i__f0______f0_______1 (plus u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackTail y2)
--
--    i__f0______f0_______1 (two u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)
ptoiItopOrig :: PostfixOpTree -> PostfixOpTree
ptoiItopOrig = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty (stackCons (end) stackEmpty) stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 PostfixEndNode y0 y1 y2 = y1

    i__f0__0__f0_0____0 (PostfixMultiNode u0) y0 y1 y2 = stackCons (multi (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2)))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2))))

    i__f0__0__f0_0____0 (PostfixOneNode u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one stackBottom) y2)))) y2)))) y2))

    i__f0__0__f0_0____0 (PostfixPlusNode u0) y0 y1 y2 = stackCons (plus (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2)))) (stackCons (stackHead y2) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackTail y2))))

    i__f0__0__f0_0____0 (PostfixTwoNode u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two stackBottom) y2)))) y2)))) y2))

    i__f0______f0_______1 PostfixEndNode y0 y1 y2 = y2

    i__f0______f0_______1 (PostfixMultiNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackTail y2)

    i__f0______f0_______1 (PostfixOneNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)

    i__f0______f0_______1 (PostfixPlusNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackTail y2)

    i__f0______f0_______1 (PostfixTwoNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)

    end = PostfixEndNode
    one = PostfixOneNode
    two = PostfixTwoNode
    plus = PostfixPlusNode
    multi = PostfixMultiNode


ptoiDepth :: PostfixOpTree -> Int
ptoiDepth = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i_1 u0 stackEmpty)) stackEmpty

    i_1 PostfixEndNode y2 = y2

    i_1 (PostfixMultiNode u0) y2 = i_1 u0 (stackCons ((+ 1) (stackHead y2)) (stackTail (stackTail y2)))

    i_1 (PostfixOneNode u0) y2 = i_1 u0 (stackCons ((+ 1) 0) y2)

    i_1 (PostfixPlusNode u0) y2 = i_1 u0 (stackCons ((+ 1) (stackHead y2)) (stackTail (stackTail y2)))

    i_1 (PostfixTwoNode u0) y2 = i_1 u0 (stackCons ((+ 1) 0) y2)


-- |
--
-- >>> putStrLn =<< encodeHaskellFromSmac "ptoiDepth" <$> composeSmttNCAndMttWSU postfixToInfixSmtt (toMacroTreeTransducer depthRightSideTdtt)
-- ptoiDepth = stackHead . initial
--   where
--     initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty stackEmpty stackEmpty)) stackEmpty
--
--     i__f0__0__f0_0____0 (end) y0 y1 y2 = y1
--
--     i__f0__0__f0_0____0 (multi u0) y0 y1 y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (True (stackHead y2)) (stackTail (stackTail y2))))) (stackCons stackBottom (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (True (stackHead y2)) (stackTail (stackTail y2))))))
--
--     i__f0__0__f0_0____0 (one u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (True (False)) y2))
--
--     i__f0__0__f0_0____0 (plus u0) y0 y1 y2 = stackCons (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (True (stackHead y2)) (stackTail (stackTail y2))))) (stackCons stackBottom (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (True (stackHead y2)) (stackTail (stackTail y2))))))
--
--     i__f0__0__f0_0____0 (two u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (True (False)) y2))
--
--     i__f0______f0_______1 (end) y0 y1 y2 = y2
--
--     i__f0______f0_______1 (multi u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (True (stackHead y2)) (stackTail (stackTail y2)))
--
--     i__f0______f0_______1 (one u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (True (False)) y2)
--
--     i__f0______f0_______1 (plus u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (True (stackHead y2)) (stackTail (stackTail y2)))
--
--     i__f0______f0_______1 (two u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (True (False)) y2)
--
ptoiDepthOrig :: PostfixOpTree -> Int
ptoiDepthOrig = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty stackEmpty stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 PostfixEndNode y0 y1 y2 = y1

    i__f0__0__f0_0____0 (PostfixMultiNode u0) y0 y1 y2 = stackCons stackBottom (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons ((+ 1) (stackHead y2)) (stackTail (stackTail y2))))

    i__f0__0__f0_0____0 (PostfixOneNode u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons ((+ 1) 0) y2))

    i__f0__0__f0_0____0 (PostfixPlusNode u0) y0 y1 y2 = stackCons stackBottom (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons ((+ 1) (stackHead y2)) (stackTail (stackTail y2))))

    i__f0__0__f0_0____0 (PostfixTwoNode u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons ((+ 1) 0) y2))

    i__f0______f0_______1 PostfixEndNode y0 y1 y2 = y2

    i__f0______f0_______1 (PostfixMultiNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons ((+ 1) (stackHead y2)) (stackTail (stackTail y2)))

    i__f0______f0_______1 (PostfixOneNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons ((+ 1) 0) y2)

    i__f0______f0_______1 (PostfixPlusNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons ((+ 1) (stackHead y2)) (stackTail (stackTail y2)))

    i__f0______f0_______1 (PostfixTwoNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons ((+ 1) 0) y2)


ptoiFlat :: PostfixOpTree -> PostfixOpTree
ptoiFlat = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i_1 u0 stackEmpty)) stackEmpty

    i_0 PostfixEndNode y2 = stackCons PostfixEndNode stackEmpty

    i_0 (PostfixMultiNode u0) y2 = stackCons stackBottom (stackCons (PostfixMultiNode (stackHead (i_0 u0 (stackCons (PostfixMultiNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))))) (stackTail (i_0 u0 (stackCons (PostfixMultiNode (stackHead (stackTail y2))) (stackTail (stackTail y2))))))

    i_0 (PostfixOneNode u0) y2 = stackTail (i_0 u0 (stackCons (PostfixOneNode (stackHead (i_0 u0 (stackCons (PostfixOneNode (stackHead (i_0 u0 (stackCons stackBottom y2)))) y2)))) y2))

    i_0 (PostfixPlusNode u0) y2 = stackCons stackBottom (stackCons (PostfixPlusNode (stackHead (i_0 u0 (stackCons (PostfixPlusNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))))) (stackTail (i_0 u0 (stackCons (PostfixPlusNode (stackHead (stackTail y2))) (stackTail (stackTail y2))))))

    i_0 (PostfixTwoNode u0) y2 = stackTail (i_0 u0 (stackCons (PostfixTwoNode (stackHead (i_0 u0 (stackCons (PostfixTwoNode (stackHead (i_0 u0 (stackCons stackBottom y2)))) y2)))) y2))

    i_1 PostfixEndNode y2 = y2

    i_1 (PostfixMultiNode u0) y2 = i_1 u0 (stackCons (PostfixMultiNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i_1 (PostfixOneNode u0) y2 = i_1 u0 (stackCons (PostfixOneNode (stackHead (i_0 u0 (stackCons (PostfixOneNode (stackHead (i_0 u0 (stackCons (PostfixOneNode (stackHead (i_0 u0 stackEmpty))) y2)))) y2)))) y2)

    i_1 (PostfixPlusNode u0) y2 = i_1 u0 (stackCons (PostfixPlusNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i_1 (PostfixTwoNode u0) y2 = i_1 u0 (stackCons (PostfixTwoNode (stackHead (i_0 u0 (stackCons (PostfixTwoNode (stackHead (i_0 u0 (stackCons (PostfixTwoNode (stackHead (i_0 u0 stackEmpty))) y2)))) y2)))) y2)


ptoiFlat2 :: PostfixOpTree -> PostfixOpTree
ptoiFlat2 = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i_1 u0 stackEmpty)) stackEmpty

    i_0 PostfixEndNode y2 = stackCons PostfixEndNode stackEmpty

    i_0 (PostfixMultiNode u0) y2 = stackCons stackBottom (stackCons (PostfixMultiNode (stackHead (i_0 u0 (stackCons (PostfixMultiNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))))) (stackTail (i_0 u0 (stackCons (PostfixMultiNode (stackHead (stackTail y2))) (stackTail (stackTail y2))))))

    i_0 (PostfixOneNode u0) y2 = stackTail i_0_u0
      where
        i_0_u0 = i_0 u0 (stackCons (PostfixOneNode (stackHead i_0_u0)) y2)

    i_0 (PostfixPlusNode u0) y2 = stackCons stackBottom (stackCons (PostfixPlusNode (stackHead (i_0 u0 (stackCons (PostfixPlusNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))))) (stackTail (i_0 u0 (stackCons (PostfixPlusNode (stackHead (stackTail y2))) (stackTail (stackTail y2))))))

    i_0 (PostfixTwoNode u0) y2 = stackTail i_0_u0
      where
        i_0_u0 = i_0 u0 (stackCons (PostfixTwoNode (stackHead i_0_u0)) y2)

    i_1 PostfixEndNode y2 = y2

    i_1 (PostfixMultiNode u0) y2 = i_1 u0 (stackCons (PostfixMultiNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i_1 (PostfixOneNode u0) y2 = i_1 u0 (stackCons (PostfixOneNode (stackHead i_0_u0)) y2)
      where
        i_0_u0 = i_0 u0 (stackCons (PostfixOneNode (stackHead i_0_u0)) y2)

    i_1 (PostfixPlusNode u0) y2 = i_1 u0 (stackCons (PostfixPlusNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i_1 (PostfixTwoNode u0) y2 = i_1 u0 (stackCons (PostfixTwoNode (stackHead i_0_u0)) y2)
      where
        i_0_u0 = i_0 u0 (stackCons (PostfixTwoNode (stackHead i_0_u0)) y2)


-- |
-- >>> putStrLn =<< encodeHaskellFromSmac "ptoiFlatOrig" <$> composeSmttNCAndMttWSU postfixToInfixSmtt flatRightSideMtt
-- ptoiFlatOrig = stackHead . initial
--   where
--     initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty (stackCons (end) stackEmpty) stackEmpty)) stackEmpty
--
--     i__f0__0__f0_0____0 (end) y0 y1 y2 = y1
--
--     i__f0__0__f0_0____0 (multi u0) y0 y1 y2 = stackCons stackBottom (stackCons (multi (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (multi (stackHead (stackTail y2))) (stackTail (stackTail y2)))))) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (multi (stackHead (stackTail y2))) (stackTail (stackTail y2))))))
--
--     i__f0__0__f0_0____0 (one u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one stackBottom) y2)))) y2)))) y2))
--
--     i__f0__0__f0_0____0 (plus u0) y0 y1 y2 = stackCons stackBottom (stackCons (plus (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (plus (stackHead (stackTail y2))) (stackTail (stackTail y2)))))) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (plus (stackHead (stackTail y2))) (stackTail (stackTail y2))))))
--
--     i__f0__0__f0_0____0 (two u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two stackBottom) y2)))) y2)))) y2))
--
--     i__f0______f0_______1 (end) y0 y1 y2 = y2
--
--     i__f0______f0_______1 (multi u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (multi (stackHead (stackTail y2))) (stackTail (stackTail y2)))
--
--     i__f0______f0_______1 (one u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (one (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)
--
--     i__f0______f0_______1 (plus u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (plus (stackHead (stackTail y2))) (stackTail (stackTail y2)))
--
--     i__f0______f0_______1 (two u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (two (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)
ptoiFlatOrig :: PostfixOpTree -> PostfixOpTree
ptoiFlatOrig = stackHead . initial
  where
    initial u0 = stackCons (stackHead (i__f0______f0_______1 u0 stackEmpty (stackCons PostfixEndNode stackEmpty) stackEmpty)) stackEmpty

    i__f0__0__f0_0____0 PostfixEndNode y0 y1 y2 = y1

    i__f0__0__f0_0____0 (PostfixMultiNode u0) y0 y1 y2 = stackCons stackBottom (stackCons (PostfixMultiNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixMultiNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))))) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixMultiNode (stackHead (stackTail y2))) (stackTail (stackTail y2))))))

    i__f0__0__f0_0____0 (PostfixOneNode u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixOneNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixOneNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixOneNode stackBottom) y2)))) y2)))) y2))

    i__f0__0__f0_0____0 (PostfixPlusNode u0) y0 y1 y2 = stackCons stackBottom (stackCons (PostfixPlusNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixPlusNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))))) (stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixPlusNode (stackHead (stackTail y2))) (stackTail (stackTail y2))))))

    i__f0__0__f0_0____0 (PostfixTwoNode u0) y0 y1 y2 = stackTail (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixTwoNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixTwoNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixTwoNode stackBottom) y2)))) y2)))) y2))

    i__f0______f0_______1 PostfixEndNode y0 y1 y2 = y2

    i__f0______f0_______1 (PostfixMultiNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (PostfixMultiNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0______f0_______1 (PostfixOneNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (PostfixOneNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixOneNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixOneNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)

    i__f0______f0_______1 (PostfixPlusNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (PostfixPlusNode (stackHead (stackTail y2))) (stackTail (stackTail y2)))

    i__f0______f0_______1 (PostfixTwoNode u0) y0 y1 y2 = i__f0______f0_______1 u0 stackEmpty y1 (stackCons (PostfixTwoNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixTwoNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 (stackCons (PostfixTwoNode (stackHead (i__f0__0__f0_0____0 u0 stackEmpty y1 stackEmpty))) y2)))) y2)))) y2)
