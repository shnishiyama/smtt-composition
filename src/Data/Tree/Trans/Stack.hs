{-# LANGUAGE TemplateHaskell #-}

module Data.Tree.Trans.Stack
  ( -- common
    StackExprValF(..)
  , StackExprStkF(..)
  , StackConstraint
  , FixVal
  , pattern FixVal
  , FixStk
  , pattern FixStk
  , injectVal
  , injectStk
  , projectVal
  , projectStk
  , pattern StackBottom
  , stackBottom
  , pattern StackHead
  , stackHead
  , pattern StackEmpty
  , stackEmpty
  , pattern StackTail
  , stackTail
  , pattern StackCons
  , stackCons

    -- evaluate functions
  , evalStackValExpr
  , evalStackStkExpr
  ) where

import SattPrelude

import Data.Bifunctor.FixLR


data StackExprValF val stk
  = StackBottomF
  | StackHeadF stk
  deriving (Eq, Ord, Show, Generic)

deriveBifunctor ''StackExprValF
deriveBifoldable ''StackExprValF
deriveEq2 ''StackExprValF
deriveOrd2 ''StackExprValF
deriveShow2 ''StackExprValF

data StackExprStkF val stk
  = StackEmptyF
  | StackTailF stk
  | StackConsF val stk
  deriving (Eq, Ord, Show, Generic)

deriveBifunctor ''StackExprStkF
deriveBifoldable ''StackExprStkF
deriveEq2 ''StackExprStkF
deriveOrd2 ''StackExprStkF
deriveShow2 ''StackExprStkF


type StackConstraint valf stkf =
  ( StackExprValF :<<: valf, StackExprStkF :<<: stkf
  , Bifunctor valf, Bifunctor stkf
  )

type FixVal = FixL
type FixStk = FixR

injectVal :: StackExprValF :<<: valf
  => StackExprValF (FixVal valf stkf) (FixStk valf stkf) -> FixVal valf stkf
injectVal = injectL

injectStk :: StackExprStkF :<<: stkf
  => StackExprStkF (FixVal valf stkf) (FixStk valf stkf) -> FixStk valf stkf
injectStk = injectR

projectVal :: StackExprValF :<<: valf
  => FixVal valf stkf -> Maybe (StackExprValF (FixVal valf stkf) (FixStk valf stkf))
projectVal = projectL

projectStk :: StackExprStkF :<<: stkf
  => FixStk valf stkf -> Maybe (StackExprStkF (FixVal valf stkf) (FixStk valf stkf))
projectStk = projectR

pattern FixVal :: valf (FixVal valf stkf) (FixStk valf stkf) -> FixVal valf stkf
pattern FixVal x = FixL x

{-# COMPLETE FixVal #-}

pattern FixStk :: stkf (FixVal valf stkf) (FixStk valf stkf) -> FixStk valf stkf
pattern FixStk x = FixR x

{-# COMPLETE FixStk #-}


pattern StackBottom :: StackExprValF :<<: valf => FixVal valf stkf
pattern StackBottom <- (projectVal -> Just StackBottomF)

stackBottom :: StackExprValF :<<: valf => FixVal valf stkf
stackBottom = injectVal StackBottomF

pattern StackHead :: StackExprValF :<<: valf => FixStk valf stkf -> FixVal valf stkf
pattern StackHead s <- (projectVal -> Just (StackHeadF s))

stackHead :: StackExprValF :<<: valf => FixStk valf stkf -> FixVal valf stkf
stackHead = injectVal . StackHeadF

pattern StackEmpty :: StackExprStkF :<<: stkf => FixStk valf stkf
pattern StackEmpty <- (projectStk -> Just StackEmptyF)

stackEmpty :: StackExprStkF :<<: stkf => FixStk valf stkf
stackEmpty = injectStk StackEmptyF

pattern StackTail :: StackExprStkF :<<: stkf => FixStk valf stkf -> FixStk valf stkf
pattern StackTail s <- (projectStk -> Just (StackTailF s))

stackTail :: StackExprStkF :<<: stkf => FixStk valf stkf -> FixStk valf stkf
stackTail = injectStk . StackTailF

pattern StackCons :: StackExprStkF :<<: stkf => FixVal valf stkf -> FixStk valf stkf -> FixStk valf stkf
pattern StackCons v s <- (projectStk -> Just (StackConsF v s))

stackCons :: StackExprStkF :<<: stkf => FixVal valf stkf -> FixStk valf stkf -> FixStk valf stkf
stackCons v s = injectStk $ StackConsF v s


evalStackValExpr :: StackConstraint valf stkf => FixVal valf stkf -> FixVal valf stkf
evalStackValExpr v = case v of
  StackBottom -> v
  StackHead s -> case evalStackStkHeadExpr s of
    Left s'       -> stackHead $ evalStackStkExpr s'
    Right (h,  _) -> h
  FixVal v'   -> FixVal $ bimap evalStackValExpr evalStackStkExpr v'

evalStackStkHeadExpr :: StackConstraint valf stkf
  => FixStk valf stkf -> Either (FixStk valf stkf) (FixVal valf stkf, FixStk valf stkf)
evalStackStkHeadExpr s = case s of
  StackEmpty    -> Right (stackBottom, s)
  StackTail t   -> case evalStackStkUnconsExpr t of
    Left t'       -> Left t'
    Right (_, t') -> evalStackStkHeadExpr t'
  StackCons h t -> Right (evalStackValExpr h, t)
  _             -> Left s

evalStackStkUnconsExpr :: StackConstraint valf stkf
  => FixStk valf stkf -> Either (FixStk valf stkf) (FixVal valf stkf, FixStk valf stkf)
evalStackStkUnconsExpr s = case s of
  StackEmpty    -> Right (stackBottom, s)
  StackTail t   -> case evalStackStkUnconsExpr t of
    Left t'       -> Left $ stackTail t'
    Right (_, t') -> evalStackStkUnconsExpr t'
  StackCons h t -> Right (h, t)
  _             -> Left s

evalStackStkExpr :: StackConstraint valf stkf => FixStk valf stkf -> FixStk valf stkf
evalStackStkExpr s = case s of
  StackEmpty    -> s
  StackTail t   -> case evalStackStkUnconsExpr t of
    Left t'       -> stackTail $ evalStackStkExpr t'
    Right (_, t') -> evalStackStkExpr t'
  StackCons h t -> stackCons (evalStackValExpr h) (evalStackStkExpr t)
  FixStk s'     -> FixStk $ bimap evalStackValExpr evalStackStkExpr s'
