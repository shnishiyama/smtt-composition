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
  , unconsStackStkExpr

    -- stack expr either
  , StackExprEither
  , pattern ValuedExpr
  , pattern StackedExpr
  , isStackedExpr
  , isValuedExpr
  , BiStackExprFix
  , BiStackExprFixVal
  , BiStackExprFixStk
  , pattern BiFixValuedExpr
  , pattern BiFixStackedExpr
  , pattern BiFixVal
  , pattern BiFixStk
  ) where

import           SattPrelude

import           Data.Bifunctor.FixLR


data StackExprValF val stk
  = StackBottomF
  | StackHeadF stk
  deriving (Eq, Ord, Show, Generic)

instance (Hashable stk) => Hashable (StackExprValF val stk)

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

instance (Hashable val, Hashable stk) => Hashable (StackExprStkF val stk)

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

injectVal :: (StackExprValF :<<: valf)
  => StackExprValF (FixVal valf stkf) (FixStk valf stkf) -> FixVal valf stkf
injectVal = injectL

injectStk :: (StackExprStkF :<<: stkf)
  => StackExprStkF (FixVal valf stkf) (FixStk valf stkf) -> FixStk valf stkf
injectStk = injectR

projectVal :: (StackExprValF :<<: valf)
  => FixVal valf stkf -> Maybe (StackExprValF (FixVal valf stkf) (FixStk valf stkf))
projectVal = projectL

projectStk :: (StackExprStkF :<<: stkf)
  => FixStk valf stkf -> Maybe (StackExprStkF (FixVal valf stkf) (FixStk valf stkf))
projectStk = projectR

pattern FixVal :: valf (FixVal valf stkf) (FixStk valf stkf) -> FixVal valf stkf
pattern FixVal x = FixL x

{-# COMPLETE FixVal #-}

pattern FixStk :: stkf (FixVal valf stkf) (FixStk valf stkf) -> FixStk valf stkf
pattern FixStk x = FixR x

{-# COMPLETE FixStk #-}


pattern StackBottom :: (StackExprValF :<<: valf) => FixVal valf stkf
pattern StackBottom <- (projectVal -> Just StackBottomF)

stackBottom :: (StackExprValF :<<: valf) => FixVal valf stkf
stackBottom = injectVal StackBottomF

pattern StackHead :: (StackExprValF :<<: valf) => FixStk valf stkf -> FixVal valf stkf
pattern StackHead s <- (projectVal -> Just (StackHeadF s))

stackHead :: (StackExprValF :<<: valf) => FixStk valf stkf -> FixVal valf stkf
stackHead = injectVal . StackHeadF

pattern StackEmpty :: (StackExprStkF :<<: stkf) => FixStk valf stkf
pattern StackEmpty <- (projectStk -> Just StackEmptyF)

stackEmpty :: (StackExprStkF :<<: stkf) => FixStk valf stkf
stackEmpty = injectStk StackEmptyF

pattern StackTail :: (StackExprStkF :<<: stkf) => FixStk valf stkf -> FixStk valf stkf
pattern StackTail s <- (projectStk -> Just (StackTailF s))

stackTail :: (StackExprStkF :<<: stkf) => FixStk valf stkf -> FixStk valf stkf
stackTail = injectStk . StackTailF

pattern StackCons :: (StackExprStkF :<<: stkf) => FixVal valf stkf -> FixStk valf stkf -> FixStk valf stkf
pattern StackCons v s <- (projectStk -> Just (StackConsF v s))

stackCons :: (StackExprStkF :<<: stkf) => FixVal valf stkf -> FixStk valf stkf -> FixStk valf stkf
stackCons v s = injectStk $ StackConsF v s


-- | evaluate value expression
--
-- Examples:
-- >>> import qualified Text.Show as S
-- >>> data Proxy2 val stk = Proxy2
-- >>> :{
-- instance Show2 Proxy2 where
--   liftShowsPrec2 _ _ _ _ d Proxy2 = S.showParen (d > 10) $ S.showString "Proxy2"
-- :}
--
-- >>> instance Bifunctor Proxy2 where bimap _ _ Proxy2 = Proxy2
-- >>> :{
-- stkProxy2 :: BiStackExprFixStk (Proxy2 :+|+: StackExprValF) (Proxy2 :+|+: StackExprStkF)
-- stkProxy2 = BiInL Proxy2
-- :}
--
-- >>> evalStackValExpr $ stackHead $ stackTail $ FixStk stkProxy2
-- FixL (BiInR (StackHeadF (FixR (BiInR (StackTailF (FixR (BiInL (Proxy2))))))))
--
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
  StackTail t   -> case unconsStackStkExpr t of
    Left t'       -> Left $ stackTail t'
    Right (_, t') -> evalStackStkHeadExpr t'
  StackCons h t -> Right (evalStackValExpr h, t)
  _             -> Left s

unconsStackStkExpr :: StackConstraint valf stkf
  => FixStk valf stkf -> Either (FixStk valf stkf) (FixVal valf stkf, FixStk valf stkf)
unconsStackStkExpr s = case s of
  StackEmpty    -> Right (stackBottom, s)
  StackTail t   -> case unconsStackStkExpr t of
    Left t'       -> Left $ stackTail t'
    Right (_, t') -> unconsStackStkExpr t'
  StackCons h t -> Right (h, t)
  _             -> Left s

-- | evaluate stack expression
--
-- Examples:
-- >>> import qualified Text.Show as S
-- >>> data Proxy2 val stk = Proxy2
-- >>> :{
-- instance Show2 Proxy2 where
--   liftShowsPrec2 _ _ _ _ d Proxy2 = S.showParen (d > 10) $ S.showString "Proxy2"
-- :}
--
-- >>> instance Bifunctor Proxy2 where bimap _ _ Proxy2 = Proxy2
-- >>> :{
-- stkProxy2 :: BiStackExprFixStk (Proxy2 :+|+: StackExprValF) (Proxy2 :+|+: StackExprStkF)
-- stkProxy2 = BiInL Proxy2
-- :}
--
-- >>> evalStackStkExpr $ stackTail $ stackTail $ stackCons stackBottom $ FixStk stkProxy2
-- FixR (BiInR (StackTailF (FixR (BiInL (Proxy2)))))
--
evalStackStkExpr :: StackConstraint valf stkf => FixStk valf stkf -> FixStk valf stkf
evalStackStkExpr s = case s of
  StackEmpty    -> s
  StackTail t   -> case unconsStackStkExpr t of
    Left t'       -> stackTail $ evalStackStkExpr t'
    Right (_, t') -> evalStackStkExpr t'
  StackCons h t -> stackCons (evalStackValExpr h) (evalStackStkExpr t)
  FixStk s'     -> FixStk $ bimap evalStackValExpr evalStackStkExpr s'


type StackExprEither = Either

pattern ValuedExpr :: val -> StackExprEither val stk
pattern ValuedExpr x = Left x

pattern StackedExpr :: stk -> StackExprEither val stk
pattern StackedExpr x = Right x

{-# COMPLETE ValuedExpr, StackedExpr #-}

isValuedExpr :: StackExprEither val stk -> Bool
isValuedExpr = isLeft

isStackedExpr :: StackExprEither val stk -> Bool
isStackedExpr = isRight

type BiStackExprFix valf stkf = BiFix valf stkf

type BiStackExprFixVal valf stkf = valf (FixVal valf stkf) (FixStk valf stkf)
type BiStackExprFixStk valf stkf = stkf (FixVal valf stkf) (FixStk valf stkf)

pattern BiFixValuedExpr :: FixVal valf stkf -> BiStackExprFix valf stkf
pattern BiFixValuedExpr x = ValuedExpr x

pattern BiFixStackedExpr :: FixStk valf stkf -> BiStackExprFix valf stkf
pattern BiFixStackedExpr x = StackedExpr x

{-# COMPLETE BiFixValuedExpr, BiFixStackedExpr #-}

pattern BiFixVal :: BiStackExprFixVal valf stkf -> BiStackExprFix valf stkf
pattern BiFixVal x = BiFixL x

pattern BiFixStk :: BiStackExprFixStk valf stkf -> BiStackExprFix valf stkf
pattern BiFixStk x = BiFixR x

{-# COMPLETE BiFixVal, BiFixStk #-}
