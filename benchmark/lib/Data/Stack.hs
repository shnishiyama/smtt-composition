{-# LANGUAGE DerivingStrategies #-}

module Data.Stack where

import           SattPrelude

newtype Stack a = Stack [a]
  deriving (Eq, Ord, Show, Generic)
  deriving newtype NFData

stackHead :: Stack a -> a
stackHead (Stack [])    = stackBottom
stackHead (Stack (h:_)) = h
{-# INLINE stackHead #-}

stackTail :: Stack a -> Stack a
stackTail s@(Stack [])  = s
stackTail (Stack (_:t)) = Stack t
{-# INLINE stackTail #-}

stackCons :: a -> Stack a -> Stack a
stackCons v (Stack x) = Stack $ v:x
{-# INLINE stackCons #-}

stackUncons :: Stack a -> (a, Stack a)
stackUncons s@(Stack [])  = (stackBottom, s)
stackUncons (Stack (h:t)) = (h, Stack t)
{-# INLINE stackUncons #-}

stackEmpty :: Stack a
stackEmpty = Stack []
{-# INLINE stackEmpty #-}

stackBottom :: a
stackBottom = error "stack bottom"
