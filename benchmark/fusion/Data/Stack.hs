module Data.Stack where

import           SattPrelude

newtype Stack a = Stack [a]
  deriving (Eq, Ord, Show, Generic)
  deriving newtype NFData

stackHead :: Stack a -> a
stackHead (Stack x) = case x of
  []  -> error "stack empty"
  h:_ -> h

stackTail :: Stack a -> Stack a
stackTail (Stack x) = Stack $ case x of
  []  -> []
  _:t -> t

stackCons :: a -> Stack a -> Stack a
stackCons v (Stack x) = Stack $ v:x

stackEmpty :: Stack a
stackEmpty = Stack []

stackBottom :: a
stackBottom = error "stack bottom"
