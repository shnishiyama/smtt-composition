module Stack where

newtype Stack a = Stack [a]
  deriving (Eq, Ord, Show, Generic)

instance NFData a => NFData (Stack a)

headStack :: Stack a -> a
headStack (Stack x) = case x of
  []  -> error "stack empty"
  h:_ -> h

tailStack :: Stack a -> Stack a
tailStack (Stack x) = case x of
  []  -> []
  _:t -> t

consStack :: a -> Stack a -> Stack a
consStack v (Stack x) = Stack $ v:x

emptyStack :: Stack a
emptyStack = Stack []

bottomStack :: a
bottomStack = error "stack bottom"
