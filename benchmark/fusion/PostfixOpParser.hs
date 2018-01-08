module PostfixOpParser where

import Stack


data PostfixOpTree
  = PostfixMultiNode PostfixOpTree
  | PostfixPlusNode  PostfixOpTree
  | PostfixOneNode   PostfixOpTree
  | PostfixTwoNode   PostfixOpTree
  | PostfixEndNode
  deriving (Eq, Ord, Show, Generic)

instance NFData PostfixOpTree


data InfixOpTree
  = InfixMultiNode InfixOpTree InfixOpTree
  | InfixPlusNode  InfixOpTree InfixOpTree
  | InfixOneNode
  | InfixTwoNode
  deriving (Eq, Ord, Show, Generic)

instance NFData InfixOpTree


ptoi :: PostfixOpTree -> InfixOpTree
ptoi t = stackHead (f0 t emptyStack)
  where
    f0 (PostfixMultiNode u0) y0 = f0 u0
      (stackCons
        (InfixMultiNode
          (stackHead (stackTail y0))
          (stackHead y0)
        )
        (stackTail (stackTail y0))
      )
    f0 (PostfixPlusNode u0) y0 = f0 u0
      (stackCons
        (InfixPlusNode
          (stackHead (stackTail y0))
          (stackHead y0)
        )
        (stackTail (stackTail y0))
      )
    f0 (PostfixOneNode u0) y0 = f0 u0
      (stackCons InfixOneNode y0)
    f0 (PostfixTwoNode u0) y0 = f0 u0
      (stackCons InfixTwoNode y0)
    f0 PostfixEndNode      y0 = y0
