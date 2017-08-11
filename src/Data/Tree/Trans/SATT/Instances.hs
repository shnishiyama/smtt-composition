{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.SATT.Instances where

-- instances

fromAttrTreeTrans :: ATT.AttrTreeTrans syn inh ta tb -> StackAttrTreeTrans syn inh EmptyType EmptyType ta tb
fromAttrTreeTrans trans = StackAttrTreeTrans
  { initialAttr           = ATT.initialAttr trans
  , outputSynthesizedRule = ouSynRule
  , outputInheritedRule   = ouInhRule
  , stackSynthesizedRule  = stSynRule
  , stackInheritedRule    = stInhRule
  }
  where
    toOutputAttr (ATT.SynAttrSide a i) = OutputSynAttrSide a i
    toOutputAttr (ATT.InhAttrSide a)   = OutputInhAttrSide a
    toOutputAttr (ATT.LabelSide l ts)  = LabelSide l $ toOutputAttr <$> ts

    ouSynRule a   l = toOutputAttr $ ATT.synthesizedRule trans a l
    ouInhRule a i l = toOutputAttr $ ATT.inheritedRule trans a i l

    stSynRule _   _ = error "not supported stack attributes"
    stInhRule _ _ _ = error "not supported stack attributes"


data StSynAttrUnit = StSynAttrUnit
  deriving (Eq, Ord, Enum, Bounded)

instance Universe StSynAttrUnit
instance Finite StSynAttrUnit

instance Show StSynAttrUnit where
  show _ = "s0"

data StInhAttrUnit = StInhAttrUnit
  deriving (Eq, Ord, Enum, Bounded)

instance Universe StInhAttrUnit
instance Finite StInhAttrUnit

instance Show StInhAttrUnit where
  show _ = "s1"

postfixToInfixTransducer :: StackAttrTreeTrans ATT.SynAttrUnit EmptyType EmptyType StInhAttrUnit PostfixOpTree InfixOpTree
postfixToInfixTransducer = StackAttrTreeTrans
  { initialAttr           = a0
  , outputSynthesizedRule = ouSynRule
  , outputInheritedRule   = ouInhRule
  , stackSynthesizedRule  = stSynRule
  , stackInheritedRule    = stInhRule
  }
  where
    a0 = ATT.SynAttrUnit
    s  = StInhAttrUnit

    one         = LabelSide "one"   []
    two         = LabelSide "two"   []
    plus  t1 t2 = LabelSide "plus"  [t1, t2]
    multi t1 t2 = LabelSide "multi" [t1, t2]

    ouSynRule _ InitialLabel              = OutputSynAttrSide a0 0
    ouSynRule _ (RankedTreeLabel "one")   = OutputSynAttrSide a0 0
    ouSynRule _ (RankedTreeLabel "two")   = OutputSynAttrSide a0 0
    ouSynRule _ (RankedTreeLabel "plus")  = OutputSynAttrSide a0 0
    ouSynRule _ (RankedTreeLabel "multi") = OutputSynAttrSide a0 0
    ouSynRule _ (RankedTreeLabel "$")     = StackHeadSide
      (StackInhAttrSide s)
    ouSynRule _ l                         = error $ "unsupported label: " <> show l

    ouInhRule _ i l = error $ "unsupported label: (" <> show i <> "," <> show l <> ")"

    stSynRule _ l = error $ "unsupported label: " <> show l

    stInhRule _ 0 InitialLabel              = StackEmptySide
    stInhRule _ 0 (RankedTreeLabel "one")   = StackConsSide one $ StackInhAttrSide s
    stInhRule _ 0 (RankedTreeLabel "two")   = StackConsSide two $ StackInhAttrSide s
    stInhRule _ 0 (RankedTreeLabel "plus")  = StackConsSide
      (plus
        (StackHeadSide (StackTailSide (StackInhAttrSide s)))
        (StackHeadSide (StackInhAttrSide s)))
      (StackTailSide
        (StackTailSide (StackInhAttrSide s)))
    stInhRule _ 0 (RankedTreeLabel "multi") = StackConsSide
      (multi
        (StackHeadSide (StackTailSide (StackInhAttrSide s)))
        (StackHeadSide (StackInhAttrSide s)))
      (StackTailSide
        (StackTailSide (StackInhAttrSide s)))
    stInhRule _ i l                         = error $ "unsupported label: (" <> show i <> "," <> show l <> ")"
