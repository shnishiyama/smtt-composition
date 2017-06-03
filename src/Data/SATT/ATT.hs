{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}

module Data.SATT.ATT where

import Data.SATT.Tree

data InputLabel l
  = InitialLabel
  | InputLabel l
  deriving (Show, Eq, Ord)

data RightHandSide syn inh l
  = SynAttrSide syn Int
  | InhAttrSide inh
  | LabelSide l [RightHandSide syn inh l]
  deriving (Show, Eq, Ord)

type InputLabelType t = InputLabel (LabelType t)

type SynthesizedRuleType syn inh ta tb =
  syn -> InputLabelType ta ->
    RightHandSide syn inh (LabelType tb)

type InheritedRuleType syn inh ta tb =
  inh -> Int -> InputLabelType ta ->
    RightHandSide syn inh (LabelType tb)

-- | Attributed Tree Transducer
data AttrTreeTrans syn inh ta tb = AttrTreeTrans
  { initialAttr     :: syn
  , synthesizedRule :: SynthesizedRuleType syn inh ta tb
  , inheritedRule   :: InheritedRuleType syn inh ta tb
  }

data ReductionStep syn inh ta
  = SynthesizedReductionStep syn (InputLabelType ta)
  | InheritedReductionStep inh Int (InputLabelType ta)

type ReductionSteps syn inh ta = [ReductionStep syn inh ta]

-- | TODO
reductionATT :: ta -> tb
reductionATT = undefined
