{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.SATT.ATT where

import Data.TFFoldable
import Data.Tree.RankedTree
import Data.Tree.Transducer

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

data ReductionState syn inh l
  = SynAttrState syn [Int]
  | InhAddrState inh [Int]
  | LabelState l [ReductionState syn inh l]
  deriving (Show, Eq, Ord)

data ReductionStep syn inh ta
  = SynthesizedReductionStep syn (InputLabelType ta)
  | InheritedReductionStep inh Int (InputLabelType ta)

type ReductionSteps syn inh ta = [ReductionStep syn inh ta]

-- | TODO
buildAttReduction :: forall b s syn inh ta tb. RankedTree ta =>
  (b -> s -> ReductionStep syn inh ta -> b) -> b -> AttrTreeTrans syn inh ta tb -> ta -> b
buildAttReduction _f _s _trans t = tfFoldl go undefined t' where
  t' :: RankedTreeWrapper ta
  t' = RankedTreeWrapper t

  go :: b -> l -> b
  go = undefined

buildAttReductionSteps :: RankedTree ta =>
  AttrTreeTrans syn inh ta tb -> ta -> ReductionSteps syn inh ta
buildAttReductionSteps trans t = reverse $ buildAttReduction builder [] trans t where
  builder steps _ step = step : steps

runAttReduction :: (RankedTree ta, RankedTree tb) =>
  AttrTreeTrans syn inh ta tb -> ta -> tb
runAttReduction trans t = go $ builder trans t where
  builder = buildAttReduction (\_ s _ -> s) $ error "not excepted operation"

  go = undefined

instance TreeTransducer (AttrTreeTrans syn inh) where
  treeTrans = runAttReduction
