module Data.SATT.ATT where

import ClassyPrelude

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

type TreeReductionState syn inh t = ReductionState syn inh (LabelType t)

data ReductionStep syn inh l
  = SynReductionStep syn l
  | InhReductionStep inh Int l
  deriving (Show, Eq, Ord)

type ReductionSteps syn inh t = [ReductionStep syn inh t]

type TreeReductionStep syn inh t = ReductionStep syn inh (InputLabelType t)
type TreeReductionSteps syn inh t = [TreeReductionStep syn inh t]

data ReductionContext syn inh l a = ReductionContext
  { reductionState :: ReductionState syn inh l
  , reductionValue :: a
  } deriving (Show, Eq, Ord)

type TreeReductionContext syn inh t = ReductionContext syn inh (LabelType t)

-- | TODO
buildAttReduction :: forall b syn inh ta tb. RankedTree ta =>
  (b -> TreeReductionStep syn inh ta -> TreeReductionState syn inh tb -> b)
  -> b -> AttrTreeTrans syn inh ta tb -> ta -> b
buildAttReduction _f s AttrTreeTrans{..} _t = reductionValue $ go initCtx where
  initState = SynAttrState initialAttr []
  initCtx = ReductionContext initState s

  {-
  t' :: RankedTreeWrapper ta
  t' = RankedTreeWrapper t
  -}

  go :: ReductionContext syn inh tb b
    -> ReductionContext syn inh tb b
  go ctx = ctx

buildAttReductionSteps :: RankedTree ta =>
  AttrTreeTrans syn inh ta tb -> ta -> TreeReductionSteps syn inh ta
buildAttReductionSteps trans t = reverse $ buildAttReduction builder [] trans t where
  builder steps step = const $ step : steps

runAttReduction :: (RankedTree ta, RankedTree tb) =>
  AttrTreeTrans syn inh ta tb -> ta -> tb
runAttReduction trans t = go $ builder trans t where
  builder = buildAttReduction (\_ s _ -> s) $ error "not excepted operation"

  go = undefined

instance TreeTransducer (AttrTreeTrans syn inh) where
  treeTrans = runAttReduction
