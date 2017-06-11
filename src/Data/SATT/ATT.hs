{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

{-# LANGUAGE FlexibleInstances #-}

module Data.SATT.ATT where

import ClassyPrelude

import Data.Proxy

import Data.Tree.RankedTree
import Data.Tree.RankedTree.Zipper
import Data.Tree.Transducer


-- common

data InputLabel l
  = InitialLabel
  | InputLabel l
  deriving (Show, Eq, Ord)

type InputLabelType t = InputLabel (LabelType t)

data RightHandSide syn inh l
  = SynAttrSide syn Int
  | InhAttrSide inh
  | LabelSide l [RightHandSide syn inh l]
  deriving (Show, Eq, Ord)

type TreeRightHandSide syn inh t = RightHandSide syn inh (LabelType t)

type SynthesizedRuleType syn inh ta tb =
  syn -> InputLabelType ta ->
    TreeRightHandSide syn inh tb

type InheritedRuleType syn inh ta tb =
  inh -> Int -> InputLabelType ta ->
    TreeRightHandSide syn inh tb

-- | Attributed Tree Transducer
data AttrTreeTrans syn inh ta tb = AttrTreeTrans
  { initialAttr     :: syn
  , synthesizedRule :: SynthesizedRuleType syn inh ta tb
  , inheritedRule   :: InheritedRuleType syn inh ta tb
  }


-- reductions

data ReductionAttrState syn inh
  = SynAttrState syn [Int]
  | InhAttrState inh [Int]
  deriving (Show, Eq, Ord)

data ReductionState syn inh t l
  = AttrState (ReductionAttrState syn inh)
  | RankedTreeState l [ReductionState syn inh t l]
  deriving (Show, Eq, Ord)

type TreeReductionState syn inh t = ReductionState syn inh t (LabelType t)

data ReductionStateLabel syn inh t l
  = AttrStateLabel (ReductionAttrState syn inh)
  | RankedTreeStateLabel l
  deriving (Show, Eq, Ord)

type TreeReductionStateLabel syn inh t = ReductionStateLabel syn inh t (LabelType t)


instance (RankedTree t, l ~ LabelType t) => RankedTree (ReductionState syn inh t l) where
  type LabelType (ReductionState syn inh t l) = ReductionStateLabel syn inh t l

  treeLabel (AttrState s)         = AttrStateLabel s
  treeLabel (RankedTreeState l _) = RankedTreeStateLabel l

  treeChilds (AttrState _)          = []
  treeChilds (RankedTreeState _ ts) = ts

  treeLabelRank _ (AttrStateLabel _)       = 0
  treeLabelRank _ (RankedTreeStateLabel l) = treeLabelRank (Proxy :: Proxy t) l

  mkTree (AttrStateLabel l) []       = AttrState l
  mkTree (RankedTreeStateLabel l) ts = RankedTreeState l ts


applyRHSToState :: RankedTree t
  => TreeRightHandSide syn inh t
  -> [Int] -> TreeReductionState syn inh t
applyRHSToState rhs p = go rhs where
  go (SynAttrSide a i) = AttrState (SynAttrState a (i:p))
  go (InhAttrSide a)   = AttrState (InhAttrState a p)
  go (LabelSide l cs)  = RankedTreeState l [go c | c <- cs]


data ReductionStep syn inh l
  = SynReductionStep syn l
  | InhReductionStep inh Int l
  deriving (Show, Eq, Ord)

type ReductionSteps syn inh t = [ReductionStep syn inh t]

type TreeReductionStep syn inh t = ReductionStep syn inh (InputLabelType t)
type TreeReductionSteps syn inh t = [TreeReductionStep syn inh t]

-- | TODO
buildAttReduction :: forall b syn inh ta tb. RankedTree ta =>
  (b -> TreeReductionStep syn inh ta -> TreeReductionState syn inh tb -> b)
  -> b -> AttrTreeTrans syn inh ta tb -> ta -> b
buildAttReduction _f _s AttrTreeTrans{..} _t = go initState where
  initState = SynAttrState initialAttr []

  go = undefined

buildAttReduction' :: forall b syn inh ta tb. (RankedTree ta, RankedTree tb) =>
  (b -> TreeReductionState syn inh tb -> b)
  -> b -> AttrTreeTrans syn inh ta tb -> ta -> b
buildAttReduction' f s AttrTreeTrans{..} t = goTop s where
  goTop state =
    let rhs      = synthesizedRule initialAttr InitialLabel
        redState = applyRHSToState rhs []
    in go (f state redState) (rtZipper t) (rtZipper redState)

  go state taZ stateZ = undefined

buildAttReductionSteps :: RankedTree ta =>
  AttrTreeTrans syn inh ta tb -> ta -> TreeReductionSteps syn inh ta
buildAttReductionSteps trans t = reverse $ buildAttReduction builder [] trans t where
  builder steps step = const $ step : steps

runAttReduction :: (RankedTree ta, RankedTree tb) =>
  AttrTreeTrans syn inh ta tb -> ta -> tb
runAttReduction trans t = render $ builder trans t where
  builder = buildAttReduction (\_ _ s -> s) $ error "not expected operation"

  render (AttrState _)          = error "not expected operation"
  render (RankedTreeState l ss) = mkTree l [render s | s <- ss]

instance TreeTransducer (AttrTreeTrans syn inh) where
  treeTrans = runAttReduction
