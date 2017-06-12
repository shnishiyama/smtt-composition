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


-- reduction states

data ReductionAttrState syn inh
  = SynAttrState syn [Int]
  | InhAttrState inh [Int]
  deriving (Show, Eq, Ord)

data ReductionState syn inh ta tb la lb
  = AttrState (RTZipper ta la) (ReductionAttrState syn inh)
  | RankedTreeState lb [ReductionState syn inh ta tb la lb]
  deriving (Show, Eq, Ord)

type TreeReductionState syn inh ta tb = ReductionState syn inh ta tb (LabelType ta) (LabelType tb)

data ReductionStateLabel syn inh ta tb la lb
  = AttrStateLabel (RTZipper ta la) (ReductionAttrState syn inh)
  | RankedTreeStateLabel lb
  deriving (Show, Eq, Ord)

type TreeReductionStateLabel syn inh ta tb = ReductionStateLabel syn inh ta tb (LabelType ta) (LabelType tb)


instance (RankedTree ta, RankedTree tb, la ~ LabelType ta, lb ~ LabelType tb)
  => RankedTree (ReductionState syn inh ta tb la lb) where

  type LabelType (ReductionState syn inh ta tb la lb) = ReductionStateLabel syn inh ta tb la lb

  treeLabel (AttrState z s)       = AttrStateLabel z s
  treeLabel (RankedTreeState l _) = RankedTreeStateLabel l

  treeChilds (AttrState _ _)        = []
  treeChilds (RankedTreeState _ ts) = ts

  treeLabelRank _ (AttrStateLabel _ _)     = 0
  treeLabelRank _ (RankedTreeStateLabel l) = treeLabelRank (Proxy :: Proxy tb) l

  mkTree (AttrStateLabel z s) []     = AttrState z s
  mkTree (RankedTreeStateLabel l) ts = RankedTreeState l ts


applyRHSToState :: (RankedTree ta, RankedTree tb)
  => TreeRightHandSide syn inh tb
  -> RankedTreeZipper ta -> [Int]
  -> TreeReductionState syn inh ta tb
applyRHSToState rhs z p = go rhs where
  go (SynAttrSide a i) = AttrState z (SynAttrState a (i:p))
  go (InhAttrSide a)   = AttrState z (InhAttrState a p)
  go (LabelSide l cs)  = RankedTreeState l [go c | c <- cs]

type TreeReductionStateZipper syn inh ta tb = RankedTreeZipper (TreeReductionState syn inh ta tb)


-- reduction steps

data ReductionStep syn inh l
  = SynReductionStep syn l
  | InhReductionStep inh Int l
  deriving (Show, Eq, Ord)

type ReductionSteps syn inh t = [ReductionStep syn inh t]

type TreeReductionStep syn inh t = ReductionStep syn inh (InputLabelType t)
type TreeReductionSteps syn inh t = [TreeReductionStep syn inh t]


buildAttReduction :: forall b syn inh ta tb. RankedTree ta =>
  (b -> TreeReductionStep syn inh ta -> TreeReductionStateZipper syn inh ta tb -> b)
  -> b -> AttrTreeTrans syn inh ta tb -> ta -> b
buildAttReduction _f _s AttrTreeTrans{..} _t = go initState where
  initState = SynAttrState initialAttr []

  go = undefined

buildAttReduction' :: forall b syn inh ta tb. (RankedTree ta, RankedTree tb) =>
  (b -> TreeReductionStateZipper syn inh ta tb -> b)
  -> b -> AttrTreeTrans syn inh ta tb -> ta -> b
buildAttReduction' f s AttrTreeTrans{..} t = goTop s where
  applyAttrToState l tz (SynAttrState a p) =
    let rhs = synthesizedRule a l
    in applyRHSToState rhs tz p
  applyAttrToState l tz (InhAttrState a (x:xs)) =
    let rhs = inheritedRule a x l
    in applyRHSToState rhs tz xs

  f' x = f $! x

  initialAttrState = SynAttrState initialAttr []

  goTop state =
    let taZ      = rtZipper t
        redState = applyAttrToState InitialLabel taZ initialAttrState
        stateZ   = rtZipper redState
    in go state stateZ

  go state stateZ =
    let nstate = f' state stateZ
    in case nextStateZ stateZ of
      Nothing      -> state
      Just nstateZ -> go' nstate nstateZ

  go' state stateZ =
    let AttrState taZ attrState = toTree stateZ
        (ntaZ, l) = nextTaZ attrState taZ
        redState  = applyAttrToState l ntaZ attrState
        stateZ'   = setTreeZipper redState stateZ
    in go state stateZ'

  nextStateZ _stateZ = undefined

  nextTaZ attrState taZ = maybe (taZ, InitialLabel) (id &&& InputLabel . treeLabel . toTree)
    $ nextTaZ' attrState taZ

  nextTaZ' (InhAttrState _ _) = zoomOutRtZipper
  nextTaZ' (SynAttrState _ _) = zoomInRtZipper


buildAttReductionSteps :: RankedTree ta =>
  AttrTreeTrans syn inh ta tb -> ta -> TreeReductionSteps syn inh ta
buildAttReductionSteps trans t = reverse $ buildAttReduction builder [] trans t where
  builder steps step = const $ step : steps

runAttReduction :: (RankedTree ta, RankedTree tb) =>
  AttrTreeTrans syn inh ta tb -> ta -> tb
runAttReduction trans t = render . toTree . zoomTopRtZipper $ builder trans t where
  builder = buildAttReduction (\_ _ s -> s) $ error "not expected operation"

  render (AttrState _ _)        = error "not expected operation"
  render (RankedTreeState l ss) = mkTree l [render s | s <- ss]

instance TreeTransducer (AttrTreeTrans syn inh) where
  treeTrans = runAttReduction
