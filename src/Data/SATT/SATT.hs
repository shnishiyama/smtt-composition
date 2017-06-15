{-# OPTIONS_GHC -fno-warn-incomplete-patterns #-}

{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}

module Data.SATT.ATT where

import ClassyPrelude

import Control.Arrow
import Data.Proxy

import qualified Data.SATT.ATT as ATT
import Data.Tree.RankedTree
import Data.Tree.RankedTree.Zipper
import Data.Tree.Transducer

-- common

type InputLabelType t = RankedTreeLabelWithInitial (LabelType t)
type InputRankedTreeZipper t = RTZipper (RankedTreeWithInitial t (LabelType t)) (InputLabelType t)

data OutputRightHandSide syn inh stsyn stinh l
  = OutputSynAttrSide syn Int
  | OutputInhAttrSide inh
  | StackHeadSide (StackRighHandSide syn inh stsyn stinh l)
  | LabelSide l [OutputRightHandSide syn inh stsyn stinh l]
  deriving (Show, Eq, Ord)

data StackRighHandSide syn inh stsyn stinh l
  = StackEmptySide
  | StackConsSide (OutputRightHandSide syn inh stsyn stinh l) (StackRighHandSide syn inh stsyn stinh l)
  | StackTailSide (StackRighHandSide syn inh stsyn stinh l)
  deriving (Show, Eq, Ord)

data RightHandSide syn inh stsyn stinh l
  = OutputExpression (OutputRightHandSide syn inh stsyn stinh l)
  | StackExpression (StackRighHandSide syn inh stsyn stinh l)
  deriving (Show, Eq, Ord)

type TreeOutputRightHandSide syn inh stsyn stinh t = OutputRightHandSide syn inh stsyn stinh (LabelType t)
type TreeStackRightHandSide syn inh stsyn stinh t = StackRightHandSide syn inh stsyn stinh (LabelType t)
type TreeRightHandSide syn inh stsyn stinh t = RightHandSide syn inh stsyn stinh (LabelType t)

type OutputSynthesizedRuleType syn inh stsyn stinh ta tb =
  syn -> InputLabelType ta ->
    TreeOutputRightHandSide syn inh stsyn stinh tb

type OutputInheritedRuleType syn inh stsyn stinh ta tb =
  inh -> Int -> InputLabelType ta ->
    TreeOutputRightHandSide syn inh stsyn stinh tb

type StackSynthesizedRuleType syn inh stsyn stinh ta tb =
  stsyn -> InputLabelType ta ->
    TreeStackRightHandSide syn inh stsyn stinh tb

type StackInheritedRuleType syn inh stsyn stinh ta tb =
  stinh -> Int -> InputLabelType ta ->
    TreeStackRightHandSide syn inh stsyn stinh tb

-- | Stack-Attributed Tree Transducer
data StackAttrTreeTrans syn inh stsyn stinh ta tb = StackAttrTreeTrans
  { initialAttr           :: syn
  , outputSynthesizedRule :: OutputSynthesizedRuleType syn inh stsyn stinh ta tb
  , outputInheritedRule   :: OutputInheritedRuleType syn inh stsyn stinh ta tb
  , stackSynthesizedRule  :: StackSynthesizedRuleType syn inh stsyn stinh ta tb
  , stackInheritedRule    :: StackInheritedRuleType syn inh stsyn stinh ta tb
  }


-- reduction states

type RTZipperWithInitial t l = RTZipper (RankedTreeWithInitial t l) (RankedTreeLabelWithInitial l)

data ReductionOutputAttrState syn inh
  = OutputSynAttrState syn [Int]
  | OutputInhAttrState inh [Int]
  deriving (Show, Eq, Ord)

data ReductionStackAttrState stsyn stinh
  = StackSynAttrState stsyn [Int]
  | StackInhAttrState stinh [Int]
  deriving (Show, Eq, Ord)

data OutputReductionType = OutputReductionType
  deriving (Show, Eq, Ord)

data StackReductionType  = StackReductionType
  deriving (Show, Eq, Ord)

data ReductionStackState syn inh stsyn stinh ta la tb lb
  = StackAttrState (RTZipperWithInitial ta la) (ReductionStackAttrState stsyn stinh)
  | StackEmptyState
  | StackConsState (ReductionState syn inh stsyn stinh ta la tb lb) (ReductionStackState syn inh stsyn stinh ta la tb lb)
  | StackTailState (ReductionStackState syn inh stsyn stinh ta la tb lb)
  deriving (Show, Eq, Ord)

data ReductionOutputState syn inh stsyn stinh ta la tb lb
  = OutputAttrState (RTZipperWithInitial ta la) (ReductionOutputAttrState syn inh)
  | RankedTreeState lb [ReductionState syn inh stsyn stinh ta la tb lb]
  | StackHeadState (ReductionStackState syn inh stsyn stinh ta la tb lb)
  deriving (Show, Eq, Ord)

data ReductionState syn inh stsyn stinh ta la tb lb
  = OutputReduction (ReductionOutputState syn inh stsyn stinh ta la tb lb)
  | StackReduction (ReductionStackState syn inh stsyn stinh ta la tb lb)
  deriving (Show, Eq, Ord)

type TreeReductionState syn inh stsyn stinh ta tb = ReductionState syn inh stsyn stinh ta (LabelType ta) tb (LabelType tb)

data ReductionStateLabel syn inh stsyn stinh ta la tb lb
  = OutputAttrStateLabel (RTZipperWithInitial ta la) (ReductionOutputAttrState syn inh)
  | StackAttrStateLabel (RTZipperWithInitial ta la) (ReductionStackAttrState stsyn stinh)
  | RankedTreeStateLabel lb
  | StackEmptyStateLabel
  | StackHeadStateLabel
  | StackConsStateLabel
  | StackTailStateLabel
  deriving (Show, Eq, Ord)

type TreeReductionStateLabel syn inh stsyn stinh ta tb = ReductionStateLabel syn inh stsyn stinh ta (LabelType ta) tb (LabelType tb)


instance (RankedTree ta, RankedTree tb, la ~ LabelType ta, lb ~ LabelType tb)
  => RankedTree (ReductionState syn inh stsyn stinh ta la tb lb) where

  type LabelType (ReductionState syn inh stsyn stinh ta la tb lb) = ReductionStateLabel syn inh stsyn stinh ta la tb lb

  treeLabel (OutputReduction os) = go os where
    go (OutputAttrState z s) = OutputAttrStateLabel z s
    go (RankedTreeState l _) = RankedTreeStateLabel l
    go (StackHeadState _)    = StackHeadStateLabel
  treeLabel (StackReduction ss) = go ss where
    go (StackAttrState  z s) = StackAttrStateLabel z s
    go StackEmptyState       = StackEmptyStateLabel
    go (StackConsState _ _)  = StackConsStateLabel
    go (StackTailState _)    = StackTailStateLabel

  treeChilds (OutputReduction os) = go os where
    go (OutputAttrState _ _)  = []
    go (RankedTreeState _ ts) = map OutputReduction ts
    go (StackHeadState s)     = [StackReduction s]
  treeChilds (StackReduction ss) = go ss where
    go (StackAttrState _ _)   = []
    go StackEmptyState        = []
    go (StackConsState h s)   = [OutputReduction h, StackReduction s]
    go (StackTailState s)     = [StackReduction s]

  treeLabelRank _ (OutputAttrStateLabel _ _) = 0
  treeLabelRank _ (StackAttrStateLabel _ _)  = 0
  treeLabelRank _ (RankedTreeStateLabel l)   = treeLabelRank (Proxy :: Proxy tb) l
  treeLabelRank _ StackEmptyStateLabel       = 0
  treeLabelRank _ StackHeadStateLabel        = 1
  treeLabelRank _ StackConsStateLabel        = 2
  treeLabelRank _ StackTailStateLabel        = 1

  mkTree (OutputAttrStateLabel z s) []  = OutputReduction $ OutputAttrState z s
  mkTree (StackAttrStateLabel z s)  []  = StackReduction $ StackAttrState z s
  mkTree (RankedTreeStateLabel l)   ts  = OutputReduction $ RankedTreeState l ts
  mkTree StackEmptyStateLabel       []  = StackReduction StackEmptyState
  mkTree StackHeadStateLabel [StackReduction s] = OutputReduction $ StackHeadState s
  mkTree StackConsStateLabel [OutputReduction h, StackReduction s] = StackReduction $ StackConsState h s
  mkTree StackTailStateLabel [StackReduction s] = StackReduction $ StackTailState s

applyRHSToState :: (RankedTree ta, RankedTree tb)
  => TreeRightHandSide syn inh tb
  -> InputRankedTreeZipper ta -> [Int]
  -> TreeReductionState syn inh ta tb
applyRHSToState rhs z p = go rhs where
  go (SynAttrSide a i) = AttrState z (SynAttrState a (i:p))
  go (InhAttrSide a)   = AttrState z (InhAttrState a p)
  go (LabelSide l cs)  = RankedTreeState l [go c | c <- cs]


type TreeReductionStateZipper syn inh ta tb
  = RTZipper (TreeReductionState syn inh ta tb) (TreeReductionStateLabel syn inh ta tb)


-- reduction steps

data ReductionStep syn inh l
  = SynReductionStep syn l [Int]
  | InhReductionStep inh Int l [Int]
  deriving (Show, Eq, Ord)

type ReductionSteps syn inh t = [ReductionStep syn inh t]

type TreeReductionStep syn inh t = ReductionStep syn inh (InputLabelType t)
type TreeReductionSteps syn inh t = [TreeReductionStep syn inh t]

buildStepFromAttrState :: l -> ReductionAttrState syn inh -> ReductionStep syn inh l
buildStepFromAttrState l (SynAttrState a p)      = SynReductionStep a l p
buildStepFromAttrState l (InhAttrState a (x:xs)) = InhReductionStep a x l xs

buildAttReduction :: forall b syn inh ta tb. (RankedTree ta, RankedTree tb) =>
  (b -> TreeReductionStateZipper syn inh ta tb -> b)
  -> b -> AttrTreeTrans syn inh ta tb -> ta -> b
buildAttReduction f s AttrTreeTrans{..} t = goTop s where
  applyAttrToState tz =
    let l = treeLabel $ toTree tz in applyAttrToState' l tz

  applyAttrToState' l tz (SynAttrState a p) =
    let rhs = synthesizedRule a l
    in applyRHSToState rhs tz p
  applyAttrToState' l tz (InhAttrState a (x:xs)) =
    let rhs = inheritedRule a x l
    in applyRHSToState rhs tz xs
  applyAttrToState' _ _ (InhAttrState _ []) = error "inherited attr is empty..."

  f' x = f $! x

  initialAttrState = SynAttrState initialAttr []

  goTop state =
    let taZ      = rtZipper $ toRankedTreeWithInitial t
        redState = applyAttrToState taZ initialAttrState
        stateZ   = rtZipper redState
    in go state stateZ

  go state stateZ = case nextStateZ stateZ of
      Nothing      -> f' state stateZ
      Just nstateZ -> go' state nstateZ

  go' state stateZ =
    let AttrState taZ attrState = toTree stateZ
        ntaZ     = nextTaZ attrState taZ
        redState = applyAttrToState ntaZ attrState
        nstate   = f' state stateZ
        stateZ'  = setTreeZipper redState stateZ
    in go nstate stateZ'

  nextTaZ attrState taZ = fromMaybe taZ $ nextTaZ' attrState taZ

  nextTaZ' (InhAttrState _ _)     = zoomOutRtZipper
  nextTaZ' (SynAttrState _ (x:_)) = zoomInIdxRtZipper x

  nextStateZ = runKleisli nextStateZ'

  nextStateZ'
    =   Kleisli filterLabelStateZipper
    <+> (Kleisli zoomInRtZipper >>> nextStateZ')
    <+> nextStateZ''

  filterLabelStateZipper :: TreeReductionStateZipper syn inh ta tb -> Maybe (TreeReductionStateZipper syn inh ta tb)
  filterLabelStateZipper taZ = case toTree taZ of
    RankedTreeState _ _ -> empty
    _                   -> return taZ

  nextStateZ''
    =   (Kleisli zoomRightRtZipper >>> nextStateZ')
    <+> (Kleisli zoomOutRtZipper   >>> nextStateZ'')

runAttReduction :: (RankedTree ta, RankedTree tb) =>
  AttrTreeTrans syn inh ta tb -> ta -> tb
runAttReduction trans t = render . toTree . zoomTopRtZipper $ builder t where
  builder = fromMaybe (error "not permitted operation")
    . buildAttReduction (\_ s -> Just s) Nothing trans

  render (AttrState _ _)        = error "not expected operation"
  render (RankedTreeState l ss) = mkTree l [render s | s <- ss]

buildAttReductionSteps :: (RankedTree ta, RankedTree tb) =>
  AttrTreeTrans syn inh ta tb -> ta -> (TreeReductionSteps syn inh ta, tb)
buildAttReductionSteps trans t = reverse *** render $ buildAttReduction builder ([], Nothing) trans t where
  builder (steps, Just sz) stateZ = (buildStepFromStateZ sz : steps, Just stateZ)
  builder (steps, Nothing) stateZ = (steps, Just stateZ)

  buildStepFromStateZ stateZ =
    let AttrState taZ attrState = toTree stateZ
    in buildStepFromAttrState (treeLabel $ toTree taZ) attrState

  render (Just stateZ) = render' . toTree $ zoomTopRtZipper stateZ
  render Nothing       = error "not excepted operation"

  render' (AttrState _ _)        = error "not expected operation"
  render' (RankedTreeState l ss) = mkTree l [render' s | s <- ss]

-- tree transducer

instance TreeTransducer (AttrTreeTrans syn inh) where
  treeTrans = runAttReduction


-- instances

data SynAttrUnit = SynAttrUnit
  deriving (Eq, Ord)

instance Show SynAttrUnit where
  show _ = "a0"

data InhAttrUnit = InhAttrUnit
  deriving (Eq, Ord)

instance Show InhAttrUnit where
  show _ = "a1"


infixToPostfixTransducer :: AttrTreeTrans SynAttrUnit InhAttrUnit InfixOpTree PostfixOpTree
infixToPostfixTransducer = AttrTreeTrans
  { initialAttr     = a0
  , synthesizedRule = synRule
  , inheritedRule   = inhRule
  }
  where
    a0 = SynAttrUnit
    a1 = InhAttrUnit

    synRule _ InitialLabel              = SynAttrSide a0 1
    synRule _ (RankedTreeLabel "one")   = LabelSide "one" [InhAttrSide a1]
    synRule _ (RankedTreeLabel "two")   = LabelSide "two" [InhAttrSide a1]
    synRule _ (RankedTreeLabel "plus")  = SynAttrSide a0 1
    synRule _ (RankedTreeLabel "multi") = SynAttrSide a0 1

    inhRule _ 1 InitialLabel              = LabelSide "$" []
    inhRule _ 1 (RankedTreeLabel "plus")  = SynAttrSide a0 2
    inhRule _ 2 (RankedTreeLabel "plus")  = LabelSide "plus" [InhAttrSide a1]
    inhRule _ 1 (RankedTreeLabel "multi") = SynAttrSide a0 2
    inhRule _ 2 (RankedTreeLabel "multi") = LabelSide "multi" [InhAttrSide a1]
