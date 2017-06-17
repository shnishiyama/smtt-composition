{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}

module Data.SATT.ATT where

import ClassyPrelude

import Control.Arrow
import Data.Proxy

import Data.Tree.RankedTree
import Data.Tree.RankedTree.Zipper
import Data.Tree.RankedTree.Transducer

-- common

type RTZipperWithInitial t l = RTZipper (RankedTreeWithInitial t l) (RankedTreeLabelWithInitial l)

type InputLabelType t = RankedTreeLabelWithInitial (LabelType t)
type InputRankedTreeZipper t = RTZipperWithInitial t (LabelType t)

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
  deriving (Eq, Ord)

instance (Show syn, Show inh) => Show (ReductionAttrState syn inh) where
  show (SynAttrState a p) = show a <> show (reverse p)
  show (InhAttrState a p) = show a <> show (reverse p)

data ReductionState syn inh ta la tb lb
  = AttrState (RTZipperWithInitial ta la) (ReductionAttrState syn inh)
  | RankedTreeState lb [ReductionState syn inh ta la tb lb]
  deriving (Eq, Ord)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show lb)
  => Show (ReductionState syn inh ta la tb lb) where
  show = showTree

type TreeReductionState syn inh ta tb = ReductionState syn inh ta (LabelType ta) tb (LabelType tb)

fromTreeReductionState :: RankedTree tb => TreeReductionState syn inh ta tb -> Maybe tb
fromTreeReductionState (RankedTreeState l ss) = pure (mkTree l) <*> traverse fromTreeReductionState ss
fromTreeReductionState _                      = empty


data ReductionStateLabel syn inh ta la tb lb
  = AttrStateLabel (RTZipperWithInitial ta la) (ReductionAttrState syn inh)
  | RankedTreeStateLabel lb
  deriving (Eq, Ord)

instance (Show syn, Show inh, Show lb) => Show (ReductionStateLabel syn inh ta la tb lb) where

  show (AttrStateLabel _ a) = show a
  show (RankedTreeStateLabel l) = show l

type TreeReductionStateLabel syn inh ta tb
  = ReductionStateLabel syn inh ta (LabelType ta) tb (LabelType tb)


instance (RtConstraint ta la, RtConstraint tb lb)
  => RankedTree (ReductionState syn inh ta la tb lb) where

  type LabelType (ReductionState syn inh ta la tb lb) = ReductionStateLabel syn inh ta la tb lb

  treeLabel (AttrState z s)       = AttrStateLabel z s
  treeLabel (RankedTreeState l _) = RankedTreeStateLabel l

  treeChilds (AttrState _ _)        = []
  treeChilds (RankedTreeState _ ts) = ts

  treeLabelRank _ (AttrStateLabel _ _)     = 0
  treeLabelRank _ (RankedTreeStateLabel l) = treeLabelRank (Proxy :: Proxy tb) l

  mkTree (AttrStateLabel z s) []     = AttrState z s
  mkTree (RankedTreeStateLabel l) ts = RankedTreeState l ts
  mkTree _ _ = error "not permitted operation"

applyRHSToState :: (RankedTree ta, RankedTree tb)
  => TreeRightHandSide syn inh tb
  -> InputRankedTreeZipper ta -> [Int]
  -> TreeReductionState syn inh ta tb
applyRHSToState rhs z p = go rhs where
  go (SynAttrSide a i) = go' $ SynAttrState a (i:p)
  go (InhAttrSide a)   = go' $ InhAttrState a p
  go (LabelSide l cs)  = RankedTreeState l [go c | c <- cs]

  go' state = AttrState (nextTz state z) state

  nextTz attrState tz = fromMaybe tz $ nextTz' attrState tz

  nextTz' (InhAttrState _ _)     = zoomOutRtZipper
  nextTz' (SynAttrState _ [])    = zoomInRtZipper
  nextTz' (SynAttrState _ (x:_)) = zoomInIdxRtZipper x

type TreeReductionStateZipper syn inh ta tb
  = RTZipper (TreeReductionState syn inh ta tb) (TreeReductionStateLabel syn inh ta tb)


-- reduction systems

buildAttReduction :: forall b syn inh ta tb. (RankedTree ta, RankedTree tb) =>
  (b -> TreeReductionStateZipper syn inh ta tb -> b)
  -> b -> AttrTreeTrans syn inh ta tb -> ta -> b
buildAttReduction f s AttrTreeTrans{..} t = goTop s where
  applyAttrToState tz attrState =
    let l   = treeLabel $ toTree tz
    in applyAttrToState' l tz attrState

  applyAttrToState' l tz (SynAttrState a p) =
    let rhs = synthesizedRule a l
    in applyRHSToState rhs tz p
  applyAttrToState' l tz (InhAttrState a (x:xs)) =
    let rhs = inheritedRule a x l
    in applyRHSToState rhs tz xs
  applyAttrToState' _ _ (InhAttrState _ []) = error "inherited attr is empty..."

  initialAttrState = SynAttrState initialAttr []

  goTop state =
    let taZ      = rtZipper $ toRankedTreeWithInitial t
        stateZ   = rtZipper $ AttrState taZ initialAttrState
    in go' state stateZ

  go !state stateZ = case nextStateZ stateZ of
      Nothing      -> f state stateZ
      Just nstateZ -> go' state nstateZ

  go' state stateZ =
    let AttrState taZ attrState = toTree stateZ
        redState = applyAttrToState taZ attrState
        nstate   = f state stateZ
        stateZ'  = setTreeZipper redState stateZ
    in go nstate stateZ'

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
runAttReduction trans = render . toTopTree . builder where
  builder = fromMaybe (error "not permitted operation")
    . buildAttReduction (const Just) Nothing trans

  render = fromMaybe (error "unexpected operation")
    . fromTreeReductionState

data ReductionStep syn inh l
  = SynReductionStep syn l [Int]
  | InhReductionStep inh Int l [Int]
  deriving (Show, Eq, Ord)

type TreeReductionStep syn inh t = ReductionStep syn inh (InputLabelType t)

data ReductionStateStep syn inh ta la tb lb = ReductionStateStep
  { reductionStepState :: ReductionState syn inh ta la tb lb
  , reductionStateStep :: ReductionStep syn inh (RankedTreeLabelWithInitial la)
  } deriving (Eq, Ord)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show la, Show lb)
  => Show (ReductionStateStep syn inh ta la tb lb) where
  show (ReductionStateStep state step) = show state <> " =" <> showStep step <> "=> " where
    showStep (SynReductionStep _ l p)   = showStep' l p
    showStep (InhReductionStep _ _ l p) = showStep' l p

    showStep' l p = "{" <> show l <> "," <> show (reverse p) <> "}"

data ReductionSteps syn inh ta la tb lb = ReductionSteps
  { reductionSteps :: [ReductionStateStep syn inh ta la tb lb]
  , reductionResult :: tb
  } deriving (Eq, Ord)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show la, Show lb, Show tb)
  => Show (ReductionSteps syn inh ta la tb lb) where
  show (ReductionSteps steps res) = intercalate "" (map show steps) <> " " <> show res

type TreeReductionSteps syn inh ta tb = ReductionSteps syn inh ta (LabelType ta) tb (LabelType tb)

buildStepFromAttrState :: l -> ReductionAttrState syn inh -> ReductionStep syn inh l
buildStepFromAttrState l = go where
  go (SynAttrState a p)      = SynReductionStep a l p
  go (InhAttrState a (x:xs)) = InhReductionStep a x l xs
  go _                       = error "unexpected operation"

buildAttReductionSteps :: (RankedTree ta, RankedTree tb) =>
  AttrTreeTrans syn inh ta tb -> ta -> TreeReductionSteps syn inh ta tb
buildAttReductionSteps trans = buildSteps . buildAttReduction builder ([], Nothing) trans where
  buildSteps = uncurry ReductionSteps <<< reverse *** render

  builder (steps, Just sz) stateZ = (buildStepFromStateZ sz : steps, Just stateZ)
  builder (steps, Nothing) stateZ = (steps, Just stateZ)

  buildStepFromStateZ stateZ =
    let AttrState taZ attrState = toTree stateZ
    in ReductionStateStep (toTopTree stateZ) $ buildStepFromAttrState (getTreeLabel taZ) attrState

  render mstateZ = fromMaybe (error "unexpected operation") $ do
    stateZ <- mstateZ
    let state = toTopTree stateZ

    fromTreeReductionState state


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

    one a   = LabelSide "one" [a]
    two a   = LabelSide "two" [a]
    plus a  = LabelSide "plus" [a]
    multi a = LabelSide "multi" [a]
    end     = LabelSide "$" []

    synRule _ InitialLabel              = SynAttrSide a0 1
    synRule _ (RankedTreeLabel "one")   = one $ InhAttrSide a1
    synRule _ (RankedTreeLabel "two")   = two $ InhAttrSide a1
    synRule _ (RankedTreeLabel "plus")  = SynAttrSide a0 1
    synRule _ (RankedTreeLabel "multi") = SynAttrSide a0 1
    synRule _ l                         = error $ "unsupported label: " ++ show l

    inhRule _ 1 InitialLabel              = end
    inhRule _ 1 (RankedTreeLabel "plus")  = SynAttrSide a0 2
    inhRule _ 2 (RankedTreeLabel "plus")  = plus $ InhAttrSide a1
    inhRule _ 1 (RankedTreeLabel "multi") = SynAttrSide a0 2
    inhRule _ 2 (RankedTreeLabel "multi") = multi $ InhAttrSide a1
    inhRule _ i l                         = error $ "unsupported label: (" <> show i <> "," <> show l <> ")"
