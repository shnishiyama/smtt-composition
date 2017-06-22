{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}

module Data.SATT.SATT where

import ClassyPrelude

import Control.Arrow
import Data.Proxy
import Data.Void

import qualified Data.SATT.ATT as ATT
import Data.Tree.RankedTree
import Data.Tree.RankedTree.Zipper
import Data.Tree.RankedTree.Transducer

-- common

type RTZipperWithInitial t l = RTZipper (RankedTreeWithInitial t l) (RankedTreeLabelWithInitial l)

type InputLabelType t = RankedTreeLabelWithInitial (LabelType t)
type InputRankedTreeZipper t = RTZipperWithInitial t (LabelType t)

data OutputRightHandSide syn inh stsyn stinh l
  = OutputSynAttrSide syn Int
  | OutputInhAttrSide inh
  | LabelSide l [OutputRightHandSide syn inh stsyn stinh l]
  | StackHeadSide (StackRightHandSide syn inh stsyn stinh l)
  deriving (Show, Eq, Ord)

data StackRightHandSide syn inh stsyn stinh l
  = StackSynAttrSide stsyn Int
  | StackInhAttrSide stinh
  | StackEmptySide
  | StackConsSide (OutputRightHandSide syn inh stsyn stinh l) (StackRightHandSide syn inh stsyn stinh l)
  | StackTailSide (StackRightHandSide syn inh stsyn stinh l)
  deriving (Show, Eq, Ord)

data RightHandSide syn inh stsyn stinh l
  = OutputExpr (OutputRightHandSide syn inh stsyn stinh l)
  | StackExpr (StackRightHandSide syn inh stsyn stinh l)
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

data ReductionOutputAttrState syn inh
  = OutputSynAttrState syn [Int]
  | OutputInhAttrState inh [Int]
  deriving (Eq, Ord)

instance (Show syn, Show inh) => Show (ReductionOutputAttrState syn inh) where
  show (OutputSynAttrState a p) = show a <> show (reverse p)
  show (OutputInhAttrState a p) = show a <> show (reverse p)

data ReductionStackAttrState stsyn stinh
  = StackSynAttrState stsyn [Int]
  | StackInhAttrState stinh [Int]
  deriving (Eq, Ord)

instance (Show stsyn, Show stinh) => Show (ReductionStackAttrState stsyn stinh) where
  show (StackSynAttrState a p) = show a <> show (reverse p)
  show (StackInhAttrState a p) = show a <> show (reverse p)

data ReductionOutputState syn inh stsyn stinh ta la tb lb
  = OutputAttrState (RTZipperWithInitial ta la) (ReductionOutputAttrState syn inh)
  | RankedTreeState lb [ReductionOutputState syn inh stsyn stinh ta la tb lb]
  | StackHeadState (ReductionStackState syn inh stsyn stinh ta la tb lb)
  deriving (Eq, Ord)

data ReductionStackState syn inh stsyn stinh ta la tb lb
  = StackAttrState (RTZipperWithInitial ta la) (ReductionStackAttrState stsyn stinh)
  | StackEmptyState
  | StackConsState
    (ReductionOutputState syn inh stsyn stinh ta la tb lb)
    (ReductionStackState syn inh stsyn stinh ta la tb lb)
  | StackTailState (ReductionStackState syn inh stsyn stinh ta la tb lb)
  deriving (Eq, Ord)

data ReductionState syn inh stsyn stinh ta la tb lb
  = OutputReduction (ReductionOutputState syn inh stsyn stinh ta la tb lb)
  | StackReduction (ReductionStackState syn inh stsyn stinh ta la tb lb)
  deriving (Eq, Ord)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show stsyn, Show stinh, Show lb)
  => Show (ReductionState syn inh stsyn stinh ta la tb lb) where
  show = showTree

type TreeReductionState syn inh stsyn stinh ta tb = ReductionState syn inh stsyn stinh ta (LabelType ta) tb (LabelType tb)

fromTreeReductionState :: RankedTree tb => TreeReductionState syn inh stsyn stinh ta tb -> Maybe tb
fromTreeReductionState (OutputReduction ostate) = go ostate where
  go (RankedTreeState l ss) = pure (mkTree l) <*> traverse go ss
  go _                      = empty
fromTreeReductionState _ = empty

data ReductionStateLabel syn inh stsyn stinh ta la tb lb
  = OutputAttrStateLabel (RTZipperWithInitial ta la) (ReductionOutputAttrState syn inh)
  | StackAttrStateLabel (RTZipperWithInitial ta la) (ReductionStackAttrState stsyn stinh)
  | RankedTreeStateLabel lb
  | StackEmptyStateLabel
  | StackHeadStateLabel
  | StackConsStateLabel
  | StackTailStateLabel
  deriving (Eq, Ord)

instance (Show syn, Show inh, Show stsyn, Show stinh, Show lb)
  => Show (ReductionStateLabel syn inh stsyn stinh ta la tb lb) where

  show (OutputAttrStateLabel _ a) = show a
  show (StackAttrStateLabel _ a)  = show a
  show (RankedTreeStateLabel l)   = show l
  show StackEmptyStateLabel       = "Empty"
  show StackHeadStateLabel        = "Head"
  show StackConsStateLabel        = "Cons"
  show StackTailStateLabel        = "Tail"


type TreeReductionStateLabel syn inh stsyn stinh ta tb
  = ReductionStateLabel syn inh stsyn stinh ta (LabelType ta) tb (LabelType tb)

instance (RtConstraint ta la, RtConstraint tb lb)
  => RankedTree (ReductionState syn inh stsyn stinh ta la tb lb) where

  type LabelType (ReductionState syn inh stsyn stinh ta la tb lb) = ReductionStateLabel syn inh stsyn stinh ta la tb lb

  treeLabel (OutputReduction os) = go os where
    go (OutputAttrState z s) = OutputAttrStateLabel z s
    go (RankedTreeState l _) = RankedTreeStateLabel l
    go (StackHeadState _)    = StackHeadStateLabel
  treeLabel (StackReduction ss) = go ss where
    go (StackAttrState z s) = StackAttrStateLabel z s
    go StackEmptyState      = StackEmptyStateLabel
    go (StackConsState _ _) = StackConsStateLabel
    go (StackTailState _)   = StackTailStateLabel

  treeChilds (OutputReduction os) = go os where
    go (OutputAttrState _ _)  = []
    go (RankedTreeState _ ts) = map OutputReduction ts
    go (StackHeadState s)     = [StackReduction s]
  treeChilds (StackReduction ss) = go ss where
    go (StackAttrState _ _) = []
    go StackEmptyState      = []
    go (StackConsState h s) = [OutputReduction h, StackReduction s]
    go (StackTailState s)   = [StackReduction s]

  treeLabelRank _ (OutputAttrStateLabel _ _) = 0
  treeLabelRank _ (StackAttrStateLabel _ _)  = 0
  treeLabelRank _ (RankedTreeStateLabel l)   = treeLabelRank (Proxy :: Proxy tb) l
  treeLabelRank _ StackEmptyStateLabel       = 0
  treeLabelRank _ StackHeadStateLabel        = 1
  treeLabelRank _ StackConsStateLabel        = 2
  treeLabelRank _ StackTailStateLabel        = 1

  mkTree (OutputAttrStateLabel z s) [] = OutputReduction $ OutputAttrState z s
  mkTree (StackAttrStateLabel z s)  [] = StackReduction  $ StackAttrState  z s
  mkTree (RankedTreeStateLabel l)   ts = OutputReduction $ RankedTreeState l ts'
    where
      ts' = map filterOutputReduction ts

      filterOutputReduction (OutputReduction h) = h
      filterOutputReduction _                   = error "unexpected operation"
  mkTree StackEmptyStateLabel [] = StackReduction StackEmptyState
  mkTree StackHeadStateLabel  [StackReduction s] = OutputReduction $ StackHeadState s
  mkTree StackConsStateLabel  [OutputReduction h, StackReduction s] = StackReduction $ StackConsState h s
  mkTree StackTailStateLabel  [StackReduction s] = StackReduction $ StackTailState s
  mkTree _ _ = error "not permitted operation"

applyRHSToState :: (RankedTree ta, RankedTree tb)
  => TreeRightHandSide syn inh stsyn stinh tb
  -> InputRankedTreeZipper ta -> [Int]
  -> TreeReductionState syn inh stsyn stinh ta tb
applyRHSToState rhs z p = go rhs where
  go (OutputExpr orhs) = OutputReduction $ goOutput orhs
  go (StackExpr  srhs) = StackReduction $ goStack srhs

  goOutput (OutputSynAttrSide a i) = goOutput' $ OutputSynAttrState a (i:p)
  goOutput (OutputInhAttrSide a)   = goOutput' $ OutputInhAttrState a p
  goOutput (LabelSide l cs)        = RankedTreeState l [goOutput c | c <- cs]
  goOutput (StackHeadSide srhs)    = StackHeadState (goStack srhs)

  goOutput' state = OutputAttrState (nextOutputTz state z) state

  nextOutputTz attrState tz = fromMaybe tz $ nextOutputTz' attrState tz

  nextOutputTz' (OutputInhAttrState _ _)     = zoomOutRtZipper
  nextOutputTz' (OutputSynAttrState _ [])    = zoomInRtZipper
  nextOutputTz' (OutputSynAttrState _ (x:_)) = zoomInIdxRtZipper x

  goStack (StackSynAttrSide a i)    = goStack' $ StackSynAttrState a (i:p)
  goStack (StackInhAttrSide a)      = goStack' $ StackInhAttrState a p
  goStack StackEmptySide            = StackEmptyState
  goStack (StackConsSide orhs srhs) = StackConsState (goOutput orhs) (goStack srhs)
  goStack (StackTailSide srhs)      = StackTailState $ goStack srhs

  goStack' state = StackAttrState (nextStackTz state z) state

  nextStackTz attrState tz = fromMaybe tz $ nextStackTz' attrState tz

  nextStackTz' (StackInhAttrState _ _)     = zoomOutRtZipper
  nextStackTz' (StackSynAttrState _ [])    = zoomInRtZipper
  nextStackTz' (StackSynAttrState _ (x:_)) = zoomInIdxRtZipper x

type TreeReductionStateZipper syn inh stsyn stinh ta tb
  = RTZipper (TreeReductionState syn inh stsyn stinh ta tb) (TreeReductionStateLabel syn inh stsyn stinh ta tb)


-- reduction systems

buildSattReduction :: forall b syn inh stsyn stinh ta tb. (RankedTree ta, RankedTree tb) =>
  (b -> TreeReductionStateZipper syn inh stsyn stinh ta tb -> b)
  -> b -> StackAttrTreeTrans syn inh stsyn stinh ta tb -> ta -> b
buildSattReduction f s StackAttrTreeTrans{..} t = goTop s where
  applyOutputAttrToState tz attrState =
    let l   = treeLabel $ toTree tz
    in applyOutputAttrToState' l tz attrState

  applyOutputRHSToState orhs = applyRHSToState $ OutputExpr orhs

  applyOutputAttrToState' l tz (OutputSynAttrState a p) =
    let rhs = outputSynthesizedRule a l
    in applyOutputRHSToState rhs tz p
  applyOutputAttrToState' l tz (OutputInhAttrState a (x:xs)) =
    let rhs = outputInheritedRule a x l
    in applyOutputRHSToState rhs tz xs
  applyOutputAttrToState' _ _ (OutputInhAttrState _ []) = error "output inherited attr is empty..."

  applyStackAttrToState tz attrState =
    let l   = treeLabel $ toTree tz
    in applyStackAttrToState' l tz attrState

  applyStackRHSToState srhs = applyRHSToState $ StackExpr srhs

  applyStackAttrToState' l tz (StackSynAttrState a p) =
    let rhs = stackSynthesizedRule a l
    in applyStackRHSToState rhs tz p
  applyStackAttrToState' l tz (StackInhAttrState a (x:xs)) =
    let rhs = stackInheritedRule a x l
    in applyStackRHSToState rhs tz xs
  applyStackAttrToState' _ _ (StackInhAttrState _ []) = error "stack inherited attr is empty..."

  initialOutputAttrState = OutputSynAttrState initialAttr []

  goTop state =
    let taZ      = rtZipper $ toRankedTreeWithInitial t
        stateZ   = rtZipper . OutputReduction $ OutputAttrState taZ initialOutputAttrState
    in go' state stateZ

  go !state stateZ = case nextStateZ stateZ of
      Nothing      -> f state stateZ
      Just nstateZ -> go' state nstateZ

  go' state stateZ =
    let nstate   = f state stateZ

        stateZ' = case toTree stateZ of
          OutputReduction (OutputAttrState taZ outputAttrState) ->
            setTreeZipper (applyOutputAttrToState taZ outputAttrState) stateZ
          StackReduction (StackAttrState taZ stackAttrState) ->
            setTreeZipper (applyStackAttrToState taZ stackAttrState) stateZ
          StackReduction (StackConsState hd tl) ->
            deconstractStack hd tl stateZ
          _ ->
            error "not permitted operation"

    in go nstate stateZ'

  deconstractStack hd tl stateZ = case zoomOutRtZipper stateZ of
    Nothing -> error "not permitted operation"
    Just nstateZ -> case toTree nstateZ of
      OutputReduction (StackHeadState _) -> setTreeZipper (OutputReduction hd) nstateZ
      StackReduction  (StackTailState _) -> setTreeZipper (StackReduction  tl) nstateZ
      _ -> error "not permitted operation"

  nextStateZ = runKleisli nextStateZ'

  nextStateZ'
    =   Kleisli filterStateZipper
    <+> (Kleisli zoomInRtZipper >>> nextStateZ')
    <+> nextStateZ''

  filterStateZipper :: TreeReductionStateZipper syn inh stsyn stinh ta tb -> Maybe (TreeReductionStateZipper syn inh stsyn stinh ta tb)
  filterStateZipper stateZ = case toTree stateZ of
    OutputReduction (RankedTreeState _ _) -> empty
    OutputReduction (StackHeadState _)    -> empty
    StackReduction  (StackTailState _)    -> empty
    StackReduction  StackEmptyState       -> empty
    _                                     -> return stateZ

  nextStateZ''
    =   (Kleisli zoomRightRtZipper >>> nextStateZ')
    <+> (Kleisli zoomOutRtZipper   >>> nextStateZ'')

runSattReduction :: (RankedTree ta, RankedTree tb) =>
  StackAttrTreeTrans syn inh stsyn stinh ta tb -> ta -> tb
runSattReduction trans = render . toTopTree . builder where
  builder = fromMaybe (error "not permitted operation")
    . buildSattReduction (const Just) Nothing trans

  render = fromMaybe (error "unexpected operation")
    . fromTreeReductionState


data ReductionStep syn inh stsyn stinh l
  = OutputSynReductionStep syn   l [Int]
  | StackSynReductionStep  stsyn l [Int]
  | OutputInhReductionStep inh   Int l [Int]
  | StackInhReductionStep  stinh Int l [Int]
  | StackHeadConsDeconstract
  | StackTailConsDeconstract
  deriving (Show, Eq, Ord)

type TreeReductionStep syn inh stsyn stinh t = ReductionStep syn inh stsyn stinh (InputLabelType t)

data ReductionStateStep syn inh stsyn stinh ta la tb lb = ReductionStateStep
  { reductionStepState :: ReductionState syn inh stsyn stinh ta la tb lb
  , reductionStateStep :: ReductionStep syn inh stsyn stinh (RankedTreeLabelWithInitial la)
  } deriving (Eq, Ord)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show stsyn, Show stinh, Show la, Show lb)
  => Show (ReductionStateStep syn inh stsyn stinh ta la tb lb) where
  show (ReductionStateStep state step) = show state <> " =" <> showStep step <> "=> " where
    showStep (OutputSynReductionStep _ l p)   = showStep' l p
    showStep (StackSynReductionStep  _ l p)   = showStep' l p
    showStep (OutputInhReductionStep _ _ l p) = showStep' l p
    showStep (StackInhReductionStep  _ _ l p) = showStep' l p
    showStep StackHeadConsDeconstract         = "HC"
    showStep StackTailConsDeconstract         = "TC"

    showStep' l p = "{" <> show l <> "," <> show (reverse p) <> "}"

data ReductionSteps syn inh stsyn stinh ta la tb lb = ReductionSteps
  { reductionSteps :: [ReductionStateStep syn inh stsyn stinh ta la tb lb]
  , reductionResult :: tb
  } deriving (Eq, Ord)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show stsyn, Show stinh, Show la, Show lb, Show tb)
  => Show (ReductionSteps syn inh stsyn stinh ta la tb lb) where
  show (ReductionSteps steps res) = intercalate "" (map show steps) <> " " <> show res

type TreeReductionSteps syn inh stsyn stinh ta tb = ReductionSteps syn inh stsyn stinh ta (LabelType ta) tb (LabelType tb)

buildStepFromOutputAttrState :: l -> ReductionOutputAttrState syn inh -> ReductionStep syn inh stsyn stinh l
buildStepFromOutputAttrState l = go where
  go (OutputSynAttrState a p)      = OutputSynReductionStep a l p
  go (OutputInhAttrState a (x:xs)) = OutputInhReductionStep a x l xs
  go (OutputInhAttrState _ [])     = error "output inherited attribute is empty..."

buildStepFromStackAttrState :: l -> ReductionStackAttrState stsyn stinh -> ReductionStep syn inh stsyn stinh l
buildStepFromStackAttrState l = go where
  go (StackSynAttrState a p)      = StackSynReductionStep a l p
  go (StackInhAttrState a (x:xs)) = StackInhReductionStep a x l xs
  go (StackInhAttrState _ [])     = error "stack inherited attribute is empty..."


buildSattReductionSteps :: (RankedTree ta, RankedTree tb) =>
  StackAttrTreeTrans syn inh stsyn stinh ta tb -> ta -> TreeReductionSteps syn inh stsyn stinh ta tb
buildSattReductionSteps trans = buildSteps . buildSattReduction builder ([], Nothing) trans where
  buildSteps = uncurry ReductionSteps <<< reverse *** render

  builder (steps, Just sz) stateZ = (buildStepFromStateZ sz : steps, Just stateZ)
  builder (steps, Nothing) stateZ = (steps, Just stateZ)

  buildStepFromStateZ stateZ =
    let stateStep = case toTree stateZ of
          OutputReduction (OutputAttrState taZ outputAttrState) ->
            buildStepFromOutputAttrState (getTreeLabel taZ) outputAttrState
          StackReduction (StackAttrState taZ stackAttrState) ->
            buildStepFromStackAttrState (getTreeLabel taZ) stackAttrState
          StackReduction (StackConsState _ _) -> case toTree <$> zoomOutRtZipper stateZ of
            Just (OutputReduction (StackHeadState _)) -> StackHeadConsDeconstract
            Just (StackReduction  (StackTailState _)) -> StackTailConsDeconstract
            _ -> error "unexpected operation"
          _ -> error "unexpected operation"
    in ReductionStateStep (toTopTree stateZ) stateStep

  render mstateZ = fromMaybe (error "unexpected operation") $ do
    stateZ <- mstateZ
    let state = toTopTree stateZ

    fromTreeReductionState state


-- tree transducer

instance TreeTransducer (StackAttrTreeTrans syn inh stsyn stinh) where
  treeTrans = runSattReduction

-- instances

fromAttrTreeTrans :: ATT.AttrTreeTrans syn inh ta tb -> StackAttrTreeTrans syn inh stsyn stinh ta tb
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
    toOutputAttr (ATT.LabelSide l ts)  = LabelSide l [toOutputAttr t | t <- ts]

    ouSynRule a   l = toOutputAttr $ ATT.synthesizedRule trans a l
    ouInhRule a i l = toOutputAttr $ ATT.inheritedRule trans a i l

    stSynRule _   _ = error "not supported stack attributes"
    stInhRule _ _ _ = error "not supported stack attributes"


data OutputSynAttrUnit = OutputSynAttrUnit
  deriving (Eq, Ord)

instance Show OutputSynAttrUnit where
  show _ = "a0"

data StackInhAttrUnit = StackInhAttrUnit
  deriving (Eq, Ord)

instance Show StackInhAttrUnit where
  show _ = "s"

postfixToInfixTransducer :: StackAttrTreeTrans OutputSynAttrUnit Void Void StackInhAttrUnit PostfixOpTree InfixOpTree
postfixToInfixTransducer = StackAttrTreeTrans
  { initialAttr           = a0
  , outputSynthesizedRule = ouSynRule
  , outputInheritedRule   = ouInhRule
  , stackSynthesizedRule  = stSynRule
  , stackInheritedRule    = stInhRule
  }
  where
    a0 = OutputSynAttrUnit
    s  = StackInhAttrUnit

    one         = LabelSide "one"   []
    two         = LabelSide "two"   []
    plus a1 a2  = LabelSide "plus"  [a1, a2]
    multi a1 a2 = LabelSide "multi" [a1, a2]

    ouSynRule _ InitialLabel              = OutputSynAttrSide a0 1
    ouSynRule _ (RankedTreeLabel "one")   = OutputSynAttrSide a0 1
    ouSynRule _ (RankedTreeLabel "two")   = OutputSynAttrSide a0 1
    ouSynRule _ (RankedTreeLabel "plus")  = OutputSynAttrSide a0 1
    ouSynRule _ (RankedTreeLabel "multi") = OutputSynAttrSide a0 1
    ouSynRule _ (RankedTreeLabel "$")     = StackHeadSide
      (StackInhAttrSide s)
    ouSynRule _ l                         = error $ "unsupported label: " ++ show l

    ouInhRule _ i l = error $ "unsupported label: (" <> show i <> "," <> show l <> ")"

    stSynRule _ l = error $ "unsupported label: " <> show l

    stInhRule _ 1 InitialLabel              = StackEmptySide
    stInhRule _ 1 (RankedTreeLabel "one")   = StackConsSide one $ StackInhAttrSide s
    stInhRule _ 1 (RankedTreeLabel "two")   = StackConsSide two $ StackInhAttrSide s
    stInhRule _ 1 (RankedTreeLabel "plus")  = StackConsSide
      (plus
        (StackHeadSide (StackTailSide (StackInhAttrSide s)))
        (StackHeadSide (StackInhAttrSide s)))
      (StackTailSide
        (StackTailSide (StackInhAttrSide s)))
    stInhRule _ 1 (RankedTreeLabel "multi") = StackConsSide
      (multi
        (StackHeadSide (StackTailSide (StackInhAttrSide s)))
        (StackHeadSide (StackInhAttrSide s)))
      (StackTailSide
        (StackTailSide (StackInhAttrSide s)))
    stInhRule _ i l                         = error $ "unsupported label: (" <> show i <> "," <> show l <> ")"
