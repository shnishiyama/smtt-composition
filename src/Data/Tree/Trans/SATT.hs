{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedLists   #-}

module Data.SATT.SATT
  (
    -- satt attr tag
    SattAttrTag(..)
  , SattAttrIdentity(..)
  , SattAttrBox(..)
  , outputSattAttrBox
  , outputSattAttrBoxUnsafe
  , stackSattAttrBox
  , stackSattAttrBoxUnsafe

    -- common
  , InputLabelType
  , InputRankedTree
  , InputRankedTreeZipper
  , OutputRightHandSide
  , StackRightHandSide
  , RightHandSide(..)
  , RightHandSideF(..)
  , RightHandSideBox
  , outputRHS
  , stackRHS
  , TreeOutputRightHandSide
  , TreeStackRightHandSide
  , TreeRightHandSide
  , TreeRightHandSideBox
  , OutputSynthesizedRuleType
  , OutputInheritedRuleType
  , StackSynthesizedRuleType
  , StackInheritedRuleType
  , StackAttrTreeTrans(..)

    -- reduction state
  , ReductionAttrState(..)
  , initialSattReductionState
  , ReductionState(..)
  , TreeReductionState
  , fromTreeReductionState
  , ReductionStateLabel(..)

    -- reduction system
  , buildSattReduction
  , runSattReduction
  , ReductionStep(..)
  , TreeReductionStep
  , ReductionStateStep(..)
  , ReductionSteps(..)
  , TreeReductionSteps
  , buildSattReductionSteps
  , buildSattReductionSteps'

    -- from att to satt
  , fromAttrTreeTrans

    -- bottom label
  , bottomLabelSide

    -- instances
  , ATT.SynAttrUnit(..)
  , ATT.InhAttrUnit(..)
  , StSynAttrUnit(..)
  , StInhAttrUnit(..)
  , postfixToInfixTransducer
  ) where

import ClassyPrelude

import Control.Arrow
import Data.Universe.Class
import Data.Universe.Instances
import Data.Coerce
import Data.Profunctor.Unsafe

import qualified Data.SATT.ATT as ATT
import Data.Tree.RankedTree
import Data.Tree.RankedTree.Zipper
import Data.Tree.RankedTree.Transducer

-- attibute kinds

data SattAttrTag
  = OutputAttrTag
  | StackAttrTag
  deriving (Eq, Ord, Show, Enum, Bounded)

type family SattAttrTagLR (tag :: SattAttrTag) = (e :: EitherTag) | e -> tag where
  SattAttrTagLR 'OutputAttrTag = 'LeftTag
  SattAttrTagLR 'StackAttrTag = 'RightTag

type TaggedOutput = SattAttrEither 'OutputAttrTag
type TaggedStack  = SattAttrEither 'StackAttrTag
type SattAttrEither tag = TaggedEither (SattAttrTagLR tag)
type SattAttrEitherBox = TaggedEitherBox

taggedOutput :: o -> TaggedOutput o s
taggedOutput = TaggedLeft

taggedStack :: s -> TaggedStack o s
taggedStack = TaggedRight

taggedOutputBox :: o -> SattAttrEitherBox o s
taggedOutputBox = taggedLeftBox

taggedStackBox :: s -> SattAttrEitherBox o s
taggedStackBox = taggedRightBox

pattern TaggedOutput :: o -> TaggedOutput o s
pattern TaggedOutput x = TaggedLeft x

pattern TaggedStack :: s -> TaggedStack o s
pattern TaggedStack x = TaggedRight x

pattern TaggedOutputBox :: o -> SattAttrEitherBox o s
pattern TaggedOutputBox x = TaggedLeftBox x

pattern TaggedStackBox :: s -> SattAttrEitherBox o s
pattern TaggedStackBox x = TaggedRightBox x

-- common

type RTZipperWithInitial t l = RTZipper (RankedTreeWithInitial t l) (RankedTreeLabelWithInitial t l)

type InputLabelType t = RtApply RankedTreeLabelWithInitial t
type InputRankedTree t = RtApply RankedTreeWithInitial t
type InputRankedTreeZipper t = RTZipperWithInitial t (LabelType t)

type OutputRightHandSide = RightHandSide 'OutputAttrTag
type StackRightHandSide  = RightHandSide 'StackAttrTag

data RightHandSide (tag :: SattAttrTag) syn inh stsyn stinh t l where
  OutputSynAttrSide :: syn -> RankNumber   -> OutputRightHandSide syn inh stsyn stinh t l
  OutputInhAttrSide :: inh                 -> OutputRightHandSide syn inh stsyn stinh t l
  StackSynAttrSide  :: stsyn -> RankNumber -> StackRightHandSide syn inh stsyn stinh t l
  StackInhAttrSide  :: stinh               -> StackRightHandSide syn inh stsyn stinh t l
  LabelSide         :: l -> (NodeVec :$ OutputRightHandSide syn inh stsyn stinh t l)
                        -> OutputRightHandSide syn inh stsyn stinh t l
  StackHeadSide     :: StackRightHandSide syn inh stsyn stinh t l
                        -> OutputRightHandSide syn inh stsyn stinh t l
  StackConsSide     :: OutputRightHandSide syn inh stsyn stinh t l -> StackRightHandSide syn inh stsyn stinh t l
                        -> StackRightHandSide syn inh stsyn stinh t l
  StackTailSide     :: StackRightHandSide syn inh stsyn stinh t l
                        -> StackRightHandSide syn inh stsyn stinh t l
  StackEmptySide    :: StackRightHandSide syn inh stsyn stinh t l

newtype RightHandSideF syn inh stsyn stinh t l tag
  = RightHandSideF (RightHandSide tag syn inh stsyn stinh t l)

type RightHandSideBox syn inh stsyn stinh t l = SattAttrBox (RightHandSideF syn inh stsyn stinh t l)

outputRHS
  :: RightHandSide 'OutputAttrTag syn inh stsyn stinh t l
  -> RightHandSideBox syn inh stsyn stinh t l
outputRHS = OutputSattAttrBox .# RightHandSideF

stackRHS
  :: RightHandSide 'StackAttrTag syn inh stsyn stinh t l
  -> RightHandSideBox syn inh stsyn stinh t l
stackRHS = StackSattAttrBox .# RightHandSideF


type TreeOutputRightHandSide syn inh stsyn stinh t = TreeRightHandSide 'OutputAttrTag syn inh stsyn stinh t
type TreeStackRightHandSide syn inh stsyn stinh t = TreeRightHandSide 'StackAttrTag syn inh stsyn stinh t
type TreeRightHandSide tag syn inh stsyn stinh t = RtApply (RightHandSide tag syn inh stsyn stinh) t
type TreeRightHandSideBox syn inh stsyn stinh t = RightHandSideBox syn inh stsyn stinh t (LabelType t)

type OutputSynthesizedRuleType syn inh stsyn stinh ta tb =
  syn -> InputLabelType ta ->
    TreeOutputRightHandSide syn inh stsyn stinh tb

type OutputInheritedRuleType syn inh stsyn stinh ta tb =
  inh -> RankNumber -> InputLabelType ta ->
    TreeOutputRightHandSide syn inh stsyn stinh tb

type StackSynthesizedRuleType syn inh stsyn stinh ta tb =
  stsyn -> InputLabelType ta ->
    TreeStackRightHandSide syn inh stsyn stinh tb

type StackInheritedRuleType syn inh stsyn stinh ta tb =
  stinh -> RankNumber -> InputLabelType ta ->
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

type OutputReductionAttrState = ReductionAttrState 'OutputAttrTag
type StackReductionAttrState  = ReductionAttrState 'StackAttrTag

data ReductionAttrState (tag :: SattAttrTag) syn inh stsyn stinh where
  OutputSynAttrState :: syn   -> [RankNumber] -> OutputReductionAttrState syn inh stsyn stinh
  OutputInhAttrState :: inh   -> [RankNumber] -> OutputReductionAttrState syn inh stsyn stinh
  StackSynAttrState  :: stsyn -> [RankNumber] -> StackReductionAttrState syn inh stsyn stinh
  StackInhAttrState  :: stinh -> [RankNumber] -> StackReductionAttrState syn inh stsyn stinh

instance (Show syn, Show inh, Show stsyn, Show stinh) => Show (ReductionAttrState tag syn inh stsyn stinh) where
  show (OutputSynAttrState a p) = show a <> show (reverse p)
  show (OutputInhAttrState a p) = show a <> show (reverse p)
  show (StackSynAttrState  a p) = show a <> show (reverse p)
  show (StackInhAttrState  a p) = show a <> show (reverse p)

type ReductionOutputState = ReductionState 'OutputAttrTag
type ReductionStackState  = ReductionState 'StackAttrTag

newtype ReductionStateF syn inh stsyn stinh ta la tb lb tag
  = ReductionStateF (ReductionState tag syn inh stsyn stinh ta la tb lb)

type ReductionStateBox syn inh stsyn stinh ta la tb lb
  = SattAttrBox (ReductionStateF syn inh stsyn stinh ta la tb lb)

outputReductionState
  :: ReductionState 'OutputAttrTag syn inh stsyn stinh ta la tb lb
  -> ReductionStateBox syn inh stsyn stinh ta la tb lb
outputReductionState = OutputSattAttrBox .# ReductionStateF

stackReductionState
  :: ReductionState 'StackAttrTag syn inh stsyn stinh ta la tb lb
  -> ReductionStateBox syn inh stsyn stinh ta la tb lb
stackReductionState = StackSattAttrBox .# ReductionStateF


data ReductionState (tag :: SattAttrTag) syn inh stsyn stinh ta la tb lb where
  AttrState       :: RTZipperWithInitial ta la -> ReductionAttrState tag syn inh stsyn stinh
                      -> ReductionState tag syn inh stsyn stinh ta la tb lb
  RankedTreeState :: lb -> (NodeVec :$ ReductionOutputState syn inh stsyn stinh ta la tb lb)
                      -> ReductionOutputState syn inh stsyn stinh ta la tb lb
  StackHeadState  :: ReductionStackState syn inh stsyn stinh ta la tb lb
                      -> ReductionOutputState syn inh stsyn stinh ta la tb lb
  StackConsState  :: ReductionOutputState syn inh stsyn stinh ta la tb lb
                      -> ReductionStackState syn inh stsyn stinh ta la tb lb
                      -> ReductionStackState syn inh stsyn stinh ta la tb lb
  StackTailState  :: ReductionStackState syn inh stsyn stinh ta la tb lb
                      -> ReductionStackState syn inh stsyn stinh ta la tb lb
  StackEmptyState :: ReductionStackState syn inh stsyn stinh ta la tb lb

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show stsyn, Show stinh, Show lb)
  => Show (ReductionStateBox syn inh stsyn stinh ta la tb lb) where
    show = showTree

type TreeReductionOutputState syn inh stsyn stinh ta tb = TreeReductionState 'OutputAttrTag syn inh stsyn stinh ta tb
type TreeReductionStackState syn inh stsyn stinh ta tb = TreeReductionState 'StackAttrTag syn inh stsyn stinh ta tb
type TreeReductionState tag syn inh stsyn stinh ta tb = RtApply (RtApply (ReductionState tag syn inh stsyn stinh) ta) tb
type TreeReductionStateBox syn inh stsyn stinh ta tb = ReductionStateBox syn inh stsyn stinh ta (LabelType ta) tb (LabelType tb)

fromTreeReductionState :: RankedTree tb => TreeReductionState tag syn inh stsyn stinh ta tb -> Maybe tb
fromTreeReductionState (RankedTreeState l ss) = pure (mkTree l) <*> traverse fromTreeReductionState ss
fromTreeReductionState _                      = empty

initialSattReductionState :: StackAttrTreeTrans syn inh stsyn stinh ta tb -> OutputReductionAttrState syn inh stsyn stinh
initialSattReductionState StackAttrTreeTrans{ initialAttr = a0 } = OutputSynAttrState a0 []


type ReductionOutputStateLabel = ReductionStateLabel 'OutputAttrTag
type ReductionStackStateLabel  = ReductionStateLabel 'StackAttrTag

newtype ReductionStateLabelF syn inh stsyn stinh ta la tb lb tag
  = ReductionStateLabelF (ReductionStateLabel tag syn inh stsyn stinh ta la tb lb)
  deriving (Show)

type ReductionStateLabelBox syn inh stsyn stinh ta la tb lb
  = SattAttrBox (ReductionStateLabelF syn inh stsyn stinh ta la tb lb)

outputReductionStateLabel
  :: ReductionStateLabel 'OutputAttrTag syn inh stsyn stinh ta la tb lb
  -> ReductionStateLabelBox syn inh stsyn stinh ta la tb lb
outputReductionStateLabel = OutputSattAttrBox .# ReductionStateLabelF

stackReductionStateLabel
  :: ReductionStateLabel 'StackAttrTag syn inh stsyn stinh ta la tb lb
  -> ReductionStateLabelBox syn inh stsyn stinh ta la tb lb
stackReductionStateLabel = StackSattAttrBox .# ReductionStateLabelF

data ReductionStateLabel (tag :: SattAttrTag) syn inh stsyn stinh ta la tb lb where
  AttrStateLabel        :: RTZipperWithInitial ta la -> ReductionAttrState tag syn inh stsyn stinh
                            -> ReductionStateLabel tag syn inh stsyn stinh ta la tb lb
  RankedTreeStateLabel  :: lb -> ReductionOutputStateLabel syn inh stsyn stinh ta la tb lb
  StackHeadStateLabel   :: ReductionOutputStateLabel syn inh stsyn stinh ta la tb lb
  StackConsStateLabel   :: ReductionStackStateLabel syn inh stsyn stinh ta la tb lb
  StackTailStateLabel   :: ReductionStackStateLabel syn inh stsyn stinh ta la tb lb
  StackEmptyStateLabel  :: ReductionStackStateLabel syn inh stsyn stinh ta la tb lb

instance (Show syn, Show inh, Show stsyn, Show stinh, Show lb)
  => Show (ReductionStateLabel tag syn inh stsyn stinh ta la tb lb) where
    show (AttrStateLabel _ a)       = show a
    show (RankedTreeStateLabel l)   = show l
    show StackEmptyStateLabel       = "Empty"
    show StackHeadStateLabel        = "Head"
    show StackConsStateLabel        = "Cons"
    show StackTailStateLabel        = "Tail"

instance (Show syn, Show inh, Show stsyn, Show stinh, Show lb)
  => Show (ReductionStateLabelBox syn inh stsyn stinh ta la tb lb) where
    show (OutputSattAttrBox x) = show (coerce x :: ReductionOutputStateLabel syn inh stsyn stinh ta la tb lb)
    show (StackSattAttrBox  x) = show (coerce x :: ReductionStackStateLabel syn inh stsyn stinh ta la tb lb)


type TreeReductionStateLabelBox syn inh stsyn stinh ta tb
  = ReductionStateLabelBox syn inh stsyn stinh ta (LabelType ta) tb (LabelType tb)

instance (RtConstraint ta la, RtConstraint tb lb)
  => RankedTree (ReductionStateBox syn inh stsyn stinh ta la tb lb) where

    type LabelType (ReductionStateBox syn inh stsyn stinh ta la tb lb)
      = ReductionStateLabelBox syn inh stsyn stinh ta la tb lb

    treeLabel s = case s of
        OutputSattAttrBox x -> outputReductionStateLabel . treeLabel' $ coerce x
        StackSattAttrBox  x -> stackReductionStateLabel  . treeLabel' $ coerce x
      where
        treeLabel'
          :: ReductionState tag syn inh stsyn stinh ta la tb lb
          -> ReductionStateLabel tag syn inh stsyn stinh ta la tb lb
        treeLabel' (AttrState z as)      = AttrStateLabel z as
        treeLabel' (RankedTreeState l _) = RankedTreeStateLabel l
        treeLabel' (StackHeadState _)    = StackHeadStateLabel
        treeLabel' (StackConsState _ _)  = StackConsStateLabel
        treeLabel' (StackTailState _)    = StackTailStateLabel
        treeLabel' StackEmptyState       = StackEmptyStateLabel

    treeChilds s = case s of
        OutputSattAttrBox x -> treeChilds' $ coerce x
        StackSattAttrBox  x -> treeChilds' $ coerce x
      where
        treeChilds'
          :: ReductionState tag syn inh stsyn stinh ta la tb lb
          -> (NodeVec :$ ReductionStateBox syn inh stsyn stinh ta la tb lb)
        treeChilds' (AttrState _ _)        = []
        treeChilds' (RankedTreeState _ ts) = outputReductionState <$> ts
        treeChilds' (StackHeadState t)     = [stackReductionState t]
        treeChilds' (StackConsState h t)   = [outputReductionState h, stackReductionState t]
        treeChilds' (StackTailState t)     = [stackReductionState t]
        treeChilds' StackEmptyState        = []

    treeLabelRank _ l = case l of
        OutputSattAttrBox x -> treeLabelRank' $ coerce x
        StackSattAttrBox  x -> treeLabelRank' $ coerce x
      where
        treeLabelRank'
          :: ReductionStateLabel tag syn inh stsyn stinh ta la tb lb -> RankNumber
        treeLabelRank' (AttrStateLabel _ _)      = 0
        treeLabelRank' (RankedTreeStateLabel lb) = treeLabelRank (treeTag :: TreeTag tb) lb
        treeLabelRank' StackHeadStateLabel       = 1
        treeLabelRank' StackConsStateLabel       = 2
        treeLabelRank' StackTailStateLabel       = 1
        treeLabelRank' StackEmptyStateLabel      = 0

    mkTreeUnchecked l = case l of
        OutputSattAttrBox x -> outputReductionState . mkTreeUnchecked' (coerce x)
        StackSattAttrBox  x -> stackReductionState  . mkTreeUnchecked' (coerce x)
      where
        mkTreeUnchecked'
          :: ReductionStateLabel tag syn inh stsyn stinh ta la tb lb
          -> (NodeVec :$ ReductionStateBox syn inh stsyn stinh ta la tb lb)
          -> ReductionState tag syn inh stsyn stinh ta la tb lb
        mkTreeUnchecked' (AttrStateLabel z s)      _  = AttrState z s
        mkTreeUnchecked' (RankedTreeStateLabel lb) ts = RankedTreeState lb ts'
          where
            ts' = coerce $ outputSattAttrBoxUnsafe <$> ts

        mkTreeUnchecked' StackHeadStateLabel       ts = StackHeadState t'
          where
            t' = coerce $ stackSattAttrBoxUnsafe $ ts ! 0

        mkTreeUnchecked' StackConsStateLabel       ts = StackConsState t1' t2'
          where
            (t1', t2') = coerce (outputSattAttrBoxUnsafe $ ts ! 0, stackSattAttrBoxUnsafe $ ts ! 1)

        mkTreeUnchecked' StackTailStateLabel       ts = StackTailState t'
          where
            t' = coerce $ stackSattAttrBoxUnsafe $ ts ! 0

        mkTreeUnchecked' StackEmptyStateLabel      _  = StackEmptyState

applyRHSToState :: forall tag syn inh stsyn stinh ta tb.
  (RankedTree ta, RankedTree tb)
  => TreeRightHandSide tag syn inh stsyn stinh tb
  -> InputRankedTreeZipper ta -> [RankNumber]
  -> TreeReductionState tag syn inh stsyn stinh ta tb
applyRHSToState rhs z p = go rhs where
  go :: TreeRightHandSide tg syn inh stsyn stinh tb -> TreeReductionState tg syn inh stsyn stinh ta tb
  go (OutputSynAttrSide a i)   = go' $ OutputSynAttrState a (i:p)
  go (OutputInhAttrSide a)     = go' $ OutputInhAttrState a p
  go (StackSynAttrSide  a i)   = go' $ StackSynAttrState  a (i:p)
  go (StackInhAttrSide  a)     = go' $ StackInhAttrState  a p
  go (LabelSide l cs)          = RankedTreeState l $ go <$> cs
  go (StackHeadSide srhs)      = StackHeadState $ go srhs
  go (StackConsSide orhs srhs) = StackConsState (go orhs) (go srhs)
  go (StackTailSide srhs)      = StackTailState $ go srhs
  go StackEmptySide            = StackEmptyState

  go' :: ReductionAttrState tg syn inh stsyn stinh -> TreeReductionState tg syn inh stsyn stinh ta tb
  go' state = AttrState (fromMaybe z $ nextTz state z) state

  nextTz :: ReductionAttrState tg syn inh stsyn stinh -> InputRankedTreeZipper ta -> Maybe (InputRankedTreeZipper ta)
  nextTz (OutputInhAttrState _ _)     = zoomOutRtZipper
  nextTz (StackInhAttrState  _ _)     = zoomOutRtZipper
  nextTz (OutputSynAttrState _ [])    = zoomInRtZipper
  nextTz (StackSynAttrState  _ [])    = zoomInRtZipper
  nextTz (OutputSynAttrState _ (n:_)) = zoomInIdxRtZipper n
  nextTz (StackSynAttrState  _ (n:_)) = zoomInIdxRtZipper n

type TreeReductionStateZipper syn inh stsyn stinh ta tb
  = RTZipper (TreeReductionStateBox syn inh stsyn stinh ta tb) (TreeReductionStateLabelBox syn inh stsyn stinh ta tb)


-- reduction systems

buildSattReduction :: forall b syn inh stsyn stinh ta tb.
  (RankedTree ta, RankedTree tb)
  => (b -> TreeReductionStateZipper syn inh stsyn stinh ta tb -> b)
  -> b
  -> OutputReductionAttrState syn inh stsyn stinh
  -> StackAttrTreeTrans syn inh stsyn stinh ta tb
  -> InputRankedTree ta -> b
buildSattReduction f s is StackAttrTreeTrans{..} t = goTop s where
  applyAttrToState
    :: InputRankedTreeZipper ta
    -> ReductionAttrState tag syn inh stsyn stinh
    -> TreeReductionState tag syn inh stsyn stinh ta tb
  applyAttrToState tz attrState =
    let l = treeLabel $ toTree tz
        (rhs, p) = applyAttrToRule l attrState
    in applyRHSToState rhs tz p

  applyAttrToRule
    :: InputLabelType ta
    -> ReductionAttrState tag syn inh stsyn stinh
    -> (TreeRightHandSide tag syn inh stsyn stinh tb, [RankNumber])
  applyAttrToRule l (OutputSynAttrState a p)      =
    (outputSynthesizedRule a l, p)
  applyAttrToRule l (StackSynAttrState  a p)      =
    (stackSynthesizedRule a l, p)
  applyAttrToRule l (OutputInhAttrState a (x:xs)) =
    (outputInheritedRule a x l, xs)
  applyAttrToRule l (StackInhAttrState  a (x:xs)) =
    (stackInheritedRule a x l, xs)
  applyAttrToRule _ _ = error "inherited attr is empty..."

  goTop state =
    let taZ      = rtZipper t
        stateZ   = rtZipper . outputReductionState $ AttrState taZ is
    in go' state stateZ

  go !state stateZ = case nextStateZ stateZ of
      Nothing      -> f state stateZ
      Just nstateZ -> go' state nstateZ

  go' state stateZ =
    let nstate   = f state stateZ
        stateZ' = reductState stateZ $ toTree stateZ
    in go nstate stateZ'

  reductState stZ (OutputSattAttrBox x) = case coerce x of
    AttrState taZ attrState -> setTreeZipper (outputReductionState $ applyAttrToState taZ attrState) stZ
    _                       -> error "not permitted operation"
  reductState stZ (StackSattAttrBox  x) = case coerce x of
    AttrState taZ attrState -> setTreeZipper (stackReductionState $ applyAttrToState taZ attrState) stZ
    StackConsState hd tl    -> deconstractStack hd tl stZ
    _                       -> error "not permitted operation"

  deconstractStack
    :: TreeReductionOutputState syn inh stsyn stinh ta tb
    -> TreeReductionStackState syn inh stsyn stinh ta tb
    -> TreeReductionStateZipper syn inh stsyn stinh ta tb
    -> TreeReductionStateZipper syn inh stsyn stinh ta tb
  deconstractStack hd tl stateZ = case zoomOutRtZipper stateZ of
    Nothing      -> error "not permitted operation"
    Just nstateZ -> case toTree nstateZ of
      OutputSattAttrBox x -> case coerce x of
          StackHeadState _    -> setTreeZipper (outputReductionState hd) nstateZ
          _                   -> error "not permitted operation"

      StackSattAttrBox  x -> case coerce x of
          StackTailState _    -> setTreeZipper (stackReductionState  tl) nstateZ
          _                   -> error "not permitted operation"

  nextStateZ = runKleisli nextStateZ'

  nextStateZ'
    =   Kleisli filterStateZipper
    <+> (Kleisli zoomInRtZipper >>> nextStateZ')
    <+> nextStateZ''

  filterStateZipper stateZ = case toTree stateZ of
    OutputSattAttrBox x -> filterStateZipper' stateZ $ coerce x
    StackSattAttrBox  x -> filterStateZipper' stateZ $ coerce x

  filterStateZipper' :: a -> TreeReductionState tag syn inh stsyn stinh ta tb -> Maybe a
  filterStateZipper' _ (RankedTreeState _ _)                   = empty
  filterStateZipper' _ (StackHeadState _)                      = empty
  filterStateZipper' _ (StackTailState _)                      = empty
  filterStateZipper' _ StackEmptyState                         = empty
  filterStateZipper' _ (AttrState _ (OutputInhAttrState _ [])) = empty
  filterStateZipper' _ (AttrState _ (StackInhAttrState _ []))  = empty
  filterStateZipper' stZ _                                     = pure stZ

  nextStateZ''
    =   (Kleisli zoomRightRtZipper >>> nextStateZ')
    <+> (Kleisli zoomOutRtZipper   >>> nextStateZ'')

runSattReduction :: (RankedTree ta, RankedTree tb)
  => OutputReductionAttrState syn inh stsyn stinh -> StackAttrTreeTrans syn inh stsyn stinh ta tb
  -> InputRankedTree ta -> TreeReductionStateBox syn inh stsyn stinh ta tb
runSattReduction is trans t = toTopTree $ builder t where
  initialStateZ = rtZipper . outputReductionState $ AttrState (rtZipper t) is

  builder = buildSattReduction (const id) initialStateZ is trans


data ReductionStep syn inh stsyn stinh t l
  = OutputSynReductionStep syn   l [RankNumber]
  | StackSynReductionStep  stsyn l [RankNumber]
  | OutputInhReductionStep inh   RankNumber l [RankNumber]
  | StackInhReductionStep  stinh RankNumber l [RankNumber]
  | StackHeadConsDeconstract
  | StackTailConsDeconstract
  deriving (Show, Eq, Ord)

type TreeReductionStep syn inh stsyn stinh t = RtApply (ReductionStep syn inh stsyn stinh) t

data ReductionStateStep syn inh stsyn stinh ta la tb lb = ReductionStateStep
  { reductionStepState :: ReductionStateBox syn inh stsyn stinh ta la tb lb
  , reductionStateStep :: ReductionStep syn inh stsyn stinh (RankedTreeWithInitial ta la) (RankedTreeLabelWithInitial ta la)
  }

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show stsyn, Show stinh, Show la, Show lb)
  => Show (ReductionStateStep syn inh stsyn stinh ta la tb lb) where
    show (ReductionStateStep state step) = show state <> " =" <> showStep step <> "=> "
      where
        showStep (OutputSynReductionStep _ l p)   = showStep' l p
        showStep (StackSynReductionStep  _ l p)   = showStep' l p
        showStep (OutputInhReductionStep _ _ l p) = showStep' l p
        showStep (StackInhReductionStep  _ _ l p) = showStep' l p
        showStep StackHeadConsDeconstract         = "HC"
        showStep StackTailConsDeconstract         = "TC"

        showStep' l p = "{" <> show l <> "," <> show (reverse p) <> "}"

data ReductionSteps syn inh stsyn stinh ta la tb lb = ReductionSteps
  { reductionSteps :: [ReductionStateStep syn inh stsyn stinh ta la tb lb]
  , reductionResult :: ReductionStateBox syn inh stsyn stinh ta la tb lb
  }

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show stsyn, Show stinh, Show la, Show lb)
  => Show (ReductionSteps syn inh stsyn stinh ta la tb lb) where
    show (ReductionSteps steps res) = intercalate "" (show <$> steps) <> show res

type TreeReductionSteps syn inh stsyn stinh ta tb = RtApply (RtApply (ReductionSteps syn inh stsyn stinh) ta) tb

buildStepFromAttrState :: RankedTree t
  => LabelType t -> ReductionAttrState tag syn inh stsyn stinh -> TreeReductionStep syn inh stsyn stinh t
buildStepFromAttrState l = go where
  go (OutputSynAttrState a p)      = OutputSynReductionStep a l p
  go (OutputInhAttrState a (x:xs)) = OutputInhReductionStep a x l xs
  go (StackSynAttrState a p)       = StackSynReductionStep a l p
  go (StackInhAttrState a (x:xs))  = StackInhReductionStep a x l xs
  go _ = error "unexpected operation"

buildSattReductionSteps :: (RankedTree ta, RankedTree tb)
  => OutputReductionAttrState syn inh stsyn stinh
  -> StackAttrTreeTrans syn inh stsyn stinh ta tb
  -> InputRankedTree ta -> TreeReductionSteps syn inh stsyn stinh ta tb
buildSattReductionSteps is trans = buildSteps
    . buildSattReduction builder ([], Nothing) is trans
  where
    buildSteps = uncurry ReductionSteps <<< reverse *** (toTree . fromMaybe (error "unexpected operation"))

    builder (steps, Just sz) stateZ = (buildStepFromStateZ sz : steps, Just stateZ)
    builder (steps, Nothing) stateZ = (steps, Just stateZ)

    buildStepFromStateZ stateZ =
      let stateStep = case toTree stateZ of
            OutputSattAttrBox x -> case coerce x of
              AttrState taZ attrState ->
                buildStepFromAttrState (getTreeLabel taZ) attrState
              _ -> error "unexpected operation"
            StackSattAttrBox  x -> case coerce x of
              AttrState taZ attrState ->
                buildStepFromAttrState (getTreeLabel taZ) attrState
              StackConsState _ _      -> case toTree <$> zoomOutRtZipper stateZ of
                Just (OutputSattAttrBox _) -> StackHeadConsDeconstract
                Just (StackSattAttrBox  _) -> StackTailConsDeconstract
                _                          -> error "unexpected operation"
              _ -> error "unexpected operation"
      in ReductionStateStep (toTopTree stateZ) stateStep

buildSattReductionSteps' :: (RankedTree ta, RankedTree tb)
  => (StackAttrTreeTrans syn inh stsyn stinh ta tb -> OutputReductionAttrState syn inh stsyn stinh)
  -> StackAttrTreeTrans syn inh stsyn stinh ta tb
  -> InputRankedTree ta -> TreeReductionSteps syn inh stsyn stinh ta tb
buildSattReductionSteps' f trans = buildSattReductionSteps (f trans) trans

-- tree transducer

instance TreeTransducer (StackAttrTreeTrans syn inh stsyn stinh) where
  treeTrans trans = render . runSattReduction (initialSattReductionState trans) trans . toRankedTreeWithInitial
    where
      render = fromMaybe (error "The input tree transducer is illegal.")
        . fromTreeReductionStateBox

      fromTreeReductionStateBox :: RankedTree tb => TreeReductionStateBox syn inh stsyn stinh ta tb -> Maybe tb
      fromTreeReductionStateBox (OutputSattAttrBox x) = fromTreeReductionState $ coerce x
      fromTreeReductionStateBox (StackSattAttrBox  x) = fromTreeReductionState $ coerce x

-- bottom label

bottomLabelSide :: RankedTree t => TreeOutputRightHandSide syn inh stsyn stinh t
bottomLabelSide = LabelSide bottomLabel []

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
