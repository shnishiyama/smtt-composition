{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedLists   #-}

module Data.SATT.ATT
  (
    -- common
    InputLabelType
  , InputRankedTree
  , InputRankedTreeZipper
  , RightHandSide(..)
  , TreeRightHandSide
  , SynthesizedRuleType
  , InheritedRuleType
  , AttrTreeTrans(..)

    -- reduction state
  , ReductionAttrState(..)
  , initialAttReductionState
  , ReductionState(..)
  , TreeReductionState
  , fromTreeReductionState
  , ReductionStateLabel(..)
  , TreeReductionStateLabel

    -- reduction system
  , buildAttReduction
  , runAttReduction
  , ReductionStep(..)
  , TreeReductionStep
  , ReductionStateStep(..)
  , ReductionSteps(..)
  , TreeReductionSteps
  , buildAttReductionSteps
  , buildAttReductionSteps'

    -- bottom label
  , bottomLabelSide

    -- instances
  , SynAttrUnit(..)
  , InhAttrUnit(..)
  , identityTransducer
  , orderExchangeTransducer
  , infixToPostfixTransducer
  ) where

import ClassyPrelude

import Control.Arrow
import Data.Universe.Class
import Data.Universe.Instances
import qualified Data.Vector as V

import Data.Tree.RankedTree
import Data.Tree.RankedTree.Zipper
import Data.Tree.RankedTree.Transducer

-- common

type RTZipperWithInitial t l = RTZipper (RankedTreeWithInitial t l) (RankedTreeLabelWithInitial t l)

type InputLabelType t = RtApply RankedTreeLabelWithInitial t
type InputRankedTree t = RtApply RankedTreeWithInitial t
type InputRankedTreeZipper t = RTZipperWithInitial t (LabelType t)

data RightHandSide syn inh t l
  = SynAttrSide syn RankNumber
  | InhAttrSide inh
  | LabelSide l (NodeVec :$ RightHandSide syn inh t l)
  deriving (Show, Eq, Ord)

type TreeRightHandSide syn inh t = RtApply (RightHandSide syn inh) t

type SynthesizedRuleType syn inh ta tb =
  syn -> InputLabelType ta ->
    TreeRightHandSide syn inh tb

type InheritedRuleType syn inh ta tb =
  inh -> RankNumber -> InputLabelType ta ->
    TreeRightHandSide syn inh tb

-- | Attributed Tree Transducer
data AttrTreeTrans syn inh ta tb = AttrTreeTrans
  { initialAttr     :: syn
  , synthesizedRule :: SynthesizedRuleType syn inh ta tb
  , inheritedRule   :: InheritedRuleType syn inh ta tb
  }


-- reduction states

data ReductionAttrState syn inh
  = SynAttrState syn [RankNumber]
  | InhAttrState inh [RankNumber]
  deriving (Eq, Ord)

instance (Show syn, Show inh) => Show (ReductionAttrState syn inh) where
  show (SynAttrState a p) = show a <> show (reverse p)
  show (InhAttrState a p) = show a <> show (reverse p)

data ReductionState syn inh ta la tb lb
  = AttrState (RTZipperWithInitial ta la) (ReductionAttrState syn inh)
  | RankedTreeState lb (NodeVec :$ ReductionState syn inh ta la tb lb)
  deriving (Eq, Ord)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show lb)
  => Show (ReductionState syn inh ta la tb lb) where
  show = showTree

type TreeReductionState syn inh ta tb = ReductionState syn inh ta (LabelType ta) tb (LabelType tb)

fromTreeReductionState :: RankedTree tb => TreeReductionState syn inh ta tb -> Maybe tb
fromTreeReductionState (RankedTreeState l ss) = pure (mkTree l) <*> traverse fromTreeReductionState ss
fromTreeReductionState _                      = empty

initialAttReductionState :: AttrTreeTrans syn inh ta tb -> ReductionAttrState syn inh
initialAttReductionState AttrTreeTrans{ initialAttr = a0 } = SynAttrState a0 []


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

  treeChilds (AttrState _ _)        = empty
  treeChilds (RankedTreeState _ ts) = ts

  treeLabelRank _ (AttrStateLabel _ _)     = 0
  treeLabelRank _ (RankedTreeStateLabel l) = treeLabelRank (treeTag :: TreeTag tb) l

  mkTreeUnchecked (AttrStateLabel z s)     _  = AttrState z s
  mkTreeUnchecked (RankedTreeStateLabel l) ts = RankedTreeState l ts

applyRHSToState :: (RankedTree ta, RankedTree tb)
  => TreeRightHandSide syn inh tb
  -> InputRankedTreeZipper ta -> [RankNumber]
  -> TreeReductionState syn inh ta tb
applyRHSToState rhs z p = go rhs where
  go (SynAttrSide a i) = go' $ SynAttrState a (i:p)
  go (InhAttrSide a)   = go' $ InhAttrState a p
  go (LabelSide l cs)  = RankedTreeState l $ go <$> cs

  go' state = AttrState (nextTz state z) state

  nextTz attrState tz = fromMaybe tz $ nextTz' attrState tz

  nextTz' (InhAttrState _ _)     = zoomOutRtZipper
  nextTz' (SynAttrState _ [])    = zoomInRtZipper
  nextTz' (SynAttrState _ (n:_)) = zoomInIdxRtZipper n

type TreeReductionStateZipper syn inh ta tb
  = RTZipper (TreeReductionState syn inh ta tb) (TreeReductionStateLabel syn inh ta tb)


-- reduction systems

buildAttReduction :: forall b syn inh ta tb. (RankedTree ta, RankedTree tb) =>
  (b -> TreeReductionStateZipper syn inh ta tb -> b)
  -> b
  -> ReductionAttrState syn inh
  -> AttrTreeTrans syn inh ta tb
  -> InputRankedTree ta -> b
buildAttReduction f s is AttrTreeTrans{..} t = goTop s
  where
    applyAttrToState tz attrState =
      let l        = treeLabel $ toTree tz
          (rhs, p) = applyAttrToRule l attrState
      in applyRHSToState rhs tz p

    applyAttrToRule l (SynAttrState a p) =
      (synthesizedRule a l, p)
    applyAttrToRule l (InhAttrState a (x:xs)) =
      (inheritedRule a x l, xs)
    applyAttrToRule _ _ = error "inherited attr is empty..."

    goTop state =
      let taZ      = rtZipper t
          stateZ   = rtZipper $ AttrState taZ is
      in case is of
        InhAttrState _ [] -> f state stateZ
        _                 -> go' state stateZ

    go !state stateZ = case nextStateZ stateZ of
        Nothing      -> f state stateZ
        Just nstateZ -> go' state nstateZ

    go' state stateZ =
      let nstate  = f state stateZ
          stateZ' = reductState stateZ $ toTree stateZ
      in go nstate stateZ'

    reductState stZ (AttrState taZ attrState) = setTreeZipper (applyAttrToState taZ attrState) stZ
    reductState _   _                         = error "not permitted operation"

    nextStateZ = runKleisli nextStateZ'

    nextStateZ'
      =   Kleisli filterStateZipper
      <+> (Kleisli zoomInRtZipper >>> nextStateZ')
      <+> nextStateZ''

    filterStateZipper stateZ = case toTree stateZ of
      RankedTreeState _ _             -> empty
      AttrState _ (InhAttrState _ []) -> empty
      _                               -> pure stateZ

    nextStateZ''
      =   (Kleisli zoomRightRtZipper >>> nextStateZ')
      <+> (Kleisli zoomOutRtZipper   >>> nextStateZ'')

runAttReduction :: (RankedTree ta, RankedTree tb)
  => ReductionAttrState syn inh -> AttrTreeTrans syn inh ta tb
  -> InputRankedTree ta -> TreeReductionState syn inh ta tb
runAttReduction is trans t = toTopTree $ builder t where
  initialStateZ = rtZipper $ AttrState (rtZipper t) is

  builder = buildAttReduction (const id) initialStateZ is trans

data ReductionStep syn inh t l
  = SynReductionStep syn l [RankNumber]
  | InhReductionStep inh RankNumber l [RankNumber]
  deriving (Show, Eq, Ord)

type TreeReductionStep syn inh t = RtApply (ReductionStep syn inh) t

data ReductionStateStep syn inh ta la tb lb = ReductionStateStep
  { reductionStepState :: ReductionState syn inh ta la tb lb
  , reductionStateStep :: ReductionStep syn inh (RankedTreeWithInitial ta la) (RankedTreeLabelWithInitial ta la)
  } deriving (Eq, Ord)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show la, Show lb)
  => Show (ReductionStateStep syn inh ta la tb lb) where
    show (ReductionStateStep state step) = show state <> " =" <> showStep step <> "=> "
      where
        showStep (SynReductionStep _ l p)   = showStep' l p
        showStep (InhReductionStep _ _ l p) = showStep' l p

        showStep' l p = "{" <> show l <> "," <> show (reverse p) <> "}"

data ReductionSteps syn inh ta la tb lb = ReductionSteps
  { reductionSteps :: [ReductionStateStep syn inh ta la tb lb]
  , reductionResult :: ReductionState syn inh ta la tb lb
  } deriving (Eq, Ord)

instance (RtConstraint ta la, RtConstraint tb lb, Show syn, Show inh, Show la, Show lb, Show tb)
  => Show (ReductionSteps syn inh ta la tb lb) where
    show (ReductionSteps steps res) = intercalate "" (show <$> steps) <> show res

type TreeReductionSteps syn inh ta tb = RtApply (RtApply (ReductionSteps syn inh) ta) tb

buildStepFromAttrState :: RankedTree t => LabelType t -> ReductionAttrState syn inh -> TreeReductionStep syn inh t
buildStepFromAttrState l = go where
  go (SynAttrState a p)      = SynReductionStep a l p
  go (InhAttrState a (x:xs)) = InhReductionStep a x l xs
  go _                       = error "unexpected operation"

buildAttReductionSteps :: (RankedTree ta, RankedTree tb)
  => ReductionAttrState syn inh
  -> AttrTreeTrans syn inh ta tb
  -> InputRankedTree ta -> TreeReductionSteps syn inh ta tb
buildAttReductionSteps is trans = buildSteps
    . buildAttReduction builder ([], Nothing) is trans
  where
    buildSteps = uncurry ReductionSteps <<< reverse *** (toTree . fromMaybe (error "unexpected operation"))

    builder (steps, Just sz) stateZ = (buildStepFromStateZ sz : steps, Just stateZ)
    builder (steps, Nothing) stateZ = (steps, Just stateZ)

    buildStepFromStateZ stateZ =
      let AttrState taZ attrState = toTree stateZ
      in ReductionStateStep (toTopTree stateZ) $ buildStepFromAttrState (getTreeLabel taZ) attrState

buildAttReductionSteps' :: (RankedTree ta, RankedTree tb)
  => (AttrTreeTrans syn inh ta tb -> ReductionAttrState syn inh)
  -> AttrTreeTrans syn inh ta tb
  -> InputRankedTree ta -> TreeReductionSteps syn inh ta tb
buildAttReductionSteps' f trans = buildAttReductionSteps (f trans) trans

-- tree transducer

instance TreeTransducer (AttrTreeTrans syn inh) where
  treeTrans trans = render . runAttReduction (initialAttReductionState trans) trans . toRankedTreeWithInitial
    where
      render = fromMaybe (error "The input tree transducer is illegal.")
        . fromTreeReductionState

-- bottom label

bottomLabelSide :: RankedTree t => TreeRightHandSide syn inh t
bottomLabelSide = LabelSide bottomLabel []

-- instances

data SynAttrUnit = SynAttrUnit
  deriving (Eq, Ord, Enum, Bounded)

instance Universe SynAttrUnit
instance Finite SynAttrUnit

instance Show SynAttrUnit where
  show _ = "a0"

data InhAttrUnit = InhAttrUnit
  deriving (Eq, Ord, Enum, Bounded)

instance Universe InhAttrUnit
instance Finite InhAttrUnit

instance Show InhAttrUnit where
  show _ = "a1"


identityTransducer :: forall t. (RankedTree t) => AttrTreeTrans SynAttrUnit EmptyType t t
identityTransducer = AttrTreeTrans
    { initialAttr     = a0
    , synthesizedRule = synRule
    , inheritedRule   = inhRule
    }
  where
    a0 = SynAttrUnit

    synRule _ InitialLabel        = SynAttrSide a0 0
    synRule _ (RankedTreeLabel l) = LabelSide l $
      V.generate (treeLabelRank (treeTag :: TreeTag t) l) (SynAttrSide a0)

    inhRule _ _ _ = error "unsupported operation"


orderExchangeTransducer :: forall t. (RankedTree t) => AttrTreeTrans SynAttrUnit EmptyType t t
orderExchangeTransducer = AttrTreeTrans
    { initialAttr     = a0
    , synthesizedRule = synRule
    , inheritedRule   = inhRule
    }
  where
    a0 = SynAttrUnit

    synRule _ InitialLabel        = SynAttrSide a0 0
    synRule _ (RankedTreeLabel l) =
      let k = treeLabelRank (treeTag :: TreeTag t) l
      in LabelSide l $ V.generate k $ SynAttrSide a0 . (k - 1 -)

    inhRule _ _ _ = error "unsupported operation"

infixToPostfixTransducer :: AttrTreeTrans SynAttrUnit InhAttrUnit InfixOpTree PostfixOpTree
infixToPostfixTransducer = AttrTreeTrans
    { initialAttr     = a0
    , synthesizedRule = synRule
    , inheritedRule   = inhRule
    }
  where
    a0 = SynAttrUnit
    a1 = InhAttrUnit

    one   a = LabelSide "one"   [a]
    two   a = LabelSide "two"   [a]
    plus  a = LabelSide "plus"  [a]
    multi a = LabelSide "multi" [a]
    end     = LabelSide "$"     []

    synRule _ InitialLabel              = SynAttrSide a0 0
    synRule _ (RankedTreeLabel "one")   = one $ InhAttrSide a1
    synRule _ (RankedTreeLabel "two")   = two $ InhAttrSide a1
    synRule _ (RankedTreeLabel "plus")  = SynAttrSide a0 0
    synRule _ (RankedTreeLabel "multi") = SynAttrSide a0 0
    synRule _ l                         = error $ "unsupported label: " <> show l

    inhRule _ 0 InitialLabel              = end
    inhRule _ 0 (RankedTreeLabel "plus")  = SynAttrSide a0 1
    inhRule _ 1 (RankedTreeLabel "plus")  = plus $ InhAttrSide a1
    inhRule _ 0 (RankedTreeLabel "multi") = SynAttrSide a0 1
    inhRule _ 1 (RankedTreeLabel "multi") = multi $ InhAttrSide a1
    inhRule _ i l                         = error $ "unsupported label: (" <> show i <> "," <> show l <> ")"
