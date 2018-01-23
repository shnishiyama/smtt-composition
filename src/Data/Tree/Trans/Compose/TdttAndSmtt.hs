{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Tree.Trans.Compose.TdttAndSmtt where

import           SattPrelude

import           Data.Bifunctor.FixLR
import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import           Data.Tree.RankedTree.Zipper
import qualified Data.Tree.Trans.MAC         as MAC
import qualified Data.Tree.Trans.SMAC        as SMAC
import           Data.Tree.Trans.Stack
import qualified Data.Tree.Trans.TOP         as TOP
import qualified Data.Vector                 as V


data ComposedSmttState s1 s2 = ComposedSmttState s1 s2
  deriving (Eq, Ord, Show, Generic, Hashable)

instance RankedLabel s2 => RankedLabel (ComposedSmttState s1 s2) where
  labelRank (ComposedSmttState _ s2) = labelRank s2

type ComposedSmttRHS s1 s2 to2 lo2 = SMAC.BiRightHandSide
  (ComposedSmttState s1 s2)
  to2 lo2



data BasePseudoReductionStateValF c u sa sb ta la tb lb val stk
  = BasePsSmttLabelSideF lb (NodeVec val)
  deriving (Eq, Ord, Show, Generic, Hashable)

deriveEq2 ''BasePseudoReductionStateValF
deriveOrd2 ''BasePseudoReductionStateValF
deriveShow2 ''BasePseudoReductionStateValF
deriveBifunctor ''BasePseudoReductionStateValF
deriveBifoldable ''BasePseudoReductionStateValF

type PseudoReductionStateValF c u sa sb ta la tb lb
  = BasePseudoReductionStateValF c u sa sb ta la tb lb :+|+: StackExprValF

pattern PsSmttLabelSideF :: lb -> NodeVec val -> PseudoReductionStateValF c u sa sb ta la tb lb val stk
pattern PsSmttLabelSideF l cs = BiInL (BasePsSmttLabelSideF l cs)

pattern PsSmttStackBottomF :: PseudoReductionStateValF c u sa sb ta la tb lb val stk
pattern PsSmttStackBottomF = BiInR StackBottomF

pattern PsSmttStackHeadF :: stk -> PseudoReductionStateValF c u sa sb ta la tb lb val stk
pattern PsSmttStackHeadF s = BiInR (StackHeadF s)

{-# COMPLETE PsSmttLabelSideF, PsSmttStackBottomF, PsSmttStackHeadF #-}

data BasePseudoReductionStateStkF c u sa sb ta la tb lb val stk
  = BasePsSmttContextF c
  | BasePsSmttStateF sa ta (NodeVec stk)
  | BasePsSmttStateSideF sb u (NodeVec stk)
  deriving (Eq, Ord, Show, Generic, Hashable)

deriveEq2 ''BasePseudoReductionStateStkF
deriveOrd2 ''BasePseudoReductionStateStkF
deriveShow2 ''BasePseudoReductionStateStkF
deriveBifunctor ''BasePseudoReductionStateStkF
deriveBifoldable ''BasePseudoReductionStateStkF

type PseudoReductionStateStkF c u sa sb ta la tb lb
  = BasePseudoReductionStateStkF c u sa sb ta la tb lb :+|+: StackExprStkF

pattern PsSmttContextF :: c -> PseudoReductionStateStkF c u sa sb ta la tb lb val stk
pattern PsSmttContextF c = BiInL (BasePsSmttContextF c)

pattern PsSmttStateF :: sa -> ta -> NodeVec stk -> PseudoReductionStateStkF c u sa sb ta la tb lb val stk
pattern PsSmttStateF s t cs = BiInL (BasePsSmttStateF s t cs)

pattern PsSmttStateSideF :: sb -> u -> NodeVec stk -> PseudoReductionStateStkF c u sa sb ta la tb lb val stk
pattern PsSmttStateSideF s u cs = BiInL (BasePsSmttStateSideF s u cs)

pattern PsSmttStackEmptyF :: PseudoReductionStateStkF c u sa sb ta la tb lb val stk
pattern PsSmttStackEmptyF = BiInR StackEmptyF

pattern PsSmttStackTailF :: stk -> PseudoReductionStateStkF c u sa sb ta la tb lb val stk
pattern PsSmttStackTailF s = BiInR (StackTailF s)

pattern PsSmttStackConsF :: val -> stk -> PseudoReductionStateStkF c u sa sb ta la tb lb val stk
pattern PsSmttStackConsF v s = BiInR (StackConsF v s)

{-# COMPLETE PsSmttContextF, PsSmttStateF, PsSmttStackEmptyF, PsSmttStackTailF, PsSmttStackConsF #-}

type PseudoReductionStateVal c u sa sb ta la tb lb = FixVal
  (PseudoReductionStateValF c u sa sb ta la tb lb)
  (PseudoReductionStateStkF c u sa sb ta la tb lb)

type PseudoReductionStateStk c u sa sb ta la tb lb = FixStk
  (PseudoReductionStateValF c u sa sb ta la tb lb)
  (PseudoReductionStateStkF c u sa sb ta la tb lb)

type PseudoReductionState c u sa sb ta la tb lb = BiStackExprFix
  (PseudoReductionStateValF c u sa sb ta la tb lb)
  (PseudoReductionStateStkF c u sa sb ta la tb lb)

instance RankedTree (PseudoReductionState c u sa sb ta la tb lb) where
  type LabelType (PseudoReductionState c u sa sb ta la tb lb) = StackExprEither
    (PseudoReductionStateValF c u sa sb ta la tb lb () ())
    (PseudoReductionStateStkF c u sa sb ta la tb lb () ())

  treeLabel (BiFixVal x) = ValuedExpr  $ bivoid x
  treeLabel (BiFixStk x) = StackedExpr $ bivoid x

  treeChilds (BiFixVal x) = fromList $ biList $ bimap ValuedExpr StackedExpr x
  treeChilds (BiFixStk x) = fromList $ biList $ bimap ValuedExpr StackedExpr x

  treeLabelRank _ (ValuedExpr  x) = bilength x
  treeLabelRank _ (StackedExpr x) = bilength x

  mkTreeUnchecked e cs = case e of
      ValuedExpr ve -> BiFixVal $ case ve of
        PsSmttLabelSideF l _ -> PsSmttLabelSideF l $ fromValuedExpr <$> cs
        PsSmttStackBottomF   -> PsSmttStackBottomF
        PsSmttStackHeadF{}   -> PsSmttStackHeadF (fromStackedExpr $ cs `indexEx` 0)
      StackedExpr se -> BiFixStk $ case se of
        PsSmttContextF c    -> PsSmttContextF c
        PsSmttStateF s u _  -> PsSmttStateF s u $ fromStackedExpr <$> cs
        PsSmttStackEmptyF   -> PsSmttStackEmptyF
        PsSmttStackTailF{}  -> PsSmttStackTailF (fromStackedExpr $ cs `indexEx` 0)
        PsSmttStackConsF{}  -> PsSmttStackConsF
          (fromValuedExpr  $ cs `indexEx` 0)
          (fromStackedExpr $ cs `indexEx` 1)
    where
      fromValuedExpr (ValuedExpr x) = x
      fromValuedExpr _              = error "expected a valued expression"

      fromStackedExpr (StackedExpr x) = x
      fromStackedExpr _               = error "expected a stacked expression"


type ComposeBasedPsSmttInputTree s1 to1 lo1
  = TOP.RightHandSide s1 to1 lo1

type ComposeBasedPsSmttOutputTree s1 s2 to2 lo2
  = ComposedSmttRHS s1 s2 to2 lo2

newtype ComposeBasedPseudoSmtt s ta la tb lb = ComposeBasedPseudoSmtt
  (SMAC.StackMacroTreeTransducer s ta la tb lb)

type ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2
  = PseudoReductionState RankNumber RankNumber s2 (ComposedSmttState s1 s2)
    (ComposeBasedPsSmttInputTree s1 to1 lo1) (LabelType (ComposeBasedPsSmttInputTree s1 to1 lo1))
    to2 lo2

buildPseudoSmttReduction :: forall tz b s1 s2 to1 lo1 ti2 li2 to2 lo2.
  ( Eq s1, Hashable s1, RtConstraint to1 lo1
  , to1 ~ ti2
  , SMAC.SmttConstraint s2 ti2 li2 to2 lo2
  , RankedTreeZipper tz
  )
  => (RtApply tz (ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2) -> b -> b)
  -> b
  -> ComposeBasedPseudoSmtt s2 ti2 li2 to2 lo2
  -> ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2
  -> b
buildPseudoSmttReduction f is (ComposeBasedPseudoSmtt trans) = undefined f is trans

runPseudoSmttReduction :: forall s1 s2 to1 lo1 ti2 li2 to2 lo2.
  ( Eq s1, Hashable s1, RtConstraint to1 lo1
  , to1 ~ ti2
  , MAC.MttConstraint s2 ti2 li2 to2 lo2
  )
  => ComposeBasedPseudoSmtt s2 ti2 li2 to2 lo2
  -> ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2
  -> ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2
runPseudoSmttReduction trans istate = toTopTree
  $ buildPseudoSmttReduction const (rtZipper istate) trans istate

fromReductionState ::
  ( SMAC.SmttConstraint s2 ti2 li2 to2 lo2
  , to1 ~ ti2
  )
  => ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2
  -> Maybe (ComposeBasedPsSmttOutputTree s1 s2 to2 lo2)
fromReductionState x = case x of
    ValuedExpr  x' -> ValuedExpr <$> fromReductionStateVal x'
    StackedExpr x' -> StackedExpr <$> fromReductionStateStk x'
  where
    fromReductionStateVal (FixVal x') = case x' of
      PsSmttLabelSideF l cs -> do
        cs' <- traverse fromReductionStateVal cs
        pure $ SMAC.SmttLabelSide l cs'
      PsSmttStackBottomF    -> pure SMAC.SmttStackBottom
      PsSmttStackHeadF s    -> SMAC.SmttStackHead <$> fromReductionStateStk s

    fromReductionStateStk (FixStk x') = case x' of
      PsSmttContextF c        -> pure $ SMAC.SmttContext c
      PsSmttStateSideF g u cs -> do
        cs' <- traverse fromReductionStateStk cs
        pure $ SMAC.SmttState g u cs'
      PsSmttStackEmptyF       -> pure SMAC.SmttStackEmpty
      PsSmttStackTailF s      -> SMAC.SmttStackTail <$> fromReductionStateStk s
      PsSmttStackConsF v s    -> SMAC.SmttStackCons
        <$> fromReductionStateVal v
        <*> fromReductionStateStk s
      PsSmttStateF{}          -> Nothing


type ComposedSmtt s1 s2 ti to = SMAC.SmttTransducer
  (ComposedSmttState s1 s2)
  ti to

-- | composition of a tdtt and a smtt
--
-- Examples:
-- >>> import Data.Tree.RankedTree.Label
-- >>> import Data.Tree.RankedTree.Instances
-- >>> import qualified Data.Tree.Trans.TOP.Instances as TOP
-- >>> import Data.Tree.Trans.SMAC.Instances
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> traUniverse = setFromList $ taggedRankedAlphabetUniverse Proxy
-- >>> identInputTrans = TOP.identityTransducer @InputSampleTree traUniverse
-- >>> identSampleTrans = composeTdttAndSmtt identInputTrans sampleSmtt
-- >>> treeTrans identSampleTrans inputSampleTree
-- D(F,F)
--
composeTdttAndSmtt :: forall s1 s2 ti1 li1 to1 lo1 ti2 li2 to2 lo2.
  ( TOP.TdttConstraint s1 ti1 li1 to1 lo1
  , to1 ~ ti2
  , SMAC.SmttConstraint s2 ti2 li2 to2 lo2
  , Show lo2, Show s2, Show s1, Show lo1, Show li1
  )
  => TOP.TopDownTreeTransducer s1 ti1 li1 to1 lo1
  -> SMAC.StackMacroTreeTransducer s2 ti2 li2 to2 lo2
  -> ComposedSmtt s1 s2 ti1 to2
composeTdttAndSmtt trans1 trans2 = fromMaybe errorUnreachable
    $ SMAC.buildSmtt ie rules
  where
    composeBasedPseudoSmtt = coerce trans2

    runRedComposeBased = fromMaybe errorUnreachable
      . fromReductionState
      . runPseudoSmttReduction composeBasedPseudoSmtt

    runReductionWithRep istate = case runRedComposeBased istate of
        StackedExpr rhs' -> rhs'
        ValuedExpr  rhs' -> SMAC.SmttStackCons rhs' SMAC.SmttStackEmpty

    fromInitialExprVal t x = FixVal $ case x of
      SMAC.SmttLabelSide l cs -> PsSmttLabelSideF l $ fromInitialExprVal t <$> cs
      SMAC.SmttStackBottom    -> PsSmttStackBottomF
      SMAC.SmttStackHead s    -> PsSmttStackHeadF (fromInitialExprStk t s)

    fromInitialExprStk t x = FixStk $ case x of
      SMAC.SmttState g _ cs  -> PsSmttStateF g t $ fromInitialExprStk t <$> cs
      SMAC.SmttContext c     -> PsSmttContextF c
      SMAC.SmttStackEmpty    -> PsSmttStackEmptyF
      SMAC.SmttStackTail s   -> PsSmttStackTailF $ fromInitialExprStk t s
      SMAC.SmttStackCons v s -> PsSmttStackConsF (fromInitialExprVal t v) (fromInitialExprStk t s)

    ie = runReductionWithRep $ StackedExpr
      $ fromInitialExprStk (TOP.tdttInitialExpr trans1) (SMAC.smttInitialExpr trans2)

    rules = do
      g <- setToList $ SMAC.smttStates trans2
      let r = labelRank g - 1
      ((f', l), rhs) <- mapToList $ TOP.tdttTransRules trans1
      let f = coerce f'
      pure $ trace ("rule - " <> show f <> "," <> show g <> ": " <> show l)
        ( ComposedSmttState f g
        , l
        , runReductionWithRep
          $ StackedExpr $ FixStk $ PsSmttStateF g rhs
            $ V.generate r
            $ \i -> FixStk $ PsSmttContextF i
        )

