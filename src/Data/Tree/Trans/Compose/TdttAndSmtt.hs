{-# LANGUAGE NoStrict        #-}
{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Tree.Trans.Compose.TdttAndSmtt where

import           SmttPrelude

import           Data.Bifunctor.FixLR
import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import           Data.Tree.RankedTree.Zipper
import qualified Data.Tree.Trans.MAC         as MAC
import qualified Data.Tree.Trans.SMAC        as SMAC
import           Data.Tree.Trans.Stack
import qualified Data.Tree.Trans.TOP         as TOP
import qualified Data.Vector                 as V
import qualified Text.PrettyPrint.Classy     as Pretty


data ComposedSmttState s1 s2 = ComposedSmttState s1 s2
  deriving (Eq, Ord, Generic, Hashable)

instance (Show s1, Show s2) => Show (ComposedSmttState s1 s2) where
  show (ComposedSmttState s1 s2) = show (s1, s2)

instance RankedLabel s2 => RankedLabel (ComposedSmttState s1 s2) where
  labelRank (ComposedSmttState _ s2) = labelRank s2

instance (Show s1, Show s2) => Pretty.Pretty (ComposedSmttState s1 s2) where
  pretty (ComposedSmttState s1 s2) = Pretty.tupled
    [Pretty.prettyShowString s1, Pretty.prettyShowString s2]

type ComposedSmttRHS s1 s2 to2 lo2 = SMAC.BiRightHandSide
  (ComposedSmttState s1 s2)
  to2 lo2



data BasePseudoReductionStateValF c u sa sb ta la tb lb val stk
  = BasePsSmttLabelSideF lb (NodeVec val)
  deriving (Eq, Ord, Show, Generic, Generic1, Hashable, Hashable1)

instance Hashable lb => Hashable2 (BasePseudoReductionStateValF c u sa sb ta la tb lb) where
  liftHashWithSalt2 = defaultLiftHashWithSalt2

deriveEq2 ''BasePseudoReductionStateValF
deriveOrd2 ''BasePseudoReductionStateValF
deriveShow2 ''BasePseudoReductionStateValF
deriveBifunctor ''BasePseudoReductionStateValF
deriveBifoldable ''BasePseudoReductionStateValF
deriveBitraversable ''BasePseudoReductionStateValF

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
  deriving (Eq, Ord, Show, Generic, Generic1, Hashable, Hashable1)

instance (Hashable c, Hashable sa, Hashable ta, Hashable sb, Hashable u)
    => Hashable2 (BasePseudoReductionStateStkF c u sa sb ta la tb lb) where

  liftHashWithSalt2 = defaultLiftHashWithSalt2

deriveEq2 ''BasePseudoReductionStateStkF
deriveOrd2 ''BasePseudoReductionStateStkF
deriveShow2 ''BasePseudoReductionStateStkF
deriveBifunctor ''BasePseudoReductionStateStkF
deriveBifoldable ''BasePseudoReductionStateStkF
deriveBitraversable ''BasePseudoReductionStateStkF

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

{-# COMPLETE PsSmttContextF, PsSmttStateF, PsSmttStateSideF, PsSmttStackEmptyF, PsSmttStackTailF, PsSmttStackConsF #-}

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
        PsSmttContextF c        -> PsSmttContextF c
        PsSmttStateF s1 t _     -> PsSmttStateF s1 t $ fromStackedExpr <$> cs
        PsSmttStateSideF s2 u _ -> PsSmttStateSideF s2 u $ fromStackedExpr <$> cs
        PsSmttStackEmptyF       -> PsSmttStackEmptyF
        PsSmttStackTailF{}      -> PsSmttStackTailF (fromStackedExpr $ cs `indexEx` 0)
        PsSmttStackConsF{}      -> PsSmttStackConsF
          (fromValuedExpr  $ cs `indexEx` 0)
          (fromStackedExpr $ cs `indexEx` 1)
    where
      fromValuedExpr (ValuedExpr x) = x
      fromValuedExpr _              = error "expected a valued expression"

      fromStackedExpr (StackedExpr x) = x
      fromStackedExpr _               = error "expected a stacked expression"

instance (Show lb, Show c, Show sa, Show u, Show la, Pretty.Pretty sb, RtConstraint ta la)
    => Pretty.Pretty (PseudoReductionState c u sa sb ta la tb lb) where

  pretty state = case state of
      ValuedExpr  v -> goVal v
      StackedExpr s -> goStk s
    where
      goVal (FixVal x) = case x of
        PsSmttLabelSideF l cs -> Pretty.prettyShowString l <> Pretty.tupled (goVal <$> toList cs)
        PsSmttStackBottomF    -> Pretty.text "_|_"
        PsSmttStackHeadF s    -> Pretty.text "H" <> Pretty.tupled [goStk s]
      goStk (FixStk x) = case x of
        PsSmttStateF     s1 t cs -> Pretty.prettyShowString s1
          <> Pretty.tupled (Pretty.prettyShowString (treeLabel t):(goStk <$> toList cs))
        PsSmttStateSideF s2 u cs -> Pretty.pretty s2
          <> Pretty.tupled (Pretty.prettyShowString u:(goStk <$> toList cs))
        PsSmttStackEmptyF        -> Pretty.text "[]"
        PsSmttStackTailF s       -> Pretty.text "T" <> Pretty.tupled [goStk s]
        PsSmttStackConsF v s     -> Pretty.text "C" <> Pretty.tupled [goVal v, goStk s]
        PsSmttContextF c         -> Pretty.prettyShowString c


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
  , Show b, Show s1, Show s2, Show lo1, Show lo2
  , Show (RtApply tz (ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2))
  )
  => (RtApply tz (ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2) -> b -> b)
  -> b
  -> ComposeBasedPseudoSmtt s2 ti2 li2 to2 lo2
  -> ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2
  -> b
buildPseudoSmttReduction f is (ComposeBasedPseudoSmtt trans) = go is . toZipper
  where
    rule = SMAC.smttTranslateRule trans

    checkReducible (BiFixVal x) = case x of
      PsSmttLabelSideF{}   -> False
      PsSmttStackBottomF{} -> False
      PsSmttStackHeadF{}   -> False
    checkReducible (BiFixStk x) = case x of
      PsSmttStateF{}      -> True
      PsSmttStateSideF{}  -> False
      PsSmttStackEmptyF{} -> True
      PsSmttStackTailF{}  -> False
      PsSmttStackConsF{}  -> True
      PsSmttContextF{}    -> False

    go x sz =
      let
        mres = do
          sz' <- zoomNextRightOutZipper (checkReducible . toTree) sz
          case reductState sz' of
            Just nsz -> pure (f nsz x, nsz)
            Nothing   -> do
              nsz <- zoomNextRightOutZipper1 (const True) sz'
              pure (x, nsz)
      in case mres of
        Just (!nx, !nsz) -> go nx nsz
        Nothing          -> x

    reductState sz = case toTree sz of
      BiFixStk x -> case x of
        PsSmttStateF s t cs  -> pure $ setTreeZipper (reductStateSide s t cs) sz
        PsSmttStackConsF h t -> deconsStackCons h t <=< zoomOutRtZipper $ sz
        PsSmttStackEmptyF    -> deconsStackEmpty <=< zoomOutRtZipper $ sz
        _                    -> error "This state is irreducible"
      BiFixVal _ -> error "This state is irreducible"

    reductStateSide s2 (Fix t) ys = case t of
      TOP.TdttLabelSideF l cs   -> replaceRHS cs ys $ rule (s2, l)
      TOP.TdttStateF s1 u       -> BiFixStk $ PsSmttStateSideF (ComposedSmttState s1 s2) u ys
      TOP.TdttBottomLabelSideF  -> BiFixStk PsSmttStackEmptyF

    deconsStackEmpty sz = case toTree sz of
      BiFixVal x -> case x of
        PsSmttStackHeadF{} -> pure $ setTreeZipper (BiFixVal PsSmttStackBottomF) sz
        _                  -> empty
      BiFixStk x -> case x of
        PsSmttStackTailF{} -> pure $ setTreeZipper (BiFixStk PsSmttStackEmptyF) sz
        _                  -> empty

    deconsStackCons h t sz = case toTree sz of
      BiFixVal x -> case x of
        PsSmttStackHeadF{} -> pure $ setTreeZipper (ValuedExpr h) sz
        _                  -> empty
      BiFixStk x -> case x of
        PsSmttStackTailF{} -> pure $ setTreeZipper (StackedExpr t) sz
        _                  -> empty

    replaceRHS us ys = StackedExpr . replaceRHSStk us ys

    replaceRHSVal us ys (FixVal x) = FixVal $ case x of
      SMAC.SmttLabelSideF l cs -> PsSmttLabelSideF l $ replaceRHSVal us ys <$> cs
      SMAC.SmttStackBottomF    -> PsSmttStackBottomF
      SMAC.SmttStackHeadF s    -> PsSmttStackHeadF $ replaceRHSStk us ys s

    replaceRHSStk us ys (FixStk x) = case x of
      SMAC.SmttContextF yi      -> ys `indexEx` yi
      SMAC.SmttStateF s ui cs   -> FixStk $ PsSmttStateF s (us `indexEx` ui) $ replaceRHSStk us ys <$> cs
      SMAC.SmttStackEmptyF      -> FixStk PsSmttStackEmptyF
      SMAC.SmttStackTailF s     -> FixStk $ PsSmttStackTailF $ replaceRHSStk us ys s
      SMAC.SmttStackConsF v s   -> FixStk $ PsSmttStackConsF
        (replaceRHSVal us ys v)
        (replaceRHSStk us ys s)

runPseudoSmttReduction :: forall s1 s2 to1 lo1 ti2 li2 to2 lo2.
  ( Eq s1, Hashable s1, RtConstraint to1 lo1
  , to1 ~ ti2
  , MAC.MttConstraint s2 ti2 li2 to2 lo2
  , Eq lo2, Hashable lo2
  , Show s1, Show s2, Show lo1, Show lo2
  )
  => ComposeBasedPseudoSmtt s2 ti2 li2 to2 lo2
  -> ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2
  -> ComposeBasedPseudoReductionState s1 s2 to1 lo1 ti2 li2 to2 lo2
runPseudoSmttReduction (ComposeBasedPseudoSmtt trans) = reductState
  where
    rule = SMAC.smttTranslateRule trans

    reductState = bimap repRedVal repRedStk

    stackConsReduct v@(FixVal x) s@(FixStk y) = case (x, y) of
      (PsSmttStackBottomF, PsSmttStackEmptyF) -> s
      _                                       -> FixStk $ PsSmttStackConsF v s

    stackTailReduct s@(FixStk x) = case x of
      PsSmttStackEmptyF     -> s
      PsSmttStackConsF _ s' -> s'
      _                     -> FixStk $ PsSmttStackTailF s

    stackHeadReduct s@(FixStk x) = case x of
      PsSmttStackEmptyF     -> stackBottom
      PsSmttStackConsF v' _ -> v'
      _                     -> FixVal $ PsSmttStackHeadF s

    repRedVal v@(FixVal x) = case x of
      PsSmttStackBottomF    -> v
      PsSmttLabelSideF l cs -> FixVal #. PsSmttLabelSideF l $ fmap repRedVal cs
      PsSmttStackHeadF s'   -> stackHeadReduct $ repRedStk s'

    repRedStk s@(FixStk x) = case x of
      PsSmttStackEmptyF        -> s
      PsSmttContextF{}         -> s
      PsSmttStateF     g t cs  -> stateFunc g t $ fmap repRedStk cs
      PsSmttStateSideF fg u cs -> FixStk #. PsSmttStateSideF fg u $ fmap repRedStk cs
      PsSmttStackTailF s'      -> stackTailReduct $ repRedStk s'
      PsSmttStackConsF v' s'   -> stackConsReduct (repRedVal v') (repRedStk s')

    stateFunc s2 (Fix t) ys = case t of
      TOP.TdttLabelSideF l us  -> replaceRHSStk us ys $ rule (s2, l)
      TOP.TdttStateF s1 u      -> FixStk $ PsSmttStateSideF (ComposedSmttState s1 s2) u ys
      TOP.TdttBottomLabelSideF -> stackEmpty

    replaceRHSVal us ys (FixVal x) = case x of
      SMAC.SmttLabelSideF l cs -> FixVal #. PsSmttLabelSideF l $ fmap (replaceRHSVal us ys) cs
      SMAC.SmttStackBottomF    -> stackBottom
      SMAC.SmttStackHeadF s    -> stackHeadReduct $ replaceRHSStk us ys s

    replaceRHSStk us ys (FixStk x) = case x of
      SMAC.SmttContextF yi      -> ys `indexEx` yi
      SMAC.SmttStateF g ui cs   ->
        let t = us `indexEx` ui
        in stateFunc g t $ fmap (replaceRHSStk us ys) cs
      SMAC.SmttStackEmptyF      -> stackEmpty
      SMAC.SmttStackTailF s     -> stackTailReduct $ replaceRHSStk us ys s
      SMAC.SmttStackConsF v s   -> stackConsReduct
        (replaceRHSVal us ys v)
        (replaceRHSStk us ys s)


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
  , Eq lo2, Hashable lo2
  , Show lo2, Show s2, Show s1, Show lo1, Show li1
  )
  => TOP.TopDownTreeTransducer s1 ti1 li1 to1 lo1
  -> SMAC.StackMacroTreeTransducer s2 ti2 li2 to2 lo2
  -> ComposedSmtt s1 s2 ti1 to2
composeTdttAndSmtt trans1 trans2 = fromMaybe errorUnreachable
    $ SMAC.buildSmtt ie rules
  where
    composeBasedPseudoSmtt = coerce $ SMAC.toFormattedSmtt trans2

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
      pure
        ( ComposedSmttState f g
        , l
        , runReductionWithRep
          $ BiFixStk $ PsSmttStateF g rhs
            $ V.generate r
            $ \i -> FixStk $ PsSmttContextF i
        )

