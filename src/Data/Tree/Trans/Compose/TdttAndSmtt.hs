{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.Compose.TdttAndSmtt where

import           SattPrelude

import           Control.Monad.State        hiding (forM_, state)
import qualified Data.HashSet               as HashSet
import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Label
import qualified Data.Tree.Trans.MAC        as MAC
import qualified Data.Tree.Trans.SMAC       as SMAC
import           Data.Tree.Trans.Stack
import qualified Data.Tree.Trans.TOP        as TOP
import qualified Data.Vector                as V


data ComposedSmttState s1 s2 = ComposedSmttState s1 s2
  deriving (Eq, Ord, Show, Generic)

instance (Hashable s1, Hashable s2) => Hashable (ComposedSmttState s1 s2)

instance RankedLabel s2 => RankedLabel (ComposedSmttState s1 s2) where
  labelRank (ComposedSmttState _ s2) = labelRank s2

type ComposedSmttRHS s1 s2 to2 lo2 = SMAC.BiRightHandSide
  (ComposedSmttState s1 s2)
  to2 lo2


type ComposeBasedMttInputTree s1 to1 lo1
  = TOP.RightHandSide s1 to1 lo1

type ComposeBasedMttOutputTree s1 s2 to2 lo2
  = ComposedSmttRHS s1 s2 to2 lo2

type ComposeBasedMtt s1 s2 to1 lo1 ti2 li2 to2 lo2
  = MAC.MttTransducer s2
    (ComposeBasedMttInputTree s1 to1 lo1)
    (ComposeBasedMttOutputTree s1 s2 to2 lo2)

toComposeBasedMtt :: forall s1 s2 to1 lo1 ti2 li2 to2 lo2.
  ( Eq s1, Hashable s1, RtConstraint to1 lo1
  , ti2 ~ to1
  , MAC.MttConstraint s2 ti2 li2 to2 lo2
  )
  => HashSet (s1, RankNumber)
  -> SMAC.StackMacroTreeTransducer s2 ti2 li2 to2 lo2
  -> ComposeBasedMtt s1 s2 to1 lo1 ti2 li2 to2 lo2
toComposeBasedMtt fus trans = fromMaybe errorUnreachable $ MAC.buildMtt
    initialExpr
    $ rules1 <> rules0
  where
    treeLabelRankTi2 = treeLabelRank (Proxy @ti2)

    states = SMAC.smttStates trans

    initialExpr = convRhs $ SMAC.smttInitialExpr trans

    rules0 =
      [ ( g
        , TOP.TdttLabelSideF l $ replicate r ()
        , convRhs rhs
        )
      | ((g, l), rhs) <- mapToList $ SMAC.smttTransRules trans
      , let r = treeLabelRankTi2 l
      ]

    convRhs rhs = let
        converter (ValuedExpr x) cs = case x of
          SMAC.SmttLabelSideF l cs' -> MAC.MttLabelSide (ValuedExpr $ SMAC.SmttLabelSideF l cs') cs
          SMAC.SmttStackBottomF     -> MAC.MttLabelSide (ValuedExpr $ SMAC.SmttStackBottomF) cs
          SMAC.SmttStackHeadF s     -> MAC.MttLabelSide (ValuedExpr $ SMAC.SmttStackHeadF s) cs
        converter (StackedExpr x) cs = case x of
          SMAC.SmttStateF s u _   -> MAC.MttState s u cs
          SMAC.SmttContextF c     -> MAC.MttContext c
          SMAC.SmttStackEmptyF    -> MAC.MttLabelSide (StackedExpr $ SMAC.SmttStackEmptyF) cs
          SMAC.SmttStackTailF s   -> MAC.MttLabelSide (StackedExpr $ SMAC.SmttStackTailF s) cs
          SMAC.SmttStackConsF v s -> MAC.MttLabelSide (StackedExpr $ SMAC.SmttStackConsF v s) cs
      in foldTree converter
        $ BiFixStackedExpr rhs

    rules1 = do
      (f, u) <- setToList fus
      g      <- setToList states
      let r = labelRank g - 1
      pure
        ( g
        , TOP.tdttStateF f u
        , MAC.MttLabelSide
          (StackedExpr $ SMAC.SmttStateF (ComposedSmttState f g) u $ replicate r ())
          $ V.generate r MAC.MttContext
        )


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
  )
  => TOP.TopDownTreeTransducer s1 ti1 li1 to1 lo1
  -> SMAC.StackMacroTreeTransducer s2 ti2 li2 to2 lo2
  -> ComposedSmtt s1 s2 ti1 to2
composeTdttAndSmtt trans1 trans2 = fromMaybe errorUnreachable
    $ SMAC.buildSmtt ie rules
  where
    fus = flip execState HashSet.empty $ do
      scanRHS $ TOP.tdttInitialExpr trans1
      forM_ (TOP.tdttTransRules trans1) scanRHS

    scanRHS rhs = case rhs of
      TOP.TdttState f u       -> modify' $ insertSet (coerce f,u)
      TOP.TdttLabelSide _ cs  -> forM_ cs scanRHS
      TOP.TdttBottomLabelSide -> pure ()

    composeBasedMtt = toComposeBasedMtt fus trans2

    runReductionWithRep istate = let
        state = MAC.runMttReduction composeBasedMtt istate
        rhs = fromMaybe errorUnreachable
          $ MAC.fromReductionState state
      in evalStackStkExpr $ case rhs of
        StackedExpr rhs' -> rhs'
        ValuedExpr  rhs' -> SMAC.SmttStackCons rhs' SMAC.SmttStackEmpty

    ie = runReductionWithRep
      $ MAC.toInitialReductionState composeBasedMtt
      $ TOP.tdttInitialExpr trans1

    rules = do
      g <- setToList $ SMAC.smttStates trans2
      let r = labelRank g - 1
      ((f', l), rhs) <- mapToList $ TOP.tdttTransRules trans1
      let f = coerce f'
      pure
        ( ComposedSmttState f g
        , l
        , runReductionWithRep
          $ MAC.RedFix $ MAC.MttStateF g rhs
            $ V.generate r
            $ \i -> MAC.RedFix $ MAC.MttLabelSideF (StackedExpr $ SMAC.SmttContextF i) []
        )

