{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.Compose.Desc where

import           SmttPrelude

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Zipper
import           Data.Tree.Trans.ATT


data ComposedAttSynAttr syn1 inh1 syn2 inh2
  = SynSynAttr syn1 syn2
  | InhInhAttr inh1 inh2
  deriving (Eq, Ord, Generic, Hashable)

instance (Show syn1, Show inh1, Show syn2, Show inh2) => Show (ComposedAttSynAttr syn1 inh1 syn2 inh2) where
  show (a1 `SynSynAttr` a2) = show (a1, a2)
  show (b1 `InhInhAttr` b2) = show (b1, b2)

data ComposedAttInhAttr syn1 inh1 syn2 inh2
  = SynInhAttr syn1 inh2
  | InhSynAttr inh1 syn2
  deriving (Eq, Ord, Generic, Hashable)

instance (Show syn1, Show inh1, Show syn2, Show inh2) => Show (ComposedAttInhAttr syn1 inh1 syn2 inh2) where
  show (a1 `SynInhAttr` b2) = show (a1, b2)
  show (b1 `InhSynAttr` a2) = show (b1, a2)

type ComposedAttRHS syn1 inh1 syn2 inh2 t l = RightHandSide
  (ComposedAttSynAttr syn1 inh1 syn2 inh2)
  (ComposedAttInhAttr syn1 inh1 syn2 inh2)
  t l


type ComposeBasedAttInputTree syn1 inh1 to1 lo1
  = RightHandSide syn1 inh1 to1 lo1

type ComposeBasedAttOutputTree syn1 inh1 syn2 inh2 to2 lo2
  = ComposedAttRHS syn1 inh1 syn2 inh2 to2 lo2

type ComposeBasedAtt syn1 inh1 syn2 inh2 to1 lo1 to2 lo2 = AttTransducer
  syn2 inh2
  (ComposeBasedAttInputTree syn1 inh1 to1 lo1)
  (ComposeBasedAttOutputTree syn1 inh1 syn2 inh2 to2 lo2)

toComposeBasedAtt :: forall syn1 inh1 syn2 inh2 to1 lo1 ti2 li2 to2 lo2.
  ( Eq syn1, Hashable syn1, Eq inh1, Hashable inh1
  , Eq lo1, Hashable lo1, RtConstraint to1 lo1
  , to1 ~ ti2
  , AttConstraint syn2 inh2 ti2 li2 to2 lo2
  )
  => HashSet (AttAttrDepend syn1 inh1)
  -> AttributedTreeTransducer syn2 inh2 ti2 li2 to2 lo2
  -> ComposeBasedAtt syn1 inh1 syn2 inh2 to1 lo1 to2 lo2
toComposeBasedAtt attrds1 trans = fromMaybe errorUnreachable $ buildAtt
    (attInitialAttr trans)
    initialRules
    $ rules1 <> rules0
  where
    initialRules = second (convRhs $ second errorVoid)
      <$> mapToList (attInitialRules trans)

    rules0 = mapToList (attTransRules trans) <&> \((a, l), rhs) ->
      ( a
      , AttLabelSideF l $ replicate (treeLabelRank (Proxy @ti2) l) ()
      , convRhs id rhs
      )

    convRhs f (AttAttrSide a)     = AttAttrSide $ f a
    convRhs f (AttLabelSide l cs) = AttLabelSide (AttLabelSideF l $ void cs) $ convRhs f <$> cs
    convRhs _ AttBottomLabelSide  = AttLabelSide AttBottomLabelSideF []

    rules1 = do
      attrd1 <- setToList attrds1
      attr2  <- setToList $ attAttributes trans
      case attr2 of
        Synthesized a2 -> case attrd1 of
          Synthesized (a1, j) -> pure
            ( Synthesized a2
            , AttAttrSideF attrd1 ()
            , AttLabelSide (AttAttrSideF (Synthesized (a1 `SynSynAttr` a2, j)) ()) []
            )
          Inherited b1        -> pure
            ( Synthesized a2
            , AttAttrSideF attrd1 ()
            , AttLabelSide (AttAttrSideF (Inherited (b1 `InhSynAttr` a2)) ()) []
            )
        _ -> empty


type AttRuleIndex syn inh ta la tb lb tz = HashMap
  (AttAttr syn inh, Maybe la)
  [(AttAttrDepend syn inh, RtApply (AttPathInfo tz) (RightHandSide syn inh tb lb))]

indexAttRule :: forall tz syn inh ta la tb lb.
  ( AttConstraint syn inh ta la tb lb
  , RankedTreeZipper tz
  )
  => AttributedTreeTransducer syn inh ta la tb lb
  -> (AttRuleIndex syn inh ta la tb lb tz, HashSet (AttAttrDepend syn inh))
indexAttRule trans = (mapFromList idx, setFromList attrds)
  where
    ia = attInitialAttr trans
    irules = mapToList $ attInitialRules trans
    rules = mapToList $ attTransRules trans

    (idx, attrds) = let
        cxt0 = ([], [])
        cxt1 = foldl' (\s (a, rhs) ->
          let
            a' = bimap (const ia) (,0) a
            l' = Nothing
            p  = initialPathInfo rhs
          in go a' l' p s)
          cxt0 irules
        cxt2 = foldl' (\s ((a, l), rhs) ->
          let
            a' = a
            l' = Just l
            p  = initialPathInfo rhs
          in go a' l' p s)
          cxt1 rules
      in cxt2

    go a l p (xs, ys) = let
        (x, ys') = scanRHS a l (zoomNextRightOutZipper (checkAttrSide . toTree) p) [] ys
      in (if null x then xs else ((a, l), x):xs, ys')

    initialPathInfo = toZipper

    scanRHS _ _ Nothing   xs ys = (xs, ys)
    scanRHS a l (Just p') xs ys = case toTree p' of
      AttAttrSide ad -> scanRHS a l
        (zoomNextRightOutZipper1 (checkAttrSide . toTree) p')
        ((ad, p'):xs) (ad:ys)
      _ -> errorUnreachable

    checkAttrSide AttAttrSide{} = True
    checkAttrSide _             = False


type ComposedAtt syn1 inh1 syn2 inh2 ti to = AttTransducer
  (ComposedAttSynAttr syn1 inh1 syn2 inh2)
  (ComposedAttInhAttr syn1 inh1 syn2 inh2)
  ti to

-- FIXME: give the implentation
checkSingleUse :: MonadThrow m
  => AttributedTreeTransducer syn1 inh1 ti1 li1 to1 lo1 -> m ()
checkSingleUse _ = pure ()

-- | composition of atts
--
-- Examples:
-- >>> import Data.Tree.RankedTree.Label
-- >>> import Data.Tree.RankedTree.Instances
-- >>> import Data.Tree.Trans.ATT.Instances
-- >>> import qualified Data.Tree.Trans.TOP.Instances as TOP
-- >>> import qualified Data.Tree.Trans.TOP as TOP
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> traUniverse = setFromList $ taggedRankedAlphabetUniverse Proxy
-- >>> :{
-- identityTransducer :: (RankedTree ta, Eq (LabelType ta), Hashable (LabelType ta))
--   => HashSet (LabelType ta) -> AttTransducer () Void ta ta
-- identityTransducer = TOP.toAttributedTreeTransducer . TOP.identityTransducer
-- :}
--
-- >>> identInputTrans = identityTransducer @InputSampleTree traUniverse
-- >>> identOutputTrans = identityTransducer @OutputSampleTree traUniverse
-- >>> sampleIdentTrans <- composeAtts sampleAtt identOutputTrans
-- >>> treeTrans sampleIdentTrans inputSampleTree
-- D(F,F)
-- >>> identSampleTrans <- composeAtts identInputTrans sampleAtt
-- >>> treeTrans identSampleTrans inputSampleTree
-- D(F,F)
--
composeAtts :: forall m syn1 inh1 syn2 inh2 ti1 li1 to1 lo1 ti2 li2 to2 lo2.
  ( AttConstraint syn1 inh1 ti1 li1 to1 lo1
  , to1 ~ ti2
  , AttConstraint syn2 inh2 ti2 li2 to2 lo2
  , MonadThrow m
  )
  => AttributedTreeTransducer syn1 inh1 ti1 li1 to1 lo1
  -> AttributedTreeTransducer syn2 inh2 ti2 li2 to2 lo2
  -> m (ComposedAtt syn1 inh1 syn2 inh2 ti1 to2)
composeAtts trans1 trans2 = do
  checkSingleUse trans1
  pure $ fromMaybe errorUnreachable $ buildAtt
    (iattr1 `SynSynAttr` iattr2)
    (foldl' (\xs irule1 -> goIrule irule1 <> xs) [] irules1)
    (foldl' (\xs rule1  -> goRule  rule1  <> xs) [] rules1)
  where
    iattr1 = attInitialAttr trans1
    iattr2 = attInitialAttr trans2

    (idx, attrds) = indexAttRule @RTZipper trans1
    irules1 = mapToList $ attInitialRules trans1
    rules1  = mapToList $ attTransRules trans1

    composeBasedAtt = toComposeBasedAtt attrds trans2

    attrs2 = setToList $ attAttributes trans2
    (synAttrs2, inhAttrs2) = foldr (\case
        Synthesized a' -> first (a':)
        Inherited   a' -> second (a':)
      ) ([], []) attrs2

    buildRules' replacerB2 replacerA2 isInitial a l rhs =
      [ ( replacerA2 a2
        , runReductionWithRep replacerB2 $ toInitialAttrState (Synthesized a2) pathInfo
        )
      | a2 <- if isInitial && isSynthesized a then [iattr2] else synAttrs2
      , let pathInfo = emptyAttPathInfo isInitial rhs
      ] <> do
        b2 <- inhAttrs2
        (ad1, p) <- ruleIndex a l
        let initAttrStateB2 = toInitialAttrState (Inherited b2) $ toInhPathInfo isInitial p
        pure $ case ad1 of
          Synthesized (a1', j') ->
            ( Inherited (a1' `SynInhAttr` b2, j')
            , runReductionWithRep replacerB2 initAttrStateB2
            )
          Inherited b1' ->
            ( Synthesized $ b1' `InhInhAttr` b2
            , runReductionWithRep replacerB2 initAttrStateB2
            )

    toInhPathInfo True  p = p & _attPathList %~ (<> [0])
    toInhPathInfo False p = p

    buildRules a@(Synthesized a1) Nothing rhs = buildRules'
      (const $ error "Not contains any inherited attributes in initial rules")
      (\a2 -> Synthesized $ a1 `SynSynAttr` a2)
      True
      a Nothing rhs
    buildRules a@(Synthesized a1) l rhs = buildRules'
      (\b2' -> Inherited $ a1 `SynInhAttr` b2')
      (\a2 -> Synthesized $ a1 `SynSynAttr` a2)
      False
      a l rhs
    buildRules a@(Inherited (b1, j)) l rhs = buildRules'
      (\b2' -> Synthesized (b1 `InhInhAttr` b2', j))
      (\a2 -> Inherited (b1 `InhSynAttr` a2, j))
      (isNothing l)
      a l rhs

    toInitialRhs (AttAttrSide a)     = AttAttrSide $ second errorVoid a
    toInitialRhs (AttLabelSide l cs) = AttLabelSide l $ toInitialRhs <$> cs
    toInitialRhs AttBottomLabelSide  = AttBottomLabelSide

    goIrule (attr1, rhs) = let
        formatRule (Synthesized _,    r) = (Synthesized (), toInitialRhs r)
        formatRule (Inherited (a, _), r) = (Inherited a,    toInitialRhs r)
      in formatRule <$> case attr1 of
        Synthesized () -> buildRules (Synthesized iattr1) Nothing rhs
        Inherited   b1 -> buildRules (Inherited (b1, 0))  Nothing rhs

    goRule ((attr1, l), rhs) = let
        formatRule (a, r) = (a, l, r)
      in formatRule <$> buildRules attr1 (Just l) rhs

    ruleIndex a l = fromMaybe [] $ lookup (a, l) idx

    runReductionWithRep f = replaceRedState f . runAttReduction @RTZipper composeBasedAtt

    replaceRedState f (RedFix x) = case x of
      AttLabelSideF l cs  -> mkTreeUnchecked l $ replaceRedState f <$> cs
      AttBottomLabelSideF -> mkTreeUnchecked AttBottomLabelSideF []
      AttAttrSideF (Inherited b) p | p ^. _attPathList . to null -> AttAttrSide $ f b
      _ -> error "This state is reducible"
