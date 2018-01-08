{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.Compose.ExtendDesc where

import           SattPrelude

import qualified Data.HashMap.Strict         as HashMap
import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Zipper
import qualified Data.Tree.Trans.ATT         as ATT
import qualified Data.Tree.Trans.SATT        as SATT
import           Data.Tree.Trans.Stack


data ComposedSattSynAttr syn1 inh1 syn2 inh2
  = SynSynAttr syn1 syn2
  | InhInhAttr inh1 inh2
  deriving (Eq, Ord, Show, Generic)

instance (Hashable syn1, Hashable inh1, Hashable syn2, Hashable inh2)
  => Hashable (ComposedSattSynAttr syn1 inh1 syn2 inh2)

data ComposedSattInhAttr syn1 inh1 syn2 inh2
  = SynInhAttr syn1 inh2
  | InhSynAttr inh1 syn2
  deriving (Eq, Ord, Show, Generic)

instance (Hashable syn1, Hashable inh1, Hashable syn2, Hashable inh2)
  => Hashable (ComposedSattInhAttr syn1 inh1 syn2 inh2)

type ComposedSattBiRHS syn1 inh1 syn2 inh2 t l = SATT.BiRightHandSide
  (ComposedSattSynAttr syn1 inh1 syn2 inh2)
  (ComposedSattInhAttr syn1 inh1 syn2 inh2)
  t l


type ComposeBasedAttInputTree syn1 inh1 to1 lo1
  = SATT.BiRightHandSide syn1 inh1 to1 lo1

type ComposeBasedAttOutputTree syn1 inh1 syn2 inh2 to2 lo2
  = ComposedSattBiRHS syn1 inh1 syn2 inh2 to2 lo2

type ComposeBasedAtt syn1 inh1 syn2 inh2 to1 lo1 to2 lo2 = ATT.AttTransducer
  syn2 inh2
  (ComposeBasedAttInputTree syn1 inh1 to1 lo1)
  (ComposeBasedAttOutputTree syn1 inh1 syn2 inh2 to2 lo2)

toComposeBasedAtt :: forall syn1 inh1 syn2 inh2 to1 lo1 ti2 li2 to2 lo2.
  ( Eq syn1, Hashable syn1, Eq inh1, Hashable inh1
  , Eq lo1, Hashable lo1, RtConstraint to1 lo1
  , to1 ~ ti2
  , ATT.AttConstraint syn2 inh2 ti2 li2 to2 lo2
  )
  => HashSet (SATT.SattAttrDepend syn1 inh1)
  -> ATT.AttributedTreeTransducer syn2 inh2 ti2 li2 to2 lo2
  -> ComposeBasedAtt syn1 inh1 syn2 inh2 to1 lo1 to2 lo2
toComposeBasedAtt attrds1 trans = fromMaybe errorUnreachable $ ATT.buildAtt
    (ATT.attInitialAttr trans)
    initialRules
    $ rules1 <> rules2 <> rules0
  where
    treeLabelRankTi2 = treeLabelRank (Proxy @ti2)

    initialRules = second
      (\rhs -> ATT.AttLabelSide (StackedExpr $ SATT.SattStackConsF () ())
        [ convRhs
          (\a -> ATT.AttLabelSide
            (ValuedExpr $ SATT.SattStackHeadF ())
            [ATT.AttAttrSide $ second errorVoid a]
          ) rhs
        , ATT.AttLabelSide (StackedExpr SATT.SattStackEmptyF) []
        ])
      <$> mapToList (ATT.attInitialRules trans)

    rules0 =
      [ ( a
        , ValuedExpr $ SATT.SattLabelSideF l $ replicate r ()
        , convRhs ATT.AttAttrSide rhs
        )
      | ((a, l), rhs) <- mapToList $ ATT.attTransRules trans
      , let r = treeLabelRankTi2 l
      ]

    convRhs f (ATT.AttAttrSide a)     = f a
    convRhs f (ATT.AttLabelSide l cs) = ATT.AttLabelSide
      (ValuedExpr $ SATT.SattLabelSideF l $ void cs)
      $ convRhs f <$> cs
    convRhs _ ATT.AttBottomLabelSide  = ATT.AttLabelSide (ValuedExpr SATT.SattStackBottomF) []

    rules1 = do
      attrd1 <- setToList attrds1
      attr2  <- setToList $ ATT.attAttributes trans
      case attr2 of
        ATT.Synthesized a2 -> case attrd1 of
          SATT.Synthesized (a1, j) -> pure
            ( ATT.Synthesized a2
            , StackedExpr $ SATT.SattAttrSideF attrd1 ()
            , ATT.AttLabelSide
              (StackedExpr $ SATT.SattAttrSideF (SATT.Synthesized (a1 `SynSynAttr` a2, j)) ())
              []
            )
          SATT.Inherited b1        -> pure
            ( ATT.Synthesized a2
            , StackedExpr $ SATT.SattAttrSideF attrd1 ()
            , ATT.AttLabelSide
              (StackedExpr $ SATT.SattAttrSideF (SATT.Inherited (b1 `InhSynAttr` a2)) ())
              []
            )
        _ -> empty

    rules2 = do
      attr2  <- setToList $ ATT.attAttributes trans
      case attr2 of
        ATT.Synthesized a2 ->
          [ ( ATT.Synthesized a2
            , StackedExpr $ SATT.SattStackConsF () ()
            , ATT.AttLabelSide
              (StackedExpr $ SATT.SattStackConsF () ())
              [ ATT.SynAttrSide a2 0
              , ATT.SynAttrSide a2 1
              ]
            )
          , ( ATT.Synthesized a2
            , StackedExpr $ SATT.SattStackEmptyF
            , ATT.AttLabelSide
              (StackedExpr $ SATT.SattStackEmptyF)
              []
            )
          , ( ATT.Synthesized a2
            , ValuedExpr $ SATT.SattStackBottomF
            , ATT.AttLabelSide
              (ValuedExpr $ SATT.SattStackBottomF)
              []
            )
          , ( ATT.Synthesized a2
            , ValuedExpr $ SATT.SattStackHeadF ()
            , ATT.AttLabelSide
              (ValuedExpr $ SATT.SattStackHeadF ())
              [ATT.SynAttrSide a2 0]
            )
          , ( ATT.Synthesized a2
            , StackedExpr $ SATT.SattStackTailF ()
            , ATT.AttLabelSide
              (StackedExpr $ SATT.SattStackTailF ())
              [ATT.SynAttrSide a2 0]
            )
          ]
        ATT.Inherited b2 ->
          [ ( ATT.Inherited (b2, 0)
            , StackedExpr $ SATT.SattStackConsF () ()
            , ATT.AttLabelSide
              (ValuedExpr $ SATT.SattStackHeadF ())
              [ATT.InhAttrSide b2]
            )
          , ( ATT.Inherited (b2, 1)
            , StackedExpr $ SATT.SattStackConsF () ()
            , ATT.AttLabelSide
              (StackedExpr $ SATT.SattStackTailF ())
              [ATT.InhAttrSide b2]
            )
          , ( ATT.Inherited (b2, 0)
            , ValuedExpr $ SATT.SattStackHeadF ()
            , ATT.AttLabelSide
              (StackedExpr $ SATT.SattStackConsF () ())
              [ ATT.InhAttrSide b2
              , ATT.AttLabelSide (StackedExpr $ SATT.SattStackEmptyF) []
              ]
            )
          , ( ATT.Inherited (b2, 0)
            , StackedExpr $ SATT.SattStackTailF ()
            , ATT.AttLabelSide
              (StackedExpr $ SATT.SattStackConsF () ())
              [ ATT.AttLabelSide (ValuedExpr $ SATT.SattStackBottomF) []
              , ATT.InhAttrSide b2
              ]
            )
          ]


type SattRuleIndex syn inh ta la tb lb tz = HashMap
  (SATT.SattAttr syn inh, Maybe la)
  [(SATT.SattAttrDepend syn inh, RtApply (SATT.SattPathInfo tz) (SATT.BiRightHandSide syn inh tb lb))]

indexSattRule :: forall tz syn inh ta la tb lb.
  ( SATT.SattConstraint syn inh ta la tb lb
  , RankedTreeZipper tz
  )
  => SATT.StackAttributedTreeTransducer syn inh ta la tb lb
  -> (SattRuleIndex syn inh ta la tb lb tz, HashSet (SATT.SattAttrDepend syn inh))
indexSattRule trans = (mapFromList idx, setFromList attrds)
  where
    ia = SATT.sattInitialAttr trans
    irules = mapToList $ SATT.sattInitialRules trans
    rules = mapToList $ SATT.sattTransRules trans

    (idx, attrds) = let
        cxt0 = ([], [])
        cxt1 = foldl' (\s (a, rhs) ->
          let
            a' = bimap (const ia) (,0) a
            l' = Nothing
            p  = initialPathInfo $ BiFixStackedExpr rhs
          in go a' l' p s)
          cxt0 irules
        cxt2 = foldl' (\s ((a, l), rhs) ->
          let
            a' = a
            l' = Just l
            p  = initialPathInfo $ BiFixStackedExpr rhs
          in go a' l' p s)
          cxt1 rules
      in cxt2

    go a l p (xs, ys) = let
        (x, ys') = scanRHS a l (zoomNextRightOutZipper (checkAttrSide . toTree) p) [] ys
      in (if null x then xs else ((a, l), x):xs, ys')

    initialPathInfo = toZipper

    scanRHS _ _ Nothing   xs ys = (xs, ys)
    scanRHS a l (Just p') xs ys = case toTree p' of
      BiFixStackedExpr x -> case x of
        SATT.SattAttrSide ad -> scanRHS a l
          (zoomNextRightOutZipper1 (checkAttrSide . toTree) p')
          ((ad, p'):xs) (ad:ys)
        _ -> errorUnreachable
      _ -> errorUnreachable

    checkAttrSide (StackedExpr x) = case x of
      SATT.SattAttrSide{} -> True
      _                   -> False
    checkAttrSide _                   = False


type ComposedSatt syn1 inh1 syn2 inh2 ti to = SATT.SattTransducer
  (ComposedSattSynAttr syn1 inh1 syn2 inh2)
  (ComposedSattInhAttr syn1 inh1 syn2 inh2)
  ti to

-- FIXME: give the implentation
checkSingleUse :: MonadThrow m
  => SATT.StackAttributedTreeTransducer syn1 inh1 ti1 li1 to1 lo1 -> m ()
checkSingleUse _ = pure ()

-- | composition of a satt and an att
--
-- Examples:
-- >>> import Data.Tree.RankedTree.Label
-- >>> import Data.Tree.RankedTree.Instances
-- >>> import Data.Tree.Trans.SATT.Instances
-- >>> import qualified Data.Tree.Trans.ATT.Instances as ATT
-- >>> import qualified Data.Tree.Trans.TOP.Instances as TOP
-- >>> import qualified Data.Tree.Trans.TOP as TOP
-- >>> import qualified Data.Tree.Trans.SATT as SATT
-- >>> import Data.Tree.Trans.Class
-- >>> a = taggedRankedLabel @"A"
-- >>> b = taggedRankedLabel @"B"
-- >>> c = taggedRankedLabel @"C"
-- >>> inputSampleTree = mkTree a [mkTree c [], mkTree b [mkTree c []]]
-- >>> traUniverse = setFromList $ taggedRankedAlphabetUniverse Proxy
-- >>> :{
-- identityAtt :: (RankedTree ta, Eq (LabelType ta), Hashable (LabelType ta))
--   => HashSet (LabelType ta) -> ATT.AttTransducer () Void ta ta
-- identityAtt = TOP.toAttributedTreeTransducer . TOP.identityTransducer
-- identitySatt :: (RankedTree ta, Eq (LabelType ta), Hashable (LabelType ta))
--   => HashSet (LabelType ta) -> SATT.SattTransducer () Void ta ta
-- identitySatt = SATT.toStackAttributedTreeTransducer . identityAtt
-- :}
--
-- >>> identOutputTrans = identityAtt @OutputSampleTree traUniverse
-- >>> sampleIdentTrans <- composeSattAndAtt sampleSatt identOutputTrans
-- >>> treeTrans sampleIdentTrans inputSampleTree
-- D(F,F)
-- >>> identInputTrans = identitySatt @InputSampleTree traUniverse
-- >>> identSampleTrans <- composeSattAndAtt identInputTrans ATT.sampleAtt
-- >>> treeTrans identSampleTrans inputSampleTree
-- D(F,F)
-- >>> pOne   = taggedRankedLabel @"one"
-- >>> pTwo   = taggedRankedLabel @"two"
-- >>> pPlus  = taggedRankedLabel @"plus"
-- >>> pMulti = taggedRankedLabel @"multi"
-- >>> pEnd   = taggedRankedLabel @"end"
-- >>> :{
-- inputPostfixTree = mkTree pOne [ mkTree pTwo [mkTree pPlus
--   [mkTree pTwo [mkTree pMulti [mkTree pEnd []]]]
--   ]]
-- :}
--
-- >>> identPostfixTrans <- composeSattAndAtt postfixToInfixSatt ATT.infixToPostfixAtt
-- >>> treeTrans identPostfixTrans inputPostfixTree
-- one(two(plus(two(multi(end)))))
--
composeSattAndAtt :: forall m syn1 inh1 syn2 inh2 ti1 li1 to1 lo1 ti2 li2 to2 lo2.
  ( SATT.SattConstraint syn1 inh1 ti1 li1 to1 lo1
  , to1 ~ ti2
  , ATT.AttConstraint syn2 inh2 ti2 li2 to2 lo2
  , Eq lo2
  , MonadThrow m
  , Show syn2, Show inh1, Show inh2, Show syn1, Show lo2, Show lo1, Show li1
  )
  => SATT.StackAttributedTreeTransducer syn1 inh1 ti1 li1 to1 lo1
  -> ATT.AttributedTreeTransducer syn2 inh2 ti2 li2 to2 lo2
  -> m (ComposedSatt syn1 inh1 syn2 inh2 ti1 to2)
composeSattAndAtt trans1NoST trans2 = do
    checkSingleUse trans1
    pure $ fromMaybe errorUnreachable $ SATT.buildSatt
      (iattr1 `SynSynAttr` iattr2)
      (foldl' (\xs irule1 -> goIrule irule1 <> xs) [] irules1)
      (foldl' (\xs rule1  -> goRule  rule1  <> xs) [] rules1)
  where
    trans1 = SATT.toStandardForm trans1NoST

    iattr1 = SATT.sattInitialAttr trans1
    iattr2 = ATT.attInitialAttr trans2

    (idx, attrds) = indexSattRule @RTZipper trans1
    irules1 = mapToList $ SATT.sattInitialRules trans1
    rules1  = mapToList $ SATT.sattTransRules trans1

    composeBasedAtt = toComposeBasedAtt attrds trans2

    attrs2 = setToList $ ATT.attAttributes trans2
    (synAttrs2, inhAttrs2) = foldr (\case
        ATT.Synthesized a' -> first (a':)
        ATT.Inherited   a' -> second (a':)
      ) ([], []) attrs2

    zipRules rules = let
        unconsS = either
          (\s -> if s == stackEmpty then Nothing else error $ "Head/Tail is not allowed")
          Just
          . unconsStackStkExpr

        zipS StackEmpty e2 = e2
        zipS e1 StackEmpty = e1
        zipS e1 e2 = case (unconsS e1, unconsS e2) of
          (Nothing, _) -> e2
          (_, Nothing) -> e1
          (Just (eh1, e1'), Just (eh2, e2')) -> case (eh1, eh2) of
            (SATT.SattStackBottom, eh) -> stackCons eh $ zipS e1' e2'
            (eh, SATT.SattStackBottom) -> stackCons eh $ zipS e1' e2'
            _                          -> error "The format is not allowed"

        zipRules' = foldl' zipS stackEmpty
      in mapToList $ fmap zipRules'
        $ HashMap.fromListWith (<>) [(a, r:[]) | (a, r) <- rules]

    buildRules' replacerB2 replacerA2 isInitial a l rhs = zipRules $
      [ ( replacerA2 a2
        , runReductionWithRep replacerB2 $ ATT.toInitialAttrState (ATT.Synthesized a2) pathInfo
        )
      | a2 <- if isInitial && ATT.isSynthesized a then [iattr2] else synAttrs2
      , let pathInfo = ATT.emptyAttPathInfo isInitial $ StackedExpr rhs
      ] <> do
        b2 <- inhAttrs2
        (ad1, p) <- ruleIndex a l
        let initAttrStateB2 = ATT.toInitialAttrState (ATT.Inherited b2) $ toInhPathInfo isInitial p
        let rhs' = runReductionWithRep replacerB2 initAttrStateB2
        pure $ case ad1 of
          SATT.Synthesized (a1', j') ->
            ( SATT.Inherited (a1' `SynInhAttr` b2, j')
            , rhs'
            )
          SATT.Inherited b1' ->
            ( SATT.Synthesized $ b1' `InhInhAttr` b2
            , rhs'
            )

    toInhPathInfo True  p = p & ATT._attPathList %~ (<> [0])
    toInhPathInfo False p = p

    buildRules a@(SATT.Synthesized a1) Nothing rhs = buildRules'
      (const $ error "Not contains any inherited attributes in initial rules")
      (\a2 -> SATT.Synthesized $ a1 `SynSynAttr` a2)
      True
      a Nothing rhs
    buildRules a@(SATT.Synthesized a1) l rhs = buildRules'
      (\b2' -> SATT.Inherited $ a1 `SynInhAttr` b2')
      (\a2 -> SATT.Synthesized $ a1 `SynSynAttr` a2)
      False
      a l rhs
    buildRules a@(SATT.Inherited (b1, j)) l rhs = buildRules'
      (\b2' -> SATT.Synthesized (b1 `InhInhAttr` b2', j))
      (\a2 -> SATT.Inherited (b1 `InhSynAttr` a2, j))
      (isNothing l)
      a l rhs

    toInitialRhsStk x = case x of
      SATT.SattAttrSide a     -> SATT.SattAttrSide $ second errorVoid a
      SATT.SattStackEmpty     -> SATT.SattStackEmpty
      SATT.SattStackTail s    -> SATT.SattStackTail (toInitialRhsStk s)
      SATT.SattStackCons v s  -> SATT.SattStackCons (toInitialRhsVal v) (toInitialRhsStk s)

    toInitialRhsVal x = case x of
      SATT.SattLabelSide l cs -> SATT.SattLabelSide l $ toInitialRhsVal <$> cs
      SATT.SattStackBottom    -> SATT.SattStackBottom
      SATT.SattStackHead s    -> SATT.SattStackHead (toInitialRhsStk s)

    goIrule (attr1, rhs) = let
        formatRule (SATT.Synthesized _,    r) = (SATT.Synthesized (), toInitialRhsStk r)
        formatRule (SATT.Inherited (a, _), r) = (SATT.Inherited a,    toInitialRhsStk r)
      in formatRule <$> case attr1 of
        SATT.Synthesized () -> buildRules (SATT.Synthesized iattr1) Nothing rhs
        SATT.Inherited   b1 -> buildRules (SATT.Inherited (b1, 0))  Nothing rhs

    goRule ((attr1, l), rhs) = let
        formatRule (a, r) = (a, l, r)
      in formatRule <$> buildRules attr1 (Just l) rhs

    ruleIndex a l = fromMaybe [] $ lookup (a, l) idx

    runReductionWithRep f istate = let
        state  = ATT.runAttReduction @RTZipper composeBasedAtt istate
        birhs' = replaceRedState f (BiFixStackedExpr SATT.SattStackEmpty) state
      in case birhs' of
        StackedExpr rhs' -> rhs'
        ValuedExpr  _    -> error "expected a stack expression"

    replaceRedState f bot (ATT.RedFix x) = case x of
      ATT.AttLabelSideF l cs  ->
        let
          replaceRedStateVal = replaceRedState f $ BiFixValuedExpr SATT.SattStackBottom
          replaceRedStateStk = replaceRedState f $ BiFixStackedExpr SATT.SattStackEmpty
          cs' = case l of
            ValuedExpr l' -> case l' of
              SATT.SattLabelSideF{}   -> replaceRedStateVal <$> cs
              SATT.SattStackBottomF{} -> []
              SATT.SattStackHeadF{}   -> replaceRedStateStk <$> cs
            StackedExpr l' -> case l' of
              SATT.SattAttrSideF{}    -> []
              SATT.SattStackEmptyF{}  -> []
              SATT.SattStackTailF{}   -> replaceRedStateStk <$> cs
              SATT.SattStackConsF{}   ->
                [ replaceRedStateVal $ cs `indexEx` 0
                , replaceRedStateStk $ cs `indexEx` 1
                ]
        in mkTreeUnchecked l cs'
      ATT.AttBottomLabelSideF -> bot
      ATT.AttAttrSideF (ATT.Inherited b) p | p ^. ATT._attPathList . to null ->
        BiFixStackedExpr $ SATT.SattAttrSide $ f b
      _ -> error "This state is reducible"
