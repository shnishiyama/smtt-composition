{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.Compose.ExtendDesc where

import           SattPrelude

import Data.Tree.RankedTree
import Data.Tree.RankedTree.Zipper
import Data.Tree.Trans.Stack
import qualified Data.Tree.Trans.ATT as ATT
import qualified Data.Tree.Trans.SATT as SATT


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
    initialRules = second (convRhs $ second errorVoid)
      <$> mapToList (ATT.attInitialRules trans)

    rules0 = mapToList (ATT.attTransRules trans) <&> \((a, l), rhs) ->
      ( a
      , ValuedExpr $ SATT.SattLabelSideF l $ replicate (treeLabelRank (Proxy @ti2) l) ()
      , convRhs id rhs
      )

    convRhs f (ATT.AttAttrSide a)     = ATT.AttAttrSide $ f a
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
  [(SATT.SattAttrDepend syn inh, RtApply (SATT.SattPathInfo tz) (SATT.RightHandSide syn inh tb lb))]

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
      SATT.SattAttrSide ad -> scanRHS a l
        (zoomNextRightOutZipper1 (checkAttrSide . toTree) p')
        ((ad, p'):xs) (ad:ys)
      _ -> errorUnreachable

    checkAttrSide SATT.SattAttrSide{} = True
    checkAttrSide _                   = False

