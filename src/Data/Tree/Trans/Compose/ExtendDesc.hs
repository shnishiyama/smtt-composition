{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.Compose.ExtendDesc where

import           SattPrelude

import Data.Tree.RankedTree
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
    $ rules0 <> rules1
  where
    initialRules = second (convRhs $ second errorVoid)
      <$> mapToList (ATT.attInitialRules trans)

    rules0 = do
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

    rules1 = mapToList (ATT.attTransRules trans) <&> \((a, l), rhs) ->
      ( a
      , ValuedExpr $ SATT.SattLabelSideF l $ replicate (treeLabelRank (Proxy @ti2) l) ()
      , convRhs id rhs
      )

    convRhs f (ATT.AttAttrSide a)     = ATT.AttAttrSide $ f a
    convRhs f (ATT.AttLabelSide l cs) = undefined f l cs
    convRhs _ ATT.AttBottomLabelSide  = ATT.AttLabelSide (ValuedExpr SATT.SattStackBottomF) []
