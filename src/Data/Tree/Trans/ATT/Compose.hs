{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE OverloadedLists   #-}
{-# LANGUAGE TypeInType        #-}

module Data.Tree.Trans.ATT.Compose
  (
    -- common
    composeAtts
  , ComposedAtt
  , ComposedAttAttr(..)

  , indexAttRule
  , toComposeBasedAtt
  , ComposeBasedAtt
  ) where

import           ClassyPrelude

import qualified Data.HashMap.Strict         as HM
import           Data.Universe.Class
import qualified Data.Vector                 as V
import           GHC.Generics
import           Unsafe.Coerce

import           Data.Tree.RankedTree
import           Data.Tree.RankedTree.Zipper
import           Data.Tree.Trans.ATT


type ExtendedAttAttr syn inh = AttrSide syn inh

data ExtendedInputLabel syn2 inh2 t2 l2 t1 l1
  = OriginalInputLabel l1
  | ExtendedAttrLabel (ExtendedAttAttr syn2 inh2)
  deriving (Show, Eq, Ord, Generic)

instance (Universe syn2, Universe inh2, Universe l1, Universe l2, RtConstraint t2 l2)
    => Universe (ExtendedInputLabel syn2 inh2 t2 l2 t1 l1) where

  universe = ([OriginalInputLabel l | l <- universe ] <>) $ do
      a <- [taggedSynBox (a, i) | a <- universe, i <- [0..(r - 1)]] <> [taggedInhBox a | a <- universe]
      return $ ExtendedAttrLabel a
    where
      r = fromMaybe 0 $ maximumMay [ treeLabelRank (treeTag @t2) l | l <- universe ]

instance (Finite syn2, Finite inh2, Finite l1, Finite l2, RtConstraint t2 l2)
  => Finite (ExtendedInputLabel syn2 inh2 t2 l2 t1 l1)
instance (Hashable syn2, Hashable inh2, Hashable l1) => Hashable (ExtendedInputLabel syn2 inh2 t2 l2 t1 l1)

data ExtendedInputTree syn2 inh2 t2 l2 t1 l1
  = OriginalInputTree l1 (NodeVec :$ ExtendedInputTree syn2 inh2 t2 l2 t1 l1)
  | ExtendedAttrNode (ExtendedAttAttr syn2 inh2)
  deriving (Show, Eq, Ord)

instance (RtConstraint t1 l1) => RankedTree (ExtendedInputTree syn2 inh2 t2 l2 t1 l1) where
  type LabelType (ExtendedInputTree syn2 inh2 t2 l2 t1 l1) = ExtendedInputLabel syn2 inh2 t2 l2 t1 l1

  treeLabel (OriginalInputTree l _) = OriginalInputLabel l
  treeLabel (ExtendedAttrNode a)    = ExtendedAttrLabel a

  treeChilds (OriginalInputTree _ ts) = ts
  treeChilds ExtendedAttrNode{}       = []

  treeLabelRank _ (OriginalInputLabel l) = treeLabelRank (treeTag @t1) l
  treeLabelRank _ ExtendedAttrLabel{}    = 0

  mkTreeUnchecked (OriginalInputLabel l) ts = OriginalInputTree l ts
  mkTreeUnchecked (ExtendedAttrLabel a)  _  = ExtendedAttrNode a


data ExtendedOutputLabel syn1 inh1 syn2 inh2 t2 l2 t1 l1
  = OriginalOutputLabel l1
  | ExtendedOutAttrLabel syn1 (ExtendedAttAttr syn2 inh2)
  deriving (Show, Eq, Ord, Generic)

instance (Universe syn1, Universe inh1, Universe syn2, Universe inh2, Universe l1, Universe l2, RtConstraint t2 l2)
    => Universe (ExtendedOutputLabel syn1 inh1 syn2 inh2 t2 l2 t1 l1) where

  universe = ([ OriginalOutputLabel l | l <- universe ] <>) $ do
      a1 <- universe
      a2 <- [taggedSynBox (a, i) | a <- universe, i <- [0..(r - 1)]] <> [taggedInhBox a | a <- universe]
      return $ ExtendedOutAttrLabel a1 a2
    where
      r = fromMaybe 0 $ maximumMay [ treeLabelRank (treeTag @t2) l | l <- universe ]

instance (Finite syn1, Finite inh1, Finite syn2, Finite inh2, Finite l1, Finite l2, RtConstraint t2 l2)
  => Finite (ExtendedOutputLabel syn1 inh1 syn2 inh2 t2 l2 t1 l1)
instance (Hashable syn1, Hashable inh1, Hashable syn2, Hashable inh2, Hashable l1)
  => Hashable (ExtendedOutputLabel syn1 inh1 syn2 inh2 t2 l2 t1 l1)

data ExtendedOutputTree syn1 inh1 syn2 inh2 t2 l2 t1 l1
  = OriginalOutputTree l1 (NodeVec :$ ExtendedOutputTree syn1 inh1 syn2 inh2 t2 l2 t1 l1)
  | ExtendedOutAttrNode syn1 (ExtendedAttAttr syn2 inh2)
  deriving (Show, Eq, Ord)

instance (RtConstraint t1 l1) => RankedTree (ExtendedOutputTree syn1 inh1 syn2 inh2 t2 l2 t1 l1) where
  type LabelType (ExtendedOutputTree syn1 inh1 syn2 inh2 t2 l2 t1 l1) = ExtendedOutputLabel syn1 inh1 syn2 inh2 t2 l2 t1 l1

  treeLabel (OriginalOutputTree l _)    = OriginalOutputLabel l
  treeLabel (ExtendedOutAttrNode a1 a2) = ExtendedOutAttrLabel a1 a2

  treeChilds (OriginalOutputTree _ ts) = ts
  treeChilds ExtendedOutAttrNode{}     = []

  treeLabelRank _ (OriginalOutputLabel l) = treeLabelRank (treeTag @t1) l
  treeLabelRank _ ExtendedOutAttrLabel{}  = 0

  mkTreeUnchecked (OriginalOutputLabel l)      ts = OriginalOutputTree l ts
  mkTreeUnchecked (ExtendedOutAttrLabel a1 a2) _  = ExtendedOutAttrNode a1 a2


type ComposeBasedAttInputTree syn inh ti1 to1 ti2 to2 = RtApply (RtApply (ExtendedInputTree syn inh) ti2) ti1
type ComposeBasedAttOutputTree syn1 inh1 syn2 inh2 ti1 to1 ti2 to2 = RtApply (RtApply (ExtendedOutputTree syn1 inh1 syn2 inh2) ti2) to1

type ComposeBasedAtt syn1 inh1 syn2 inh2 ti1 to1 ti2 to2 = FiniteAttrTreeTrans syn1 inh1
  (ComposeBasedAttInputTree syn2 inh2 ti1 to1 ti2 to2)
  (ComposeBasedAttOutputTree syn1 inh1 syn2 inh2 ti1 to1 ti2 to2)

toComposeBasedAtt :: forall t syn1 inh1 syn2 inh2 ti1 to1 ti2 to2.
  ( FiniteAttrTreeTransReq syn1 inh1 ti1 to1
  , Eq syn2, Eq inh2, Hashable syn2, Hashable inh2, Finite syn2, Finite inh2
  , FiniteRankedTree ti2
  , AttrTreeTrans t ti1 to1, syn1 ~ SynthesAttr t, inh1 ~ InheritAttr t
  )
  => t
  -> ComposeBasedAtt syn1 inh1 syn2 inh2 ti1 to1 ti2 to2
toComposeBasedAtt trans = FinAttrTreeTrans
    { finInitialAttr   = fbInitialAttr
    , finReductionRule = fromFunctionBase rule
    }
  where
    FbAttrTreeTrans{..} = projAttrTreeTrans trans

    rule a InitialLabel          = convRhs $ fbReductionRule a InitialLabel
    rule a (RankedTreeLabel rtl) = case rtl of
      OriginalInputLabel l  -> convRhs $ fbReductionRule a $ RankedTreeLabel l
      ExtendedAttrLabel  a2 -> case a of
        SynAttr a1 -> LabelSide (ExtendedOutAttrLabel a1 a2) []
        _          -> bottomLabelSide

    convRhs rhs = case rhs of
      AttrSide  a    -> AttrSide a
      LabelSide l cs -> LabelSide (OriginalOutputLabel l) $ convRhs <$> cs

fromTreeRHS :: TreeRightHandSide syn inh ti1 -> ComposeBasedAttInputTree syn inh ti1 to1 ti2 to2
fromTreeRHS (LabelSide l ss) = OriginalInputTree l $ fromTreeRHS <$> ss
fromTreeRHS (AttrSide a)     = ExtendedAttrNode a


data ComposedAttAttr (tag :: AttAttrTag) syn1 inh1 syn2 inh2 where
  SynSynAttr :: syn1 -> syn2 -> ComposedAttAttr SynAttrTag syn1 inh1 syn2 inh2
  InhInhAttr :: inh1 -> inh2 -> ComposedAttAttr SynAttrTag syn1 inh1 syn2 inh2
  SynInhAttr :: syn1 -> inh2 -> ComposedAttAttr InhAttrTag syn1 inh1 syn2 inh2
  InhSynAttr :: inh1 -> syn2 -> ComposedAttAttr InhAttrTag syn1 inh1 syn2 inh2

deriving instance (Eq syn1, Eq inh1, Eq syn2, Eq inh2) => Eq (ComposedAttAttr tag syn1 inh1 syn2 inh2)
deriving instance (Ord syn1, Ord inh1, Ord syn2, Ord inh2) => Ord (ComposedAttAttr tag syn1 inh1 syn2 inh2)

instance (Show syn1, Show inh1, Show syn2, Show inh2) => Show (ComposedAttAttr tag syn1 inh1 syn2 inh2) where
  show (SynSynAttr a1 a2) = show (a1, a2)
  show (InhInhAttr b1 b2) = show (b1, b2)
  show (SynInhAttr a1 b2) = show (a1, b2)
  show (InhSynAttr b1 a2) = show (b1, a2)

instance (Universe syn1, Universe inh1, Universe syn2, Universe inh2)
    => Universe (ComposedAttAttr SynAttrTag syn1 inh1 syn2 inh2) where

  universe
    =  [a1 `SynSynAttr` a2 | a1 <- universe, a2 <- universe]
    <> [b1 `InhInhAttr` b2 | b1 <- universe, b2 <- universe]

instance (Finite syn1, Finite inh1, Finite syn2, Finite inh2)
  => Finite (ComposedAttAttr SynAttrTag syn1 inh1 syn2 inh2)

instance (Universe syn1, Universe inh1, Universe syn2, Universe inh2)
  => Universe (ComposedAttAttr InhAttrTag syn1 inh1 syn2 inh2) where

  universe
    =  [a1 `SynInhAttr` b2 | a1 <- universe, b2 <- universe]
    <> [b1 `InhSynAttr` a2 | b1 <- universe, a2 <- universe]

instance (Finite syn1, Finite inh1, Finite syn2, Finite inh2)
  => Finite (ComposedAttAttr InhAttrTag syn1 inh1 syn2 inh2)

instance Generic (ComposedAttAttr tag syn1 inh1 syn2 inh2) where
  type Rep (ComposedAttAttr tag syn1 inh1 syn2 inh2) = D1
    ('MetaData "ComposedAttAttr" "Data.Tree.Trans.ATT.Compose" "satt-composition" 'False)
    (   C1 ('MetaCons "SynSynAttr" 'PrefixI 'False)
          (   S1 ('MetaSel 'Nothing
                  'NoSourceUnpackedness
                  'NoSourceStrictness
                  'DecidedStrict) (Rec0 syn1)
          :*: S1 ('MetaSel 'Nothing
                  'NoSourceUnpackedness
                  'NoSourceStrictness
                  'DecidedStrict) (Rec0 syn2)
          )
    :+: C1 ('MetaCons "InhInhAttr" 'PrefixI 'False)
          (   S1 ('MetaSel 'Nothing
                  'NoSourceUnpackedness
                  'NoSourceStrictness
                  'DecidedStrict) (Rec0 inh1)
          :*: S1 ('MetaSel 'Nothing
                  'NoSourceUnpackedness
                  'NoSourceStrictness
                  'DecidedStrict) (Rec0 inh2)
          )
    :+: C1 ('MetaCons "SynInhAttr" 'PrefixI 'False)
          (   S1 ('MetaSel 'Nothing
                  'NoSourceUnpackedness
                  'NoSourceStrictness
                  'DecidedStrict) (Rec0 syn1)
          :*: S1 ('MetaSel 'Nothing
                  'NoSourceUnpackedness
                  'NoSourceStrictness
                  'DecidedStrict) (Rec0 inh2)
          )
    :+: C1 ('MetaCons "InhSynAttr" 'PrefixI 'False)
          (   S1 ('MetaSel 'Nothing
                  'NoSourceUnpackedness
                  'NoSourceStrictness
                  'DecidedStrict) (Rec0 inh1)
          :*: S1 ('MetaSel 'Nothing
                  'NoSourceUnpackedness
                  'NoSourceStrictness
                  'DecidedStrict) (Rec0 syn2)
          )
    )

  from (a1 `SynSynAttr` a2) = M1 $           L1 $ M1 $ M1 (K1 a1) :*: M1 (K1 a2)
  from (b1 `InhInhAttr` b2) = M1 $      R1 $ L1 $ M1 $ M1 (K1 b1) :*: M1 (K1 b2)
  from (a1 `SynInhAttr` b2) = M1 $ R1 $ R1 $ L1 $ M1 $ M1 (K1 a1) :*: M1 (K1 b2)
  from (b1 `InhSynAttr` a2) = M1 $ R1 $ R1 $ R1 $ M1 $ M1 (K1 b1) :*: M1 (K1 a2)

  to (M1         (L1 (M1 (M1 (K1 a1) :*: M1 (K1 a2)))))   = unsafeCoerce $ a1 `SynSynAttr` a2
  to (M1     (R1 (L1 (M1 (M1 (K1 b1) :*: M1 (K1 b2))))))  = unsafeCoerce $ b1 `InhInhAttr` b2
  to (M1 (R1 (R1 (L1 (M1 (M1 (K1 a1) :*: M1 (K1 b2))))))) = unsafeCoerce $ a1 `SynInhAttr` b2
  to (M1 (R1 (R1 (R1 (M1 (M1 (K1 b1) :*: M1 (K1 a2))))))) = unsafeCoerce $ b1 `InhSynAttr` a2

instance (Hashable syn1, Hashable inh1, Hashable syn2, Hashable inh2)
  => Hashable (ComposedAttAttr tag syn1 inh1 syn2 inh2)


type AttRuleIndex syn inh ti to
  = HashMap (AttrSide syn inh, InputLabelType ti) (InputAttr syn inh, [RankNumber])

indexAttRule ::
  ( FiniteAttrTreeTransReq syn inh ti to
  , AttrTreeTrans t ti to, syn ~ SynthesAttr t, inh ~ InheritAttr t
  )
  => t -> AttRuleIndex syn inh ti to
indexAttRule t = HM.fromList $ do
    AttRuleInputParams (a, l) <- universeF
    indexRHS a l
  where
    rule = reductionRule t

    indexRHS a l = indexRHS' a l [] (rule a l)

    indexRHS' a l p (AttrSide s)  = return ((s, l), (a, p))
    indexRHS' a l p (LabelSide _ cs) = concat $ V.ifoldl' (\r i c -> indexRHS' a l (i:p) c:r) [] cs

type ComposedAtt syn1 inh1 syn2 inh2 ti to = FiniteAttrTreeTrans
  (ComposedAttAttr SynAttrTag syn1 inh1 syn2 inh2)
  (ComposedAttAttr InhAttrTag syn1 inh1 syn2 inh2)
  ti to

-- | composition of atts
--
-- Examples:
--
-- >>> import Data.Tree.RankedTree.Instances
-- >>> import Data.Tree.Trans.Class
-- >>> import Data.Tree.Trans.ATT.Instances
-- >>> infixOpTreeSample = InfixMulti InfixTwo (InfixPlus InfixOne InfixTwo)
--
-- >>> treeTrans (identityTransducer `composeAtts` infixToPostfixTransducer) infixOpTreeSample
-- two(one(two(plus(multi($)))))
--
-- >>> treeTrans infixToPostfixTransducer . treeTrans orderExchangeTransducer $ infixOpTreeSample
-- two(one(plus(two(multi($)))))
--
-- >>> treeTrans (infixToPostfixTransducer `composeAtts` orderExchangeTransducer) infixOpTreeSample
-- two(one(plus(two(multi($)))))
--
composeAtts :: forall syn1 inh1 ti1 to1 t1 syn2 inh2 ti2 to2 t2.
  ( FiniteAttrTreeTransReq syn1 inh1 ti1 to1, RankedTree to1
  , AttrTreeTrans t1 ti1 to1, syn1 ~ SynthesAttr t1, inh1 ~ InheritAttr t1
  , to2 ~ ti1
  , FiniteAttrTreeTransReq syn2 inh2 ti2 to2, RankedTree to2
  , AttrTreeTrans t2 ti2 to2, syn2 ~ SynthesAttr t2, inh2 ~ InheritAttr t2

  , Show (LabelType ti2)
  )
  => t1 -> t2 -> ComposedAtt syn1 inh1 syn2 inh2 ti2 to1
composeAtts t1 t2 = FinAttrTreeTrans
    { finInitialAttr   = initialAttr t1 `SynSynAttr` initialAttr t2
    , finReductionRule = fromFunctionBase rule
    }
  where
    composeBasedAtt :: ComposeBasedAtt syn1 inh1 syn2 inh2 ti1 to1 ti2 to2
    composeBasedAtt = toComposeBasedAtt t1

    composeBasedAtt' = projAttrTreeTrans composeBasedAtt

    indexT2 = indexAttRule t2

    runReduction t s = runAttReduction @RTZipper s composeBasedAtt' t
    runReductionWithRep f t s = replaceReductionState f $ runReduction t s

    replaceReductionState f (RankedTreeState el ss) = case el of
      OriginalOutputLabel l                          -> LabelSide l $ replaceReductionState f <$> ss
      ExtendedOutAttrLabel a1 (TaggedSynBox (a2, j)) -> synAttrSide (a1 `SynSynAttr` a2) j
      ExtendedOutAttrLabel a1 (TaggedInhBox b2)      -> inhAttrSide (a1 `SynInhAttr` b2)
    replaceReductionState f (AttrState _ astate) = case astate of
      ReductionAttrState (TaggedInhBox b2) [] -> f b2
      _                                       -> error "reduction is not done"

    ruleT2 = reductionRule t2
    ruleT2' a = fromTreeRHS . ruleT2 a

    rule (SynAttr (a1 `SynSynAttr` a2)) l@InitialLabel = runReductionWithRep
      (\_ -> error "not permitted operation")
      (toRankedTreeWithInitial $ ruleT2' (TaggedSynBox a2) l)
      (ReductionAttrState (TaggedSynBox a1) [])
    rule (SynAttr (a1 `SynSynAttr` a2)) l@RankedTreeLabel{} = runReductionWithRep
      (\b1' -> inhAttrSide (b1' `InhSynAttr` a2))
      (toRankedTreeWithoutInitial $ ruleT2' (TaggedSynBox a2) l)
      (ReductionAttrState (TaggedSynBox a1) [])
    rule (SynAttr (b1 `InhInhAttr` b2')) l@RankedTreeLabel{} = case indexT2 ! (taggedInhBox b2', l) of
      (sa2@(SynAttr a2), w) -> runReductionWithRep
        (\b1' -> inhAttrSide (b1' `InhSynAttr` a2))
        (toRankedTreeWithoutInitial $ ruleT2' sa2 l)
        (ReductionAttrState (TaggedInhBox b1) w)
      (ib2@(InhAttr b2 j), w) -> runReductionWithRep
        (\b1' -> synAttrSide (b1' `InhInhAttr` b2) j)
        (toRankedTreeWithoutInitial $ ruleT2' ib2 l)
        (ReductionAttrState (TaggedInhBox b1) w)
    rule (SynAttr _) _ = bottomLabelSide

    rule (InhAttr (a1 `SynInhAttr` b2) 0) l@InitialLabel = runReductionWithRep
      (\b1' -> synAttrSide (b1' `InhInhAttr` b2) 0)
      (toRankedTreeWithoutInitial $ ruleT2' (TaggedInhBox (b2, 0)) l)
      (ReductionAttrState (TaggedSynBox a1) [])
    rule (InhAttr (b1 `InhSynAttr` a2') 0) l@InitialLabel = case indexT2 ! (taggedSynBox (a2', 0), l) of
      (sa2@(SynAttr _), w) -> runReductionWithRep
        (\_ -> error "not permitted operation")
        (toRankedTreeWithInitial $ ruleT2' sa2 l)
        (ReductionAttrState (TaggedInhBox b1) (w <> [0]))
      (ib2@(InhAttr b2 j), w) -> runReductionWithRep
        (\b1' -> synAttrSide (b1' `InhInhAttr` b2) j)
        (toRankedTreeWithoutInitial $ ruleT2' ib2 l)
        (ReductionAttrState (TaggedInhBox b1) w)
    rule (InhAttr (a1 `SynInhAttr` b2) j) l@RankedTreeLabel{} = runReductionWithRep
      (\b1' -> synAttrSide (b1' `InhInhAttr` b2) j)
      (toRankedTreeWithoutInitial $ ruleT2' (TaggedInhBox (b2, j)) l)
      (ReductionAttrState (TaggedSynBox a1) [])
    rule (InhAttr (b1 `InhSynAttr` a2') j') l@RankedTreeLabel{} = case indexT2 ! (taggedSynBox (a2', j'), l) of
      (sa2@(SynAttr a2), w) -> runReductionWithRep
        (\b1' -> inhAttrSide (b1' `InhSynAttr` a2))
        (toRankedTreeWithoutInitial $ ruleT2' sa2 l)
        (ReductionAttrState (TaggedInhBox b1) w)
      (ib2@(InhAttr b2 j), w) -> runReductionWithRep
        (\b1' -> synAttrSide (b1' `InhInhAttr` b2) j)
        (toRankedTreeWithoutInitial $ ruleT2' ib2 l)
        (ReductionAttrState (TaggedInhBox b1) w)
    rule (InhAttr _ _) _ = bottomLabelSide
