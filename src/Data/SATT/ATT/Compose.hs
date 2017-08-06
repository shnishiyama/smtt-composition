{-# LANGUAGE OverloadedLists #-}

module Data.SATT.ATT.Compose where

import ClassyPrelude
import qualified Data.Vector as V

import Data.Tree.RankedTree
import Data.SATT.ATT


data ExtendedInputLabel syn2 inh2 t1 l1
  = OriginalInputLabel l1
  | ExtendedSynAttrLabel syn2 RankNumber
  | ExtendedInhAttrLabel inh2
  deriving (Show, Eq, Ord)

data ExtendedInputTree syn2 inh2 t1 l1
  = OriginalInputTree l1 (NodeVec :$ ExtendedInputTree syn2 inh2 t1 l1)
  | ExtendedSynAttrNode syn2 RankNumber
  | ExtendedInhAttrNode inh2
  deriving (Show, Eq, Ord)

instance (RtConstraint t1 l1) => RankedTree (ExtendedInputTree syn2 inh2 t1 l1) where
  type LabelType (ExtendedInputTree syn2 inh2 t1 l1) = ExtendedInputLabel syn2 inh2 t1 l1

  treeLabel (OriginalInputTree l _)     = OriginalInputLabel l
  treeLabel (ExtendedSynAttrNode syn i) = ExtendedSynAttrLabel syn i
  treeLabel (ExtendedInhAttrNode inh)   = ExtendedInhAttrLabel inh

  treeChilds (OriginalInputTree _ ts) = ts
  treeChilds ExtendedSynAttrNode{}    = []
  treeChilds ExtendedInhAttrNode{}    = []

  treeLabelRank _ (OriginalInputLabel l) = treeLabelRank (treeTag :: TreeTag t1) l
  treeLabelRank _ ExtendedSynAttrLabel{} = 0
  treeLabelRank _ ExtendedInhAttrLabel{} = 0

  mkTreeUnchecked (OriginalInputLabel l)     ts = OriginalInputTree l ts
  mkTreeUnchecked (ExtendedSynAttrLabel a n) _  = ExtendedSynAttrNode a n
  mkTreeUnchecked (ExtendedInhAttrLabel a)   _  = ExtendedInhAttrNode a


data ExtendedOutputLabel syn1 inh1 syn2 inh2 t l
  = OriginalOutputLabel l
  | ExtendedOutSynAttrLabel syn1 syn2 RankNumber
  | ExtendedOutInhAttrLabel syn1 inh2
  deriving (Show, Eq, Ord)

data ExtendedOutputTree syn1 inh1 syn2 inh2 t l
  = OriginalOutputTree l (NodeVec :$ ExtendedOutputTree syn1 inh1 syn2 inh2 t l)
  | ExtendedOutSynAttrNode syn1 syn2 RankNumber
  | ExtendedOutInhAttrNode syn1 inh2
  deriving (Show, Eq, Ord)

instance (RtConstraint t l) => RankedTree (ExtendedOutputTree syn1 inh1 syn2 inh2 t l) where
  type LabelType (ExtendedOutputTree syn1 inh1 syn2 inh2 t l) = ExtendedOutputLabel syn1 inh1 syn2 inh2 t l

  treeLabel (OriginalOutputTree l _)         = OriginalOutputLabel l
  treeLabel (ExtendedOutSynAttrNode a1 a2 n) = ExtendedOutSynAttrLabel a1 a2 n
  treeLabel (ExtendedOutInhAttrNode a1 a2)   = ExtendedOutInhAttrLabel a1 a2

  treeChilds (OriginalOutputTree _ ts) = ts
  treeChilds ExtendedOutSynAttrNode{}  = []
  treeChilds ExtendedOutInhAttrNode{}  = []

  treeLabelRank _ (OriginalOutputLabel l)   = treeLabelRank (treeTag :: TreeTag t) l
  treeLabelRank _ ExtendedOutSynAttrLabel{} = 0
  treeLabelRank _ ExtendedOutInhAttrLabel{} = 0

  mkTreeUnchecked (OriginalOutputLabel l)           ts = OriginalOutputTree l ts
  mkTreeUnchecked (ExtendedOutSynAttrLabel a1 a2 n) _  = ExtendedOutSynAttrNode a1 a2 n
  mkTreeUnchecked (ExtendedOutInhAttrLabel a1 a2)   _  = ExtendedOutInhAttrNode a1 a2


type ComposeBasedAttInputTree syn inh ta tb = RtApply (ExtendedInputTree syn inh) ta
type ComposeBasedAttOutputTree syn1 inh1 syn2 inh2 ta tb = RtApply (ExtendedOutputTree syn1 inh1 syn2 inh2) tb

type ComposeBasedAtt syn1 inh1 syn2 inh2 ti1 to1 = AttrTreeTrans syn1 inh1
  (ComposeBasedAttInputTree syn2 inh2 ti1 to1)
  (ComposeBasedAttOutputTree syn1 inh1 syn2 inh2 ti1 to1)

toComposeBasedAtt :: (RankedTree ti1, RankedTree to1)
  => AttrTreeTrans syn1 inh1 ti1 to1
  -> ComposeBasedAtt syn1 inh1 syn2 inh2 ti1 to1
toComposeBasedAtt AttrTreeTrans{..} = AttrTreeTrans
    { initialAttr     = initialAttr
    , synthesizedRule = synRule
    , inheritedRule   = inhRule
    }
  where
    synRule a1  InitialLabel          = convRhs $ synthesizedRule a1 InitialLabel
    synRule a1  (RankedTreeLabel rtl) = case rtl of
      OriginalInputLabel l      -> convRhs $ synthesizedRule a1 $ RankedTreeLabel l
      ExtendedSynAttrLabel a2 j -> LabelSide (ExtendedOutSynAttrLabel a1 a2 j) []
      ExtendedInhAttrLabel b2   -> LabelSide (ExtendedOutInhAttrLabel a1 b2)   []

    inhRule b1 j InitialLabel          = convRhs $ inheritedRule b1 j InitialLabel
    inhRule b1 j (RankedTreeLabel rtl) = case rtl of
      OriginalInputLabel l  -> convRhs $ inheritedRule b1 j $ RankedTreeLabel l
      _                     -> error "not permitted operation"

    convRhs rhs = case rhs of
      SynAttrSide a j -> SynAttrSide a j
      InhAttrSide a   -> InhAttrSide a
      LabelSide l cs  -> LabelSide (OriginalOutputLabel l) $ convRhs <$> cs

fromTreeRHS :: TreeRightHandSide syn inh ta -> ComposeBasedAttInputTree syn inh ta tb
fromTreeRHS (LabelSide l ss)  = OriginalInputTree l $ fromTreeRHS <$> ss
fromTreeRHS (SynAttrSide a j) = ExtendedSynAttrNode a j
fromTreeRHS (InhAttrSide a)   = ExtendedInhAttrNode a


data AttAttrTag
  = SynAttrTag
  | InhAttrTag
  deriving (Eq, Ord, Show, Enum)

type AttAttrSynIdentity = AttAttrIdentity 'SynAttrTag
type AttAttrInhIdentity = AttAttrIdentity 'InhAttrTag

data AttAttrIdentity (tag :: AttAttrTag) syn inh where
  SynAttrIdentity :: syn -> AttAttrSynIdentity syn inh
  InhAttrIdentity :: inh -> AttAttrInhIdentity syn inh

instance (Eq syn, Eq inh) => Eq (AttAttrIdentity tag syn inh) where
  SynAttrIdentity x == SynAttrIdentity y = x == y
  InhAttrIdentity x == InhAttrIdentity y = x == y

instance (Ord syn, Ord inh) => Ord (AttAttrIdentity tag syn inh) where
  SynAttrIdentity x `compare` SynAttrIdentity y = compare x y
  InhAttrIdentity x `compare` InhAttrIdentity y = compare x y

instance (Show syn, Show inh) => Show (AttAttrIdentity tag syn inh) where
  show (SynAttrIdentity x) = show x
  show (InhAttrIdentity x) = show x

data AttrIndexedData syn inh
  = AttrIndexedSynData syn [RankNumber]
  | AttrIndexedInhData inh RankNumber [RankNumber]
  deriving (Eq, Ord, Show)

newtype IndexedValue i a = IndexedValue (i, a)
  deriving (Eq, Ord)

indexedValue :: i -> a -> IndexedValue i a
indexedValue i x = IndexedValue (i, x)

instance (Show a) => Show (IndexedValue i a) where
  show (IndexedValue (_, x)) = show x

type AttrIndexedQueue syn inh = [AttrIndexedData (AttAttrSynIdentity syn inh) (AttAttrInhIdentity syn inh)]
type AttrIndexedAttr tag syn inh = IndexedValue (AttrIndexedQueue syn inh) (AttAttrIdentity tag syn inh)

type AttrIndexedSynAttr syn inh = AttrIndexedAttr 'SynAttrTag syn inh
type AttrIndexedInhAttr syn inh = AttrIndexedAttr 'InhAttrTag syn inh

indexedRHS :: forall tag syn inh t. RankedTree t
  => AttAttrIdentity tag syn (inh, RankNumber) -> AttrIndexedQueue syn inh
  -> TreeRightHandSide syn inh t
  -> TreeRightHandSide (AttrIndexedSynAttr syn inh) (AttrIndexedInhAttr syn inh) t
indexedRHS ai q = go [] where
  indexedAttr :: [RankNumber] -> a -> IndexedValue (AttrIndexedQueue syn inh) a
  indexedAttr p x = IndexedValue (indexedAttr' ai p, x)

  indexedAttr' :: AttAttrIdentity tag syn (inh, RankNumber) -> [RankNumber] -> AttrIndexedQueue syn inh
  indexedAttr' (SynAttrIdentity a)      p = AttrIndexedSynData (SynAttrIdentity a)   p : q
  indexedAttr' (InhAttrIdentity (b, j)) p = AttrIndexedInhData (InhAttrIdentity b) j p : q

  go p (LabelSide l cs)  = LabelSide l . V.imap (\i -> go (i:p)) $ cs
  go p (SynAttrSide a j) = SynAttrSide (indexedAttr p $ SynAttrIdentity a) j
  go p (InhAttrSide b)   = InhAttrSide (indexedAttr p $ InhAttrIdentity b)

type AttrIndexedAtt syn2 inh2 ti2 to2 = AttrTreeTrans
  (AttrIndexedSynAttr syn2 inh2)
  (AttrIndexedInhAttr syn2 inh2)
  ti2 to2

toAttrIndexedAtt :: forall syn2 inh2 ti2 to2. (RankedTree ti2, RankedTree to2)
  => AttrTreeTrans syn2 inh2 ti2 to2
  -> AttrIndexedAtt syn2 inh2 ti2 to2
toAttrIndexedAtt AttrTreeTrans{..} = AttrTreeTrans
    { initialAttr     = indexedValue [] (SynAttrIdentity initialAttr)
    , synthesizedRule = synRule
    , inheritedRule   = inhRule
    }
  where
    synRule (IndexedValue (q, SynAttrIdentity a2))
      = indexedRHS (SynAttrIdentity a2)      q . synthesizedRule a2
    inhRule (IndexedValue (q, InhAttrIdentity b2)) j
      = indexedRHS (InhAttrIdentity (b2, j)) q . inheritedRule b2 j

data ComposedAttSynAttr syn1 inh1 syn2 inh2
  = SynSynAttr syn1 (AttrIndexedSynAttr syn2 inh2)
  | InhInhAttr inh1 (AttrIndexedInhAttr syn2 inh2)
  deriving (Eq, Ord)

instance (Show syn1, Show inh1, Show syn2, Show inh2) => Show (ComposedAttSynAttr syn1 inh1 syn2 inh2) where
  show (SynSynAttr a1 a2) = show (a1, a2)
  show (InhInhAttr a1 a2) = show (a1, a2)

data ComposedAttInhAttr syn1 inh1 syn2 inh2
  = InhSynAttr inh1 (AttrIndexedSynAttr syn2 inh2)
  | SynInhAttr syn1 (AttrIndexedInhAttr syn2 inh2)
  deriving (Eq, Ord)

instance (Show syn1, Show inh1, Show syn2, Show inh2) => Show (ComposedAttInhAttr syn1 inh1 syn2 inh2) where
  show (SynInhAttr a1 a2) = show (a1, a2)
  show (InhSynAttr a1 a2) = show (a1, a2)


type ComposedAtt syn1 inh1 syn2 inh2 ti to = AttrTreeTrans
  (ComposedAttSynAttr syn1 inh1 syn2 inh2)
  (ComposedAttInhAttr syn1 inh1 syn2 inh2)
  ti to

composeAtts :: forall syn1 inh1 ti1 to1 syn2 inh2 ti2 to2.
  ( RankedTree ti1, RankedTree to1
  , to2 ~ ti1
  , RankedTree ti2, RankedTree to2
  )
  => AttrTreeTrans syn1 inh1 ti1 to1
  -> AttrTreeTrans syn2 inh2 ti2 to2
  -> ComposedAtt syn1 inh1 syn2 inh2 ti2 to1
composeAtts t1 t2 = AttrTreeTrans
    { initialAttr     = initialAttr t1 `SynSynAttr` initialAttr attrIndexedAtt
    , synthesizedRule = synRule
    , inheritedRule   = inhRule
    }
  where
    composeBasedAtt = toComposeBasedAtt t1
    attrIndexedAtt  = toAttrIndexedAtt t2

    runReduction t s = runAttReduction s composeBasedAtt t
    runReductionWithRep f t s = replaceReductionState f $ runReduction t s

    replaceReductionState f (RankedTreeState el ss) = case el of
      OriginalOutputLabel l           -> LabelSide l $ replaceReductionState f <$> ss
      ExtendedOutSynAttrLabel a1 a2 j -> SynAttrSide (SynSynAttr a1 a2) j
      ExtendedOutInhAttrLabel a1 a2   -> InhAttrSide (SynInhAttr a1 a2)
    replaceReductionState f (AttrState _ astate) = case astate of
      InhAttrState a [] -> f a
      _                 -> error "reduction is not done"

    synRuleT2 = synthesizedRule attrIndexedAtt
    synRuleT2' a = fromTreeRHS . synRuleT2 a

    inhRuleT2 = inheritedRule attrIndexedAtt
    inhRuleT2' a j = fromTreeRHS . inhRuleT2 a j

    synRule (a1 `SynSynAttr` a2) l@InitialLabel        = runReductionWithRep
      (\_ -> error "unsupported operation")
      (toRankedTreeWithInitial $ synRuleT2' a2 l)
      (SynAttrState a1 [])
    synRule (a1 `SynSynAttr` a2) l@(RankedTreeLabel _) = runReductionWithRep
      (\b1' -> InhAttrSide (b1' `InhSynAttr` a2))
      (toRankedTreeWithoutInitial $ synRuleT2' a2 l)
      (SynAttrState a1 [])
    synRule (b1 `InhInhAttr` IndexedValue (x:q, _)) l@(RankedTreeLabel _) = case x of
      AttrIndexedSynData a2 w ->
        let ia2 = indexedValue q a2
        in runReductionWithRep
          (\b1' -> InhAttrSide (b1' `InhSynAttr` ia2))
          (toRankedTreeWithoutInitial $ synRuleT2' ia2 l)
          (InhAttrState b1 w)
      AttrIndexedInhData b2 j w ->
        let ib2 = indexedValue q b2
        in runReductionWithRep
          (\b1' -> SynAttrSide (b1' `InhInhAttr` ib2) j)
          (toRankedTreeWithoutInitial $ inhRuleT2' ib2 j l)
          (InhAttrState b1 w)
    synRule _ _ = bottomLabelSide

    inhRule (a1 `SynInhAttr` b2)  0 l@InitialLabel                     = runReductionWithRep
      (\b1' -> SynAttrSide (InhInhAttr b1' b2) 0)
      (toRankedTreeWithoutInitial $ inhRuleT2' b2 0 l)
      (SynAttrState a1 [])
    inhRule (b1 `InhSynAttr` IndexedValue (x:q, _)) 0 l@InitialLabel = case x of
      AttrIndexedSynData a2 w ->
        let ia2 = indexedValue q a2
        in runReductionWithRep
          (\_ -> error "unsupported operation")
          (toRankedTreeWithInitial $ synRuleT2' ia2 l)
          (InhAttrState b1 $ w <> [0])
      AttrIndexedInhData b2 j w ->
        let ib2 = indexedValue q b2
        in runReductionWithRep
          (\b1' -> SynAttrSide (b1' `InhInhAttr` ib2) j)
          (toRankedTreeWithoutInitial $ inhRuleT2' ib2 j l)
          (InhAttrState b1 w)
    inhRule (a1 `SynInhAttr` b2)  j l@(RankedTreeLabel _) = runReductionWithRep
      (\b1' -> SynAttrSide (InhInhAttr b1' b2) j)
      (toRankedTreeWithoutInitial $ inhRuleT2' b2 j l)
      (SynAttrState a1 [])
    inhRule (b1 `InhSynAttr` IndexedValue (x:q, _)) _ l@(RankedTreeLabel _) = case x of
      AttrIndexedSynData a2 w ->
        let ia2 = indexedValue q a2
        in runReductionWithRep
          (\b1' -> InhAttrSide (b1' `InhSynAttr` ia2))
          (toRankedTreeWithoutInitial $ synRuleT2' ia2 l)
          (InhAttrState b1 w)
      AttrIndexedInhData b2 j w ->
        let ib2 = indexedValue q b2
        in runReductionWithRep
          (\b1' -> SynAttrSide (b1' `InhInhAttr` ib2) j)
          (toRankedTreeWithoutInitial $ inhRuleT2' ib2 j l)
          (InhAttrState b1 w)
    inhRule _                     _ _                     = bottomLabelSide
