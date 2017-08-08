{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.ATT.Compose where

import ClassyPrelude
import qualified Data.Vector as V
import Data.TypeLevel.TaggedEither
import Data.Pattern.Error

import Data.Tree.RankedTree
import Data.Tree.Trans.ATT


type ExtendedAttAttr syn inh = AttrSide syn inh


data ExtendedInputLabel syn2 inh2 t1 l1
  = OriginalInputLabel l1
  | ExtendedAttrLabel (ExtendedAttAttr syn2 inh2)
  deriving (Show, Eq, Ord)

data ExtendedInputTree syn2 inh2 t1 l1
  = OriginalInputTree l1 (NodeVec :$ ExtendedInputTree syn2 inh2 t1 l1)
  | ExtendedAttrNode (ExtendedAttAttr syn2 inh2)
  deriving (Show, Eq, Ord)

instance (RtConstraint t1 l1) => RankedTree (ExtendedInputTree syn2 inh2 t1 l1) where
  type LabelType (ExtendedInputTree syn2 inh2 t1 l1) = ExtendedInputLabel syn2 inh2 t1 l1

  treeLabel (OriginalInputTree l _) = OriginalInputLabel l
  treeLabel (ExtendedAttrNode a)    = ExtendedAttrLabel a

  treeChilds (OriginalInputTree _ ts) = ts
  treeChilds ExtendedAttrNode{}       = []

  treeLabelRank _ (OriginalInputLabel l) = treeLabelRank (treeTag :: TreeTag t1) l
  treeLabelRank _ ExtendedAttrLabel{}    = 0

  mkTreeUnchecked (OriginalInputLabel l) ts = OriginalInputTree l ts
  mkTreeUnchecked (ExtendedAttrLabel a)  _  = ExtendedAttrNode a


data ExtendedOutputLabel syn1 inh1 syn2 inh2 t l
  = OriginalOutputLabel l
  | ExtendedOutAttrLabel syn1 (ExtendedAttAttr syn2 inh2)
  deriving (Show, Eq, Ord)

data ExtendedOutputTree syn1 inh1 syn2 inh2 t l
  = OriginalOutputTree l (NodeVec :$ ExtendedOutputTree syn1 inh1 syn2 inh2 t l)
  | ExtendedOutAttrNode syn1 (ExtendedAttAttr syn2 inh2)
  deriving (Show, Eq, Ord)

instance (RtConstraint t l) => RankedTree (ExtendedOutputTree syn1 inh1 syn2 inh2 t l) where
  type LabelType (ExtendedOutputTree syn1 inh1 syn2 inh2 t l) = ExtendedOutputLabel syn1 inh1 syn2 inh2 t l

  treeLabel (OriginalOutputTree l _)    = OriginalOutputLabel l
  treeLabel (ExtendedOutAttrNode a1 a2) = ExtendedOutAttrLabel a1 a2

  treeChilds (OriginalOutputTree _ ts) = ts
  treeChilds ExtendedOutAttrNode{}     = []

  treeLabelRank _ (OriginalOutputLabel l) = treeLabelRank (treeTag :: TreeTag t) l
  treeLabelRank _ ExtendedOutAttrLabel{}  = 0

  mkTreeUnchecked (OriginalOutputLabel l)      ts = OriginalOutputTree l ts
  mkTreeUnchecked (ExtendedOutAttrLabel a1 a2) _  = ExtendedOutAttrNode a1 a2


type ComposeBasedAttInputTree syn inh ta tb = RtApply (ExtendedInputTree syn inh) ta
type ComposeBasedAttOutputTree syn1 inh1 syn2 inh2 ta tb = RtApply (ExtendedOutputTree syn1 inh1 syn2 inh2) tb

type ComposeBasedAtt syn1 inh1 syn2 inh2 ti1 to1 = AttrTreeTrans syn1 inh1
  (ComposeBasedAttInputTree syn2 inh2 ti1 to1)
  (ComposeBasedAttOutputTree syn1 inh1 syn2 inh2 ti1 to1)

toComposeBasedAtt :: (RankedTree ti1, RankedTree to1)
  => AttrTreeTrans syn1 inh1 ti1 to1
  -> ComposeBasedAtt syn1 inh1 syn2 inh2 ti1 to1
toComposeBasedAtt AttrTreeTrans{..} = AttrTreeTrans
    { initialAttr   = initialAttr
    , reductionRule = rule
    }
  where
    rule a InitialLabel          = convRhs $ reductionRule a InitialLabel
    rule a (RankedTreeLabel rtl) = case rtl of
      OriginalInputLabel l  -> convRhs $ reductionRule a $ RankedTreeLabel l
      ExtendedAttrLabel  a2 -> case a of
        SynAttr a1 -> LabelSide (ExtendedOutAttrLabel a1 a2) []
        _          -> error "unsupported operation"

    convRhs rhs = case rhs of
      AttrSide  a    -> AttrSide a
      LabelSide l cs -> LabelSide (OriginalOutputLabel l) $ convRhs <$> cs

fromTreeRHS :: TreeRightHandSide syn inh ta -> ComposeBasedAttInputTree syn inh ta tb
fromTreeRHS (LabelSide l ss) = OriginalInputTree l $ fromTreeRHS <$> ss
fromTreeRHS (AttrSide a)     = ExtendedAttrNode a


data AttrIndexedData syn inh = AttrIndexedData (InputAttr syn inh) [RankNumber]
  deriving (Eq, Ord, Show)

newtype IndexedValue i a = IndexedValueC (i, a)
  deriving (Eq, Ord)

pattern IndexedValue :: i -> a -> IndexedValue i a
pattern IndexedValue i a = IndexedValueC (i, a)

indexedValue :: i -> a -> IndexedValue i a
indexedValue i x = IndexedValueC (i, x)

instance (Show a) => Show (IndexedValue i a) where
  show (IndexedValue _ x) = show x
  show _                  = unreachable

type AttrIndexedQueue syn inh = [AttrIndexedData syn inh]
type AttrIndexedAttr tag syn inh = IndexedValue (AttrIndexedQueue syn inh) (AttAttrEither tag syn inh)

type AttrIndexedSynAttr syn inh = AttrIndexedAttr 'SynAttrTag syn inh
type AttrIndexedInhAttr syn inh = AttrIndexedAttr 'InhAttrTag syn inh

indexedRHS :: forall tag syn inh t. RankedTree t
  => AttAttrEither tag syn (inh, RankNumber) -> AttrIndexedQueue syn inh
  -> TreeRightHandSide syn inh t
  -> TreeRightHandSide (AttrIndexedSynAttr syn inh) (AttrIndexedInhAttr syn inh) t
indexedRHS ai q = go [] where
  indexedAttr :: [RankNumber] -> a -> IndexedValue (AttrIndexedQueue syn inh) a
  indexedAttr p = indexedValue $ indexedAttr' ai p

  indexedAttr' :: AttAttrEither tag syn (inh, RankNumber) -> [RankNumber] -> AttrIndexedQueue syn inh
  indexedAttr' a p = AttrIndexedData (TaggedEitherBox a) p : q

  go p (LabelSide l cs)                 = LabelSide l . V.imap (\i -> go (i:p)) $ cs
  go p (AttrSide (TaggedSynBox (a, j))) = synAttrSide (indexedAttr p $ taggedSyn a) j
  go p (AttrSide (TaggedInhBox a))      = inhAttrSide (indexedAttr p (taggedInh a))
  go _ (AttrSide _)                     = unreachable

type AttrIndexedAtt syn2 inh2 ti2 to2 = AttrTreeTrans
  (AttrIndexedSynAttr syn2 inh2)
  (AttrIndexedInhAttr syn2 inh2)
  ti2 to2

toAttrIndexedAtt :: forall syn2 inh2 ti2 to2. (RankedTree ti2, RankedTree to2)
  => AttrTreeTrans syn2 inh2 ti2 to2
  -> AttrIndexedAtt syn2 inh2 ti2 to2
toAttrIndexedAtt AttrTreeTrans{..} = AttrTreeTrans
    { initialAttr      = indexedValue [] (taggedSyn initialAttr)
    , reductionRule = rule
    }
  where
    rule (TaggedSynBox (IndexedValue q (TaggedSyn a)))    = rule' q $ taggedSyn a
    rule (TaggedInhBox (IndexedValue q (TaggedInh a), j)) = rule' q $ taggedInh (a, j)
    rule _                                                = unreachable

    rule' :: AttrIndexedQueue syn2 inh2 -> AttAttrEither tag syn2 (inh2, RankNumber)
      -> InputLabelType ti2
      -> TreeRightHandSide (AttrIndexedSynAttr syn2 inh2) (AttrIndexedInhAttr syn2 inh2) to2
    rule' q a = indexedRHS a q . reductionRule (TaggedEitherBox a)


type ComposedAttSynAttr = ComposedAttAttr 'SynAttrTag
type ComposedAttInhAttr = ComposedAttAttr 'InhAttrTag
data ComposedAttAttr (tag :: AttAttrTag) syn1 inh1 syn2 inh2 where
  SynSynAttr :: syn1 -> AttrIndexedSynAttr syn2 inh2 -> ComposedAttSynAttr syn1 inh1 syn2 inh2
  InhInhAttr :: inh1 -> AttrIndexedInhAttr syn2 inh2 -> ComposedAttSynAttr syn1 inh1 syn2 inh2
  SynInhAttr :: syn1 -> AttrIndexedInhAttr syn2 inh2 -> ComposedAttInhAttr syn1 inh1 syn2 inh2
  InhSynAttr :: inh1 -> AttrIndexedSynAttr syn2 inh2 -> ComposedAttInhAttr syn1 inh1 syn2 inh2

deriving instance (Eq syn1, Eq inh1, Eq syn2, Eq inh2) => Eq (ComposedAttAttr tag syn1 inh1 syn2 inh2)
deriving instance (Ord syn1, Ord inh1, Ord syn2, Ord inh2) => Ord (ComposedAttAttr tag syn1 inh1 syn2 inh2)

instance (Show syn1, Show inh1, Show syn2, Show inh2) => Show (ComposedAttAttr tag syn1 inh1 syn2 inh2) where
  show (SynSynAttr a1 a2) = show (a1, a2)
  show (InhInhAttr b1 b2) = show (b1, b2)
  show (SynInhAttr a1 b2) = show (a1, b2)
  show (InhSynAttr b1 a2) = show (b1, a2)

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
    { initialAttr   = initialAttr t1 `SynSynAttr` initialAttr attrIndexedAtt
    , reductionRule = rule
    }
  where
    composeBasedAtt = toComposeBasedAtt t1
    attrIndexedAtt  = toAttrIndexedAtt t2

    runReduction t s = runAttReduction s composeBasedAtt t
    runReductionWithRep f t s = replaceReductionState f $ runReduction t s

    replaceReductionState f (RankedTreeState el ss) = case el of
      OriginalOutputLabel l                          -> LabelSide l $ replaceReductionState f <$> ss
      ExtendedOutAttrLabel a1 (TaggedSynBox (a2, j)) -> synAttrSide (a1 `SynSynAttr` a2) j
      ExtendedOutAttrLabel a1 (TaggedInhBox b2)      -> inhAttrSide (a1 `SynInhAttr` b2)
      _                                              -> unreachable
    replaceReductionState f (AttrState _ astate) = case astate of
      ReductionAttrState (TaggedInhBox b2) [] -> f b2
      _                                       -> error "reduction is not done"

    ruleT2 = reductionRule attrIndexedAtt
    ruleT2' a = fromTreeRHS . ruleT2 a

    rule (SynAttr (a1 `SynSynAttr` a2)) l@InitialLabel = runReductionWithRep
      (\_ -> error "not permitted operation")
      (toRankedTreeWithInitial $ ruleT2' (TaggedSynBox a2) l)
      (ReductionAttrState (TaggedSynBox a1) [])
    rule (SynAttr (a1 `SynSynAttr` a2)) l@(RankedTreeLabel _) = runReductionWithRep
      (\b1' -> inhAttrSide (b1' `InhSynAttr` a2))
      (toRankedTreeWithoutInitial $ ruleT2' (TaggedSynBox a2) l)
      (ReductionAttrState (TaggedSynBox a1) [])
    rule (SynAttr (b1 `InhInhAttr` IndexedValue (x:q) _)) l@(RankedTreeLabel _) = case x of
      AttrIndexedData (TaggedSynBox a2) w ->
        let ia2 = indexedValue q (taggedSyn a2) in runReductionWithRep
          (\b1' -> inhAttrSide (b1' `InhSynAttr` ia2))
          (toRankedTreeWithoutInitial $ ruleT2' (TaggedSynBox ia2) l)
          (ReductionAttrState (TaggedInhBox b1) w)
      AttrIndexedData (TaggedInhBox (b2, j)) w ->
        let ib2 = indexedValue q (taggedInh b2) in runReductionWithRep
          (\b1' -> synAttrSide (b1' `InhInhAttr` ib2) j)
          (toRankedTreeWithoutInitial $ ruleT2' (TaggedInhBox (ib2, j)) l)
          (ReductionAttrState (TaggedInhBox b1) w)
      _                   -> unreachable
    rule (SynAttr _) _ = bottomLabelSide

    rule (InhAttr (a1 `SynInhAttr` b2) 0) l@InitialLabel = runReductionWithRep
      (\b1' -> synAttrSide (b1' `InhInhAttr` b2) 0)
      (toRankedTreeWithoutInitial $ ruleT2' (TaggedInhBox (b2, 0)) l)
      (ReductionAttrState (TaggedSynBox a1) [])
    rule (InhAttr (b1 `InhSynAttr` IndexedValue (x:q) _) 0) l@InitialLabel = case x of
      AttrIndexedData (TaggedSynBox a2) w ->
        let ia2 = indexedValue q (taggedSyn a2) in runReductionWithRep
          (\_ -> error "not permitted operation")
          (toRankedTreeWithInitial $ ruleT2' (TaggedSynBox ia2) l)
          (ReductionAttrState (TaggedInhBox b1) (w <> [0]))
      AttrIndexedData (TaggedInhBox (b2, j)) w ->
        let ib2 = indexedValue q (taggedInh b2) in runReductionWithRep
          (\b1' -> synAttrSide (b1' `InhInhAttr` ib2) j)
          (toRankedTreeWithoutInitial $ ruleT2' (TaggedInhBox (ib2, j)) l)
          (ReductionAttrState (TaggedInhBox b1) w)
      _ -> unreachable
    rule (InhAttr (a1 `SynInhAttr` b2) j) l@(RankedTreeLabel _) = runReductionWithRep
      (\b1' -> synAttrSide (b1' `InhInhAttr` b2) j)
      (toRankedTreeWithoutInitial $ ruleT2' (TaggedInhBox (b2, j)) l)
      (ReductionAttrState (TaggedSynBox a1) [])
    rule (InhAttr (b1 `InhSynAttr` IndexedValue (x:q) _) _) l@(RankedTreeLabel _) = case x of
      AttrIndexedData (TaggedSynBox a2) w ->
        let ia2 = indexedValue q (taggedSyn a2) in runReductionWithRep
          (\b1' -> inhAttrSide (b1' `InhSynAttr` ia2))
          (toRankedTreeWithoutInitial $ ruleT2' (TaggedSynBox ia2) l)
          (ReductionAttrState (TaggedInhBox b1) w)
      AttrIndexedData (TaggedInhBox (b2, j)) w ->
        let ib2 = indexedValue q (taggedInh b2) in runReductionWithRep
          (\b1' -> synAttrSide (b1' `InhInhAttr` ib2) j)
          (toRankedTreeWithoutInitial $ ruleT2' (TaggedInhBox (ib2, j)) l)
          (ReductionAttrState (TaggedInhBox b1) w)
      _ -> unreachable
    rule (InhAttr _ _) _ = bottomLabelSide

    rule _ _ = unreachable
