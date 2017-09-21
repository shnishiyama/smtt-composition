{-# LANGUAGE OverloadedLists #-}
{-# LANGUAGE TypeInType      #-}

module Data.Tree.Trans.SATT.Compose where

import           ClassyPrelude

import           Data.Pattern.Error
import           Data.TypeLevel.TaggedEither

import           Data.Tree.RankedTree
import qualified Data.Tree.Trans.ATT         as ATT
import           Data.Tree.Trans.ATT.Compose (ComposedAttAttr (..),
                                              IndexedValue (..),
                                              pattern IndexedValue,
                                              indexedValue)
import qualified Data.Tree.Trans.ATT.Compose as ATTC
import           Data.Tree.Trans.SATT

type SimuratedAttAttr out stk = SattAttrEitherBox out (stk, RankNumber)

simurateSatt :: forall syn inh stsyn stinh ta tb.
  (RankedTree ta, RankedTree tb)
  => StackAttrTreeTrans syn inh stsyn stinh ta tb
  -> ATT.AttrTreeTrans (SimuratedAttAttr syn stsyn) (SimuratedAttAttr inh stinh) ta tb
simurateSatt StackAttrTreeTrans{..} = ATT.AttrTreeTrans
    { ATT.initialAttr   = taggedOutBox initialAttr
    , ATT.reductionRule = rule
    }
  where
    simOutTag = taggedOut ()
    simStkTag = taggedStk

    simuration
      :: SattAttrEither tag () RankNumber -> TreeRightHandSide tag syn inh stsyn stinh tb
      -> ATT.TreeRightHandSide (SimuratedAttAttr syn stsyn) (SimuratedAttAttr inh stinh) tb
    simuration _             (AttrSide (TaggedOut a))
      = ATT.AttrSide $ bimap (first taggedOutBox) taggedOutBox a
    simuration (TaggedStk i) (AttrSide (TaggedStk a))
      = ATT.AttrSide $ bimap (first $ taggedStkBox . (, i)) (taggedStkBox . (, i)) a
    simuration (TaggedStk 0) (StackConsSide h _)
      = simuration simOutTag h
    simuration (TaggedStk i) (StackConsSide _ t)
      = simuration (simStkTag $ i - 1) t
    simuration _             StackEmptySide
      = ATT.bottomLabelSide
    simuration _             (StackHeadSide h)
      = simuration (simStkTag 0) h
    simuration (TaggedStk i) (StackTailSide t)
      = simuration (simStkTag $ i + 1) t
    simuration _             (LabelSide l cs)
      = ATT.LabelSide l $ simuration simOutTag <$> cs

    rule (ATT.SynAttr a)   = rule' (reductionRule . bimap taggedSynBox taggedSynBox) a
    rule (ATT.InhAttr a i) = rule' (reductionRule . bimap (taggedInhBox . (,i)) (taggedInhBox . (,i))) a

    rule'
      :: (forall tag. SattAttrEither tag out stk -> InputLabelType ta -> TreeRightHandSide tag syn inh stsyn stinh tb)
      -> SimuratedAttAttr out stk
      -> InputLabelType ta -> ATT.TreeRightHandSide (SimuratedAttAttr syn stsyn) (SimuratedAttAttr inh stinh) tb
    rule' f (TaggedOutBox a) = simuration simOutTag . f (taggedOut a)
    rule' f (TaggedStkBox s) = case s of (a, i) -> simuration (simStkTag i) . f (taggedStk a)

standardForm :: forall syn inh stsyn stinh ta tb.
  (RankedTree ta, RankedTree tb)
  => StackAttrTreeTrans syn inh stsyn stinh ta tb -> StackAttrTreeTrans syn inh stsyn stinh ta tb
standardForm StackAttrTreeTrans{..} = StackAttrTreeTrans
    { initialAttr   = initialAttr
    , reductionRule = rule
    }
  where
    evaluation :: TreeRightHandSide tag syn inh stsyn stinh tb -> TreeRightHandSide tag syn inh stsyn stinh tb
    evaluation (StackHeadSide t)   = case evaluation t of
      StackConsSide h _ -> h
      StackEmptySide    -> bottomLabelSide
      t'                -> StackHeadSide t'
    evaluation (LabelSide l cs)    = LabelSide l $ evaluation <$> cs
    evaluation (StackConsSide h t) = StackConsSide (evaluation h) (evaluation t)
    evaluation (StackTailSide t)   = case evaluation t of
      StackConsSide _ t' -> t'
      StackEmptySide     -> StackEmptySide
      t'                 -> StackTailSide t'
    evaluation t                   = t

    rule :: SattRuleType tag syn inh stsyn stinh ta tb
    rule a = evaluation . reductionRule a


type SimAttrIndexer syn2 inh2 stsyn2 stinh2
  = ATTC.AttrIndexer (SimuratedAttAttr syn2 stsyn2) (SimuratedAttAttr inh2 stinh2)
type AttrIndexedAttr tags taga syn2 inh2 stsyn2 stinh2
  = SimAttrIndexer syn2 inh2 stsyn2 stinh2
    (SattAttrEither tags (AttAttrEither taga syn2 inh2) (AttAttrEither taga stsyn2 stinh2))

type SimAttAttr tag syn inh stsyn stinh
  = AttAttrEither tag (SimuratedAttAttr syn stsyn) (SimuratedAttAttr inh stinh)

simSynAttr :: () => tag ~ SynAttrTag
  => syn -> SimAttAttr tag syn inh stsyn stinh
simSynAttr a = taggedSyn $ taggedOutBox a

simStSynAttr :: () => tag ~ SynAttrTag
  => stsyn -> RankNumber -> SimAttAttr tag syn inh stsyn stinh
simStSynAttr a i = taggedSyn $ taggedStkBox (a, i)

simInhAttr :: () => tag ~ InhAttrTag
  => inh -> SimAttAttr tag syn inh stsyn stinh
simInhAttr a = taggedInh $ taggedOutBox a

simStInhAttr :: () => tag ~ InhAttrTag
  => stinh -> RankNumber -> SimAttAttr tag syn inh stsyn stinh
simStInhAttr a i = taggedInh $ taggedStkBox (a, i)

pattern SimSynAttr :: () => tag ~ SynAttrTag
  => syn -> SimAttAttr tag syn inh stsyn stinh
pattern SimSynAttr   a = TaggedSyn (TaggedOutBox a)

pattern SimStSynAttr :: () => tag ~ SynAttrTag
  => stsyn -> RankNumber -> SimAttAttr tag syn inh stsyn stinh
pattern SimStSynAttr s i = TaggedSyn (TaggedStkBox (s, i))

{-# COMPLETE SimSynAttr, SimStSynAttr #-}

pattern SimInhAttr :: () => tag ~ InhAttrTag
  => inh -> SimAttAttr tag syn inh stsyn stinh
pattern SimInhAttr   a = TaggedInh (TaggedOutBox a)

pattern SimStInhAttr :: () => tag ~ InhAttrTag
  => stinh -> RankNumber -> SimAttAttr tag syn inh stsyn stinh
pattern SimStInhAttr s i = TaggedInh (TaggedStkBox (s, i))

{-# COMPLETE SimInhAttr, SimStInhAttr #-}


newtype ComposedSattAttr (tags :: SattAttrTag) (taga :: AttAttrTag) syn1 inh1 syn2 inh2 stsyn2 stinh2
  = ComposedSattAttr
  { unComposedSattAttr :: SattAttrEither tags
    (ComposedAttAttr taga syn1 inh1 syn2 inh2)
    (ComposedAttAttr taga syn1 inh1 stsyn2 stinh2)
  }

pattern ComposedSattOutAttr :: () => (tags ~ OutAttrTag)
  => ComposedAttAttr taga syn1 inh1 syn2 inh2
  -> ComposedSattAttr tags taga syn1 inh1 syn2 inh2 stsyn2 stinh2
pattern ComposedSattOutAttr x = ComposedSattAttr (TaggedOut x)

pattern ComposedSattStkAttr :: () => (tags ~ StkAttrTag)
  => ComposedAttAttr taga syn1 inh1 stsyn2 stinh2
  -> ComposedSattAttr tags taga syn1 inh1 syn2 inh2 stsyn2 stinh2
pattern ComposedSattStkAttr x = ComposedSattAttr (TaggedStk x)


composedSattOutAttr
  :: ATTC.ComposedAttAttr taga syn1 inh1 syn2 inh2
  -> ComposedSattAttr OutAttrTag taga syn1 inh1 syn2 inh2 stsyn2 stinh2
composedSattOutAttr = ComposedSattAttr . taggedOut

composedSattStkAttr
  :: ATTC.ComposedAttAttr taga syn1 inh1 stsyn2 stinh2
  -> ComposedSattAttr StkAttrTag taga syn1 inh1 syn2 inh2 stsyn2 stinh2
composedSattStkAttr = ComposedSattAttr . taggedStk


deriving instance (Eq syn1, Eq inh1, Eq syn2, Eq inh2, Eq stsyn2, Eq stinh2)
  => Eq (ComposedSattAttr tags taga syn1 inh1 syn2 inh2 stsyn2 stinh2)
deriving instance (Ord syn1, Ord inh1, Ord syn2, Ord inh2, Ord stsyn2, Ord stinh2)
  => Ord (ComposedSattAttr tags taga syn1 inh1 syn2 inh2 stsyn2 stinh2)

instance (Show syn1, Show inh1, Show syn2, Show inh2, Show stsyn2, Show stinh2)
  => Show (ComposedSattAttr tags taga syn1 inh1 syn2 inh2 stsyn2 stinh2) where
    show (ComposedSattAttr x) = case x of
      TaggedOut a -> show a
      TaggedStk a -> show a

type ComposedIndexedSattAttr tags taga syn1 inh1 syn2 inh2 stsyn2 stinh2
   = ComposedSattAttr tags taga syn1 inh1
     (AttrIndexedAttr OutAttrTag SynAttrTag syn2 inh2 stsyn2 stinh2)
     (AttrIndexedAttr OutAttrTag InhAttrTag syn2 inh2 stsyn2 stinh2)
     (AttrIndexedAttr StkAttrTag SynAttrTag syn2 inh2 stsyn2 stinh2)
     (AttrIndexedAttr StkAttrTag InhAttrTag syn2 inh2 stsyn2 stinh2)

type ComposedSatt syn1 inh1 syn2 inh2 stsyn2 stinh2 ti2 to1
  = StackAttrTreeTrans
    (ComposedIndexedSattAttr OutAttrTag SynAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
    (ComposedIndexedSattAttr OutAttrTag InhAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
    (ComposedIndexedSattAttr StkAttrTag SynAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
    (ComposedIndexedSattAttr StkAttrTag InhAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
    ti2 to1

composeSatts :: forall syn1 inh1 ti1 to1 syn2 inh2 stsyn2 stinh2 ti2 to2.
  ( RankedTree ti1, RankedTree to1
  , to2 ~ ti1
  , RankedTree ti2, RankedTree to2
  )
  => ATT.AttrTreeTrans syn1 inh1 ti1 to1
  -> StackAttrTreeTrans syn2 inh2 stsyn2 stinh2 ti2 to2
  -> ComposedSatt syn1 inh1 syn2 inh2 stsyn2 stinh2 ti2 to1
composeSatts trans1 trans2 = StackAttrTreeTrans
    { initialAttr   = composedSattOutAttr
    $ initialAttrT1 `SynSynAttr` indexedValue [] (taggedOut $ taggedSyn initialAttrT2)
    , reductionRule = rule
    }
  where
    initialAttrT1 = ATT.initialAttr trans1
    initialAttrT2 = initialAttr sfT2

    sfT2 = standardForm trans2
    simsfT2 = simurateSatt sfT2

    composedT1AndSimsfT2 = trans1 `ATTC.composeAtts` simsfT2
    ruleBase = ATT.reductionRule composedT1AndSimsfT2

    retailN t 0 = t
    retailN t l = retailN (StackTailSide t) $ l - 1

    runReductionWithRep a = runReductionWithRep' . ruleBase a

    runReductionWithRep'
      :: ATT.TreeRightHandSide
        (ATTC.ComposedIndexedAttAttr SynAttrTag syn1 inh1
          (SimuratedAttAttr syn2 stsyn2)
          (SimuratedAttAttr inh2 stinh2))
        (ATTC.ComposedIndexedAttAttr InhAttrTag syn1 inh1
          (SimuratedAttAttr syn2 stsyn2)
          (SimuratedAttAttr inh2 stinh2))
        to1
      -> TreeOutRightHandSide
        (ComposedIndexedSattAttr OutAttrTag SynAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
        (ComposedIndexedSattAttr OutAttrTag InhAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
        (ComposedIndexedSattAttr StkAttrTag SynAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
        (ComposedIndexedSattAttr StkAttrTag InhAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
        to1
    runReductionWithRep' (ATT.AttrSide abox)  = case abox of
      TaggedSynBox (a, j) -> case a of
        a1 `SynSynAttr` IndexedValue q (SimSynAttr   a2)   -> synAttrSide (composedSattOutAttr $ a1 `SynSynAttr` indexedValue q (taggedOut $ taggedSyn a2)) j
        a1 `SynSynAttr` IndexedValue q (SimStSynAttr s2 i) -> StackHeadSide $ retailN (stsynAttrSide (composedSattStkAttr $ a1 `SynSynAttr` indexedValue q (taggedStk $ taggedSyn s2)) j) i
        b1 `InhInhAttr` IndexedValue q (SimInhAttr   b2)   -> synAttrSide (composedSattOutAttr $ b1 `InhInhAttr` indexedValue q (taggedOut $ taggedInh b2)) j
        b1 `InhInhAttr` IndexedValue q (SimStInhAttr d2 i) -> StackHeadSide $ retailN (stsynAttrSide (composedSattStkAttr $ b1 `InhInhAttr` indexedValue q (taggedStk $ taggedInh d2)) j) i
      TaggedInhBox b      -> case b of
        a1 `SynInhAttr` IndexedValue q (SimInhAttr   b2)   -> inhAttrSide (composedSattOutAttr $ a1 `SynInhAttr` indexedValue q (taggedOut $ taggedInh b2))
        a1 `SynInhAttr` IndexedValue q (SimStInhAttr d2 i) -> StackHeadSide $ retailN (stinhAttrSide (composedSattStkAttr $ a1 `SynInhAttr` indexedValue q (taggedStk $ taggedInh d2))) i
        b1 `InhSynAttr` IndexedValue q (SimSynAttr   a2)   -> inhAttrSide (composedSattOutAttr $ b1 `InhSynAttr` indexedValue q (taggedOut $ taggedSyn a2))
        b1 `InhSynAttr` IndexedValue q (SimStSynAttr d2 i) -> StackHeadSide $ retailN (stinhAttrSide (composedSattStkAttr $ b1 `InhSynAttr` indexedValue q (taggedStk $ taggedSyn d2))) i
    runReductionWithRep' (ATT.LabelSide l cs) = LabelSide l $ runReductionWithRep' <$> cs

    runReductionForR2 redf attrf = runReductionForR2' redf attrf 0 0

    runReductionForR2'
      :: (RankNumber -> TreeOutRightHandSide s2 i2 ss2 si2 tb)
      -> (RankNumber -> RankNumber -> AttrSide StkAttrTag s1 i1 ss1 si1 -> AttrSide StkAttrTag s2 i2 ss2 si2)
      -> RankNumber -> RankNumber
      -> TreeStkRightHandSide s1 i1 ss1 si1 ta
      -> TreeStkRightHandSide s2 i2 ss2 si2 tb
    runReductionForR2' redf attrf m l (StackConsSide _ t)
      = StackConsSide (redf m) $ runReductionForR2' redf attrf (m + 1) l t
    runReductionForR2' _ _ _ _ StackEmptySide
      = StackEmptySide
    runReductionForR2' redf attrf m l (StackTailSide t)
      = StackTailSide $ runReductionForR2' redf attrf m (l + 1) t
    runReductionForR2' _ attrf m l (AttrSide attr)
      = AttrSide $ attrf m l attr

    rule :: SattRuleType tag
      (ComposedIndexedSattAttr OutAttrTag SynAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
      (ComposedIndexedSattAttr OutAttrTag InhAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
      (ComposedIndexedSattAttr StkAttrTag SynAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
      (ComposedIndexedSattAttr StkAttrTag InhAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2)
      ti2 to1
    rule (SynAttr (ComposedSattOutAttr (a1 `SynSynAttr` IndexedValue q (TaggedOut (TaggedSyn a2))))) l
      = runReductionWithRep
        (taggedSynBox $ a1 `SynSynAttr` indexedValue q (simSynAttr a2)) l
    rule (SynAttr (ComposedSattOutAttr (b1 `InhInhAttr` IndexedValue q (TaggedOut (TaggedInh b2))))) l
      = runReductionWithRep
        (taggedSynBox $ b1 `InhInhAttr` indexedValue q (simInhAttr b2)) l
    rule (InhAttr (ComposedSattOutAttr (a1 `SynInhAttr` IndexedValue q (TaggedOut (TaggedInh b2)))) i) l
      = runReductionWithRep
        (taggedInhBox (a1 `SynInhAttr` indexedValue q (simInhAttr b2), i)) l
    rule (InhAttr (ComposedSattOutAttr (b1 `InhSynAttr` IndexedValue q (TaggedOut (TaggedSyn a2)))) i) l
      = runReductionWithRep
        (taggedInhBox (b1 `InhSynAttr` indexedValue q (simSynAttr a2), i)) l

    rule (StSynAttr (ComposedSattStkAttr (a1 `SynSynAttr` IndexedValue q (TaggedStk (TaggedSyn c2))))) l
      = runReductionForR2
        (\i -> runReductionWithRep
          (taggedSynBox $ a1 `SynSynAttr` indexedValue q (simStSynAttr c2 i)) l)
        (\_ _ (TaggedStk abox) -> taggedStk $ taggedEitherMap
          (\(c2', j') -> (composedSattStkAttr $ a1 `SynSynAttr` indexedValue
            (ATTC.AttrIndexedData (taggedSynBox $ taggedStkBox (c2, 0)) []: q) (taggedStk $ taggedSyn c2'), j'))
          (\d2' -> composedSattStkAttr $ a1 `SynInhAttr` indexedValue
            (ATTC.AttrIndexedData (taggedSynBox $ taggedStkBox (c2, 0)) []: q) (taggedStk $ taggedInh d2'))
          abox)
        $ reductionRule sfT2 (TaggedStk (TaggedSynBox c2)) l
    rule (StInhAttr (ComposedSattStkAttr (a1 `SynInhAttr` IndexedValue q (TaggedStk (TaggedInh d2)))) j) l
      = runReductionForR2
        (\i -> runReductionWithRep
          (taggedInhBox (a1 `SynInhAttr` indexedValue q (simStInhAttr d2 i), j)) l)
        (\_ _ (TaggedStk abox) -> taggedStk $ taggedEitherMap
          (\(c2', j') -> (composedSattStkAttr $ a1 `SynSynAttr` indexedValue
            (ATTC.AttrIndexedData (taggedInhBox (taggedStkBox (d2, 0), j)) []: q) (taggedStk $ taggedSyn c2'), j'))
          (\d2' -> composedSattStkAttr $ a1 `SynInhAttr` indexedValue
            (ATTC.AttrIndexedData (taggedInhBox (taggedStkBox (d2, 0), j)) []: q) (taggedStk $ taggedInh d2'))
          abox)
        $ reductionRule sfT2 (TaggedStk (TaggedInhBox (d2, j))) l

    rule (StInhAttr (ComposedSattStkAttr (b1 `InhSynAttr` IndexedValue (x:q) (TaggedStk (TaggedSyn c2)))) i) l
      = undefined b1 x q c2 i l
    rule (StSynAttr (ComposedSattStkAttr (b1 `InhInhAttr` IndexedValue (x:q) (TaggedStk (TaggedInh d2))))) l
      = undefined b1 x q d2 l

    rule _ _ = unreachable
