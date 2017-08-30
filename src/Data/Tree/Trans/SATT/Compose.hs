{-# LANGUAGE OverloadedLists #-}

module Data.Tree.Trans.SATT.Compose where

import           ClassyPrelude

import           Data.Tree.RankedTree
import qualified Data.Tree.Trans.ATT         as ATT
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


type ComposedSattSynAttr   syn1 inh1 syn2 inh2 stsyn2 stinh2
  = ComposedSattAttr OutAttrTag SynAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2
type ComposedSattInhAttr   syn1 inh1 syn2 inh2 stsyn2 stinh2
  = ComposedSattAttr OutAttrTag InhAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2
type ComposedSattStSynAttr syn1 inh1 syn2 inh2 stsyn2 stinh2
  = ComposedSattAttr StkAttrTag SynAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2
type ComposedSattStInhAttr syn1 inh1 syn2 inh2 stsyn2 stinh2
  = ComposedSattAttr StkAttrTag InhAttrTag syn1 inh1 syn2 inh2 stsyn2 stinh2

type ComposedSattAttrIndexedQueue syn2 inh2 stsyn2 stinh2
  = ATTC.AttrIndexedQueue (SimuratedAttAttr syn2 stsyn2) (SimuratedAttAttr inh2 stinh2)
type ComposedSattAttrIndexedValue syn2 inh2 stsyn2 stinh2
  = ATTC.IndexedValue :$ ComposedSattAttrIndexedQueue syn2 inh2 stsyn2 stinh2
type ComposedSattAttr tags taga syn1 inh1 syn2 inh2 stsyn2 stinh2 = ComposedSattAttrBase
  tags taga syn1 inh1
  (ComposedSattAttrIndexedValue syn2 inh2 stsyn2 stinh2 syn2)
  (ComposedSattAttrIndexedValue syn2 inh2 stsyn2 stinh2 inh2)
  (ComposedSattAttrIndexedValue syn2 inh2 stsyn2 stinh2 stsyn2)
  (ComposedSattAttrIndexedValue syn2 inh2 stsyn2 stinh2 stinh2)

newtype ComposedSattAttrBase tags taga syn1 inh1 syn2 inh2 stsyn2 stinh2
  = ComposedSattAttrBase {
    unComposedSattAttrBase :: SattAttrEither tags
      (ATTC.ComposedAttAttr taga syn1 inh1 syn2 inh2)
      (ATTC.ComposedAttAttr taga syn1 inh1 stsyn2 stinh2)
  } deriving (Eq, Ord)

composedSattOutAttr
  :: ATTC.ComposedAttAttr taga syn1 inh1 syn2 inh2
  -> ComposedSattAttrBase OutAttrTag taga syn1 inh1 syn2 inh2 stsyn2 stinh2
composedSattOutAttr = ComposedSattAttrBase . taggedOut

composedSattStkAttr
  :: ATTC.ComposedAttAttr taga syn1 inh1 stsyn2 stinh2
  -> ComposedSattAttrBase StkAttrTag taga syn1 inh1 syn2 inh2 stsyn2 stinh2
composedSattStkAttr = ComposedSattAttrBase . taggedStk

instance (Show syn1, Show inh1, Show syn2, Show inh2, Show stsyn2, Show stinh2)
  => Show (ComposedSattAttrBase tags taga syn1 inh1 syn2 inh2 stsyn2 stinh2) where
    show (ComposedSattAttrBase x) = case x of
      TaggedOut ox -> show ox
      TaggedStk sx -> show sx


type ComposedSatt syn1 inh1 syn2 inh2 stsyn2 stinh2 ta tb = StackAttrTreeTrans
  (ComposedSattSynAttr   syn1 inh1 syn2 inh2 stsyn2 stinh2)
  (ComposedSattInhAttr   syn1 inh1 syn2 inh2 stsyn2 stinh2)
  (ComposedSattStSynAttr syn1 inh1 syn2 inh2 stsyn2 stinh2)
  (ComposedSattStInhAttr syn1 inh1 syn2 inh2 stsyn2 stinh2)
  ta tb

{-
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
    $ initialAttrT1 `ATTC.SynSynAttr` ATTC.indexedValue [] (taggedSyn initialAttrT2)
    , reductionRule = rule
    }
  where
    initialAttrT1 = ATT.initialAttr trans1
    initialAttrT2 = initialAttr sfT2

    sfT2 = standardForm trans2
    simsfT2 = simurateSatt sfT2

    composedT1AndSimsfT2 :: ATT.AttrTreeTrans
      (ATTC.ComposedAttSynAttr syn1 inh1 (SimuratedAttAttr syn2 stsyn2) (SimuratedAttAttr inh2 stinh2))
      (ATTC.ComposedAttInhAttr syn1 inh1 (SimuratedAttAttr syn2 stsyn2) (SimuratedAttAttr inh2 stinh2))
      ti2 to1
    composedT1AndSimsfT2 = trans1 `ATTC.composeAtts` simsfT2

    retailN t 0 = t
    retailN t n = retailN (StackTailSide t) $ n - 1

    rule :: SattRuleType tag
      (ComposedSattSynAttr   syn1 inh1 syn2 inh2 stsyn2 stinh2)
      (ComposedSattInhAttr   syn1 inh1 syn2 inh2 stsyn2 stinh2)
      (ComposedSattStSynAttr syn1 inh1 syn2 inh2 stsyn2 stinh2)
      (ComposedSattStInhAttr syn1 inh1 syn2 inh2 stsyn2 stinh2)
      ta tb
    rule = undefined
    runReductionWithRep (ATT.LabelSide l cs) = LabelSide l $ runReductionWithRep <$> cs
    runReductionWithRep (ATT.SynAttrSide (a1 `ATTC.SynSynAttr` ATTC.IndexedValue (q, ATTC.SynAttrIdentity a2)) j) = case a2 of
      SimSynAttr   a2'   -> OutputSynAttrSide (a1 `SynSynAttr` ATTC.indexedValue q a2') j
      SimStSynAttr a2' i -> StackHeadSide $ retailN (StackSynAttrSide (a1 `SynStSynAttr` ATTC.indexedValue q a2') j) i
    runReductionWithRep (ATT.SynAttrSide (b1 `ATTC.InhInhAttr` ATTC.IndexedValue (q, ATTC.InhAttrIdentity b2)) j) = case b2 of
      SimInhAttr   b2'   -> OutputSynAttrSide (b1 `InhInhAttr` ATTC.indexedValue q b2') j
      SimStInhAttr b2' i -> StackHeadSide $ retailN (StackSynAttrSide (b1 `InhStInhAttr` ATTC.indexedValue q b2') j) i
    runReductionWithRep (ATT.InhAttrSide (a1 `ATTC.SynInhAttr` ATTC.IndexedValue (q, ATTC.InhAttrIdentity b2)))   = case b2 of
      SimInhAttr   b2'   -> OutputInhAttrSide (a1 `SynInhAttr` ATTC.indexedValue q b2')
      SimStInhAttr b2' i -> StackHeadSide $ retailN (StackInhAttrSide (a1 `SynStInhAttr` ATTC.indexedValue q b2')) i
    runReductionWithRep (ATT.InhAttrSide (b1 `ATTC.InhSynAttr` ATTC.IndexedValue (q, ATTC.SynAttrIdentity a2)))   = case a2 of
      SimSynAttr   a2'   -> OutputInhAttrSide (b1 `InhSynAttr` ATTC.indexedValue q a2')
      SimStSynAttr a2' i -> StackHeadSide $ retailN (StackInhAttrSide (b1 `InhStSynAttr` ATTC.indexedValue q a2')) i

    synRuleBased = ATT.synthesizedRule composedT1AndSimsfT2
    inhRuleBased = ATT.inheritedRule composedT1AndSimsfT2

    synRule (a1 `SynSynAttr` ATTC.IndexedValue (q, a2)) = runReductionWithRep
      . synRuleBased (a1 `ATTC.SynSynAttr` ATTC.indexedValue q (ATTC.SynAttrIdentity $ SimSynAttr a2))
    synRule (b1 `InhInhAttr` ATTC.IndexedValue (q, b2)) = runReductionWithRep
      . synRuleBased (b1 `ATTC.InhInhAttr` ATTC.indexedValue q (ATTC.InhAttrIdentity $ SimInhAttr b2))

    inhRule (a1 `SynInhAttr` ATTC.IndexedValue (q, b2)) j = runReductionWithRep
      . inhRuleBased (a1 `ATTC.SynInhAttr` ATTC.indexedValue q (ATTC.InhAttrIdentity $ SimInhAttr b2)) j
    inhRule (b1 `InhSynAttr` ATTC.IndexedValue (q, a2)) j = runReductionWithRep
      . inhRuleBased (b1 `ATTC.InhSynAttr` ATTC.indexedValue q (ATTC.SynAttrIdentity $ SimSynAttr a2)) j


    traverseReductionForStack f fc fd = traverseReductionForStack' f fc fd 0 0

    traverseReductionForStack'
      :: (RankNumber -> TreeOutputRightHandSide syn3 inh3 stsyn3 stinh3 tb)
      -> (stsyn2 -> RankNumber -> RankNumber -> stsyn3)
      -> (stinh2 -> RankNumber -> RankNumber -> stinh3)
      -> RankNumber -> RankNumber
      -> TreeStackRightHandSide syn2 inh2 stsyn2 stinh2 ta
      -> TreeStackRightHandSide syn3 inh3 stsyn3 stinh3 tb
    traverseReductionForStack' f fc fd k l (StackConsSide _ t)
      = StackConsSide (f k) $ traverseReductionForStack' f fc fd (k + 1) l t
    traverseReductionForStack' _ _  _  _ _ StackEmptySide
      = StackEmptySide
    traverseReductionForStack' f fc fd k l (StackTailSide t)
      = StackTailSide $ traverseReductionForStack' f fc fd k (l + 1) t
    traverseReductionForStack' _ fc _  k l (StackSynAttrSide c j)
      = StackSynAttrSide (fc c k l) j
    traverseReductionForStack' _ _ fd  k l (StackInhAttrSide d)
      = StackInhAttrSide (fd d k l)

    buildStackRHS = buildStackRHS' 0

    buildStackRHS' _ 0 0 _ a = a
    buildStackRHS' n 0 l f a = StackTailSide $ buildStackRHS' n 0 (l - 1) f a
    buildStackRHS' n k l f a = StackConsSide (f n) $ buildStackRHS' (n + 1) (k - 1) l f a

    stsynRuleT2 = stackSynthesizedRule sfT2
    stinhRuleT2 = stackInheritedRule sfT2

    stsynRule :: StackSynthesizedRuleType
      (ComposedSattSynAttr   syn1 inh1 syn2 inh2 stsyn2 stinh2)
      (ComposedSattInhAttr   syn1 inh1 syn2 inh2 stsyn2 stinh2)
      (ComposedSattStSynAttr syn1 inh1 syn2 inh2 stsyn2 stinh2)
      (ComposedSattStInhAttr syn1 inh1 syn2 inh2 stsyn2 stinh2)
      ti2 to1
    stsynRule (a1 `SynStSynAttr` ATTC.IndexedValue (q, c2)) lb = traverseReductionForStack
      (\i -> runReductionWithRep
        . synRuleBased (a1 `ATTC.SynSynAttr` ATTC.indexedValue q (ATTC.SynAttrIdentity $ SimStSynAttr c2 i)) $ lb)
      (\c k l -> a1 `SynStSynAttr` ATTC.indexedValue
        (ATTC.AttrIndexedSynData (ATTC.SynAttrIdentity $ SimStSynAttr c2 k) [l]:q) c)
      (\d k l -> a1 `SynStInhAttr` ATTC.indexedValue
        (ATTC.AttrIndexedSynData (ATTC.SynAttrIdentity $ SimStSynAttr c2 k) [l]:q) d)
      $ stsynRuleT2 c2 lb
    stsynRule (b1 `InhStInhAttr` ATTC.IndexedValue (x:q, c2)) lb = case x of
      ATTC.AttrIndexedSynData (ATTC.SynAttrIdentity (SimStSynAttr d2 k)) [l] -> buildStackRHS k l
        (\i -> runReductionWithRep
          . synRuleBased (b1 `ATTC.InhInhAttr` ATTC.indexedValue (ATTC.AttrIndexedSynData
            (ATTC.SynAttrIdentity (SimStSynAttr d2 (i - l + k)) ) [] : q)
            (ATTC.InhAttrIdentity $ SimStInhAttr c2 i)) $ lb)
        (StackInhAttrSide (b1 `InhStSynAttr` ATTC.indexedValue q d2))
      ATTC.AttrIndexedInhData (ATTC.InhAttrIdentity (SimStInhAttr d2 k)) j [l] -> buildStackRHS k l
        (\i -> runReductionWithRep
          . synRuleBased (b1 `ATTC.InhInhAttr` ATTC.indexedValue
            (ATTC.AttrIndexedInhData (ATTC.InhAttrIdentity (SimStInhAttr d2 (i - l + k))) j [] : q)
            (ATTC.InhAttrIdentity $ SimStInhAttr c2 i)) $ lb)
        (StackSynAttrSide (b1 `InhStInhAttr` ATTC.indexedValue q d2) j)
      _ -> error "stsynrule not operation"
    stsynRule _ _ = error "stsynrule not operation"

    stinhRule (a1 `SynStInhAttr` ATTC.IndexedValue (q, c2)) j lb = traverseReductionForStack
      (\i -> runReductionWithRep
        . inhRuleBased (a1 `ATTC.SynInhAttr` ATTC.indexedValue q (ATTC.InhAttrIdentity $ SimStInhAttr c2 i)) j $ lb)
      (\c k l -> a1 `SynStSynAttr` ATTC.indexedValue
        (ATTC.AttrIndexedInhData (ATTC.InhAttrIdentity $ SimStInhAttr c2 k) j [l]:q) c)
      (\d k l -> a1 `SynStInhAttr` ATTC.indexedValue
        (ATTC.AttrIndexedInhData (ATTC.InhAttrIdentity $ SimStInhAttr c2 k) j [l]:q) d)
      $ stinhRuleT2 c2 j lb
    stinhRule (b1 `InhStSynAttr` ATTC.IndexedValue (x:q, c2)) j' lb = case x of
      ATTC.AttrIndexedSynData (ATTC.SynAttrIdentity (SimStSynAttr d2 k)) [l] -> buildStackRHS k l
        (\i -> runReductionWithRep
          . inhRuleBased (b1 `ATTC.InhSynAttr` ATTC.indexedValue q (ATTC.SynAttrIdentity $ SimStSynAttr c2 i)) j' $ lb)
        (StackInhAttrSide (b1 `InhStSynAttr` ATTC.indexedValue q d2))
      ATTC.AttrIndexedInhData (ATTC.InhAttrIdentity (SimStInhAttr d2 k)) j [l] -> buildStackRHS k l
        (\i -> runReductionWithRep
          . inhRuleBased (b1 `ATTC.InhSynAttr` ATTC.indexedValue q (ATTC.SynAttrIdentity $ SimStSynAttr c2 i)) j' $ lb)
        (StackSynAttrSide (b1 `InhStInhAttr` ATTC.indexedValue q d2) j)
      _ -> error "stinhrule not operation"
    stinhRule _ _ _ = error "stinhrule not operation"
-}
