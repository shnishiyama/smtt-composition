module Data.Tree.Trans.Compose.TdttAndSmtt where

import SattPrelude

import qualified Data.Tree.Trans.SMAC as SMAC
import qualified Data.Tree.Trans.TOP as TOP
import qualified Data.Tree.Trans.MAC as MAC
import qualified Data.Vector as V


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
  ( Eq s1,
  , to1 ~ ti2
  , MAC.MttConstraint s2 ti2 li2 to2 lo2
  )
  => HashSet (s1, RankNumber)
  -> SMAC.StackMacroTreeTransducer s2 ti2 li2 to2 lo2
  -> ComposeBasedMtt s1 s2 to1 lo1 ti2 li2 to2 lo2
toComposeBasedMtt fus trans = fromMaybe errorUnreachable $ MAC.buildMtt
    initialExpr
    $ rules1 <> rules0
  where
    states = smttStates trans

    initialExpr = undefined

    rules0 = undefined

    convRhs = undefined

    rules1 = do
      (f, u) <- setFromList fus
      g      <- setFromList states
      let r = labelRank g
      pure
        ( g
        , TOP.tdttStateF f u
        , MAC.MttLabelSide
          (SMAC.SmttStateF (ComposedSmttState f g) u $ replicate r ())
          $ V.generate r id
        )



type ComposedSmtt s1 s2 ti to = SMAC.SmttTransducer
  (ComposedSmttState s1 s2)
  ti to

composeTdttAndSmtt :: forall m s1 s2 ti1 li1 to1 lo1 ti2 li2 to2 lo2.
  ( TOP.TdttConstraint s1 ti1 li1 to1 lo1
  , to1 ~ ti2
  , SMAC.SmttConstraint s2 ti2 li2 to2 lo2
  , MonadThrow m
  )
  => TOP.TopDownTreeTransducer s1 ti1 li1 to1 lo1
  -> SMAC.StackMacroTreeTransducer s2 ti2 li2 to2 lo2
  -> ComposedSmtt s1 s2 ti1 to2
composeTdttAndSmtt trans1 trans2 = fromMaybe errorUnreachable
    $ buildSmtt ie rules
  where
    ie = undefined

    rules = undefined

