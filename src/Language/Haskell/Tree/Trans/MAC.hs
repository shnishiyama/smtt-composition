{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Tree.Trans.MAC where

import           SmttPrelude

import qualified Data.HashMap.Strict        as HashMap
import qualified Data.Text                  as T
import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.MAC
import           Language.Haskell.Encoding

encodeHaskellFromMtt :: forall s ta la tb lb.
  ( MttConstraint s ta la tb lb
  , Show s, Show la, Show lb
  )
  => Text -> MacroTreeTransducer s ta la tb lb -> Text
encodeHaskellFromMtt name trans = intercalate "\n" $
    [ name <> " = initial" ]
    <> indentTexts
      ( [ "where" ]
      <> (intersperse "" . indentTexts)
        ( [ "initial u0 = " <> encodeHaskellFromRhs ie
          ]
        <> sort
          [  lookupStateIdent f
          <> " "
          <> "(" <> tshow l <> concat [ " u" <> tshow i | i <- [0..(treeLabelRank (Proxy @ta) l - 1)] ] <> ")"
          <> concat [ " " <> "y" <> tshow i | i <- [0..(labelRank f - 2)] ]
          <> " = "
          <> encodeHaskellFromRhs rhs
          | ((f, l), rhs) <- mapToList rules
          ]
        )
      )
  where
    stateMap = snd $ foldl'
      (\(i, m) f -> (i + 1, insertMap f (encodeToIdent i f) m))
      (0 :: Int, HashMap.empty) (mttStates trans)

    encodeToIdent i = T.pack . encodeToIdentifier (showHexWithMaxNumber (length $ mttStates trans) i) . show

    lookupStateIdent f = fromMaybe (error "illegal transducer") $ lookup f stateMap

    ie = mttInitialExpr trans
    rules = mttTransRules trans

    indentTexts = fmap ("  " <>)

    encodeHaskellFromRhs = encodeHaskellFromRhsBase False

    paren True  s = "(" <> s <> ")"
    paren False s = s

    encodeHaskellFromRhsBase b x = case x of
      MttContext i    -> "y" <> tshow i
      MttState f u cs -> paren b $
        lookupStateIdent f
        <> " "
        <> "u" <> tshow u
        <> concatMap (\c -> " " <> encodeHaskellFromRhsBase True c) cs
      MttLabelSide l cs  -> paren b $ tshow l <> concatMap (\c -> " " <> encodeHaskellFromRhsBase True c) cs
      MttBottomLabelSide -> "undefined"
