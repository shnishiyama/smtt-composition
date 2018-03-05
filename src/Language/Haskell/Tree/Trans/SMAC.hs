{-# LANGUAGE OverloadedStrings #-}

module Language.Haskell.Tree.Trans.SMAC where

import           SattPrelude

import qualified Data.HashMap.Strict        as HashMap
import qualified Data.Text                  as T
import           Data.Tree.RankedTree.Label
import           Data.Tree.Trans.SMAC
import           Language.Haskell.Encoding

encodeHaskellFromSmtt :: forall s ta la tb lb.
  ( SmttConstraint s ta la tb lb
  , Show s, Show la, Show lb
  )
  => Text -> StackMacroTreeTransducer s ta la tb lb -> Text
encodeHaskellFromSmtt name trans = intercalate "\n" $
    [ name <> " = stackHead . initial" ]
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
      (0 :: Int, HashMap.empty) (smttStates trans)

    encodeToIdent i = T.pack . encodeToIdentifier (showHexWithMaxNumber (length $ smttStates trans) i) . show

    lookupStateIdent f = fromMaybe (error "illegal transducer") $ lookup f stateMap

    ie = smttInitialExpr trans
    rules = smttTransRules trans

    indentTexts = fmap ("  " <>)

    encodeHaskellFromRhs = encodeHaskellFromRhsStk False

    paren True  s = "(" <> s <> ")"
    paren False s = s

    encodeHaskellFromRhsStk b x = case x of
      SmttContext i    -> "y" <> tshow i
      SmttState f u cs -> paren b $
        lookupStateIdent f
        <> " "
        <> "u" <> tshow u
        <> concatMap (\c -> " " <> encodeHaskellFromRhsStk True c) cs
      SmttStackEmpty -> "stackEmpty"
      SmttStackTail s -> paren b $ "stackTail " <> encodeHaskellFromRhsStk True s
      SmttStackCons v s -> paren b $ "stackCons " <> encodeHaskellFromRhsVal True v <> " " <> encodeHaskellFromRhsStk True s

    encodeHaskellFromRhsVal b x = case x of
      SmttLabelSide l cs -> paren b $ tshow l <> concatMap (\c -> " " <> encodeHaskellFromRhsVal True c) cs
      SmttStackBottom -> "stackBottom"
      SmttStackHead s -> paren b $ "stackHead " <> encodeHaskellFromRhsStk True s
