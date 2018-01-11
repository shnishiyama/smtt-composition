module Text.PrettyPrint.Classy
  ( module Text.PrettyPrint.ANSI.Leijen

    -- for show wrapper
  , ShowDoc (..)
  , prettyShowString

    -- combinators
  , record
  ) where

import Prelude hiding ((<$>))
import Text.PrettyPrint.ANSI.Leijen


newtype ShowDoc a = ShowDoc a

instance Show a => Pretty (ShowDoc a) where
  pretty (ShowDoc x) = pretty $ show x

prettyShowString :: Show a => a -> Doc
prettyShowString x = pretty (ShowDoc x)


record :: String -> [(String, Doc)] -> Doc
record name fields = text name
    <+> fieldDoc [text fieldName <+> text "=" <+> fieldBody | (fieldName, fieldBody) <- fields ]
  where
    fieldDoc = encloseSep lbrace rbrace comma
