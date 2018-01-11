module Text.PrettyPrint.Classy
  ( module Text.PrettyPrint.ANSI.Leijen

    -- renames
  , emptyDoc
  , (<$^>)

    -- for show wrapper
  , ShowDoc (..)
  , prettyShowString

    -- combinators
  , record
  ) where

import Prelude
import Text.PrettyPrint.ANSI.Leijen hiding ((<$>), empty)
import qualified Text.PrettyPrint.ANSI.Leijen as PrettyPrint


emptyDoc :: Doc
emptyDoc = PrettyPrint.empty

(<$^>) :: Doc -> Doc -> Doc
(<$^>) = (PrettyPrint.<$>)


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
