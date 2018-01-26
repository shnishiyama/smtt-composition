module Text.PrettyPrint.Classy
  ( module Text.PrettyPrint.ANSI.Leijen

    -- renames
  , emptyDoc
  , (<$^>)

    -- for show wrapper
  , ShowDoc (..)
  , prettyShowString
  , prettyShowsPrec

    -- combinators
  , record

    -- utilities
  , putDocLn
  , hPutDocLn
  ) where

import           Prelude
import           System.IO
import           Text.PrettyPrint.ANSI.Leijen hiding (empty, (<$>))
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

prettyShowsPrec :: Show a => Int -> a -> Doc
prettyShowsPrec d x = pretty $ showsPrec d x ""


record :: String -> [(String, Doc)] -> Doc
record name fields = text name
    <+> fieldDoc [text fieldName <+> text "=" <+> fieldBody | (fieldName, fieldBody) <- fields ]
  where
    fieldDoc = encloseSep lbrace rbrace comma


putDocLn :: Doc -> IO ()
putDocLn d = do
  putDoc d
  putStrLn ""

hPutDocLn :: Handle -> Doc -> IO ()
hPutDocLn h d = do
  hPutDoc h d
  hPutStrLn h ""
