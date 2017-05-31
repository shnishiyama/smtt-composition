module Data.SATT.ATT where

data AttrTreeTrans = AttrTreeTrans
  { inputs  :: [String]
  , inhAttr :: [String]
  , synAttr :: [String]
  } deriving (Eq, Show)
