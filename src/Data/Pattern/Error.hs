module Data.Pattern.Error where

import ClassyPrelude

unreachable :: a
unreachable = error "Pattern.unreachable"
