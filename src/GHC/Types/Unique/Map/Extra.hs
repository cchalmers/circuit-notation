{-# LANGUAGE PackageImports #-}

module GHC.Types.Unique.Map.Extra where

import "ghc" GHC.Types.Unique.Map
import GHC.Types.Unique.FM (nonDetEltsUFM)

nonDetUniqMapToList :: UniqMap key a -> [(key, a)]
nonDetUniqMapToList (UniqMap u) = nonDetEltsUFM u
