{-# LANGUAGE CPP #-}
{-# LANGUAGE PackageImports #-}

module GHC.Types.Unique.Map.Extra where

#if __GLASGOW_HASKELL__ >= 902
import "ghc" GHC.Types.Unique.Map
#else
import GHC.Types.Unique.Map
#endif

#if __GLASGOW_HASKELL__ >= 900
import GHC.Types.Unique.FM (nonDetEltsUFM)
#elif __GLASGOW_HASKELL__ <= 810
import UniqFM (nonDetEltsUFM)
#endif

nonDetUniqMapToList :: UniqMap key a -> [(key, a)]
nonDetUniqMapToList (UniqMap u) = nonDetEltsUFM u
