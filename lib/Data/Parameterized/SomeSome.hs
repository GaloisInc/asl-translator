{-# LANGUAGE GADTs #-}
{-# LANGUAGE PolyKinds #-}

module Data.Parameterized.SomeSome
  ( SomeSome(..)
  ) where

import Data.Kind ( Type )

-- | Like @Data.Parameterized.Some.Some@, but for doubly-parameterized types.
data SomeSome (f :: k1 -> k2 -> Type) = forall x y. SomeSome (f x y)
