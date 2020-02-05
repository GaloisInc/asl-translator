{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE StandaloneDeriving #-}

module Language.ASL.Crucible.Exceptions ( CrucibleException(..) ) where

import qualified Control.Exception as X
import qualified Lang.Crucible.Types as CT
import qualified Data.Text as T

data CrucibleException =
    InvalidFunctionName T.Text
  | forall tp . ExpectedBaseTypeRepr (CT.TypeRepr tp)
  | BadUninterpretedFunctionCache T.Text

deriving instance Show CrucibleException


instance X.Exception CrucibleException
