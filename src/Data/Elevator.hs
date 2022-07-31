-- | Near zero-cost coercions between lifted and boxed unlifted types.
--
-- Turn any lifted type into an unlifted boxed type with 'Strict', eagerly
-- forcing any wrapped computation in the syntactic binding context.
--
-- Turn any unlifted boxed type into a lifted type with 'Lazy', suspending any
-- wrapped computation until the 'Lazy' is matched upon.
--
-- Re-use existing code by coercing functions that can be generalised according
-- to the levity polymorphism subkinding law @Unlifted <: Lifted@ with
-- 'levCoerce'.
--
module Data.Elevator
  ( UnliftedType, LiftedType
  , Strict(Strict), Lazy(Lazy)
  , LevitySubsumption(..), levCoerce
  ) where

import Data.Elevator.Internal
import GHC.Exts
