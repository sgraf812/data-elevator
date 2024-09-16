{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE PolyKinds             #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE RoleAnnotations       #-}
{-# LANGUAGE MagicHash             #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE ViewPatterns          #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE UnliftedNewtypes      #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE ScopedTypeVariables   #-}

-- | This module doesn't respect the PVP!
-- Breaking changes may happen at any minor version (^>= *.*.m.*)

module Data.Elevator.Internal where

import GHC.Exts
import Data.Kind
import Unsafe.Coerce

-- | The kind of boxed, lifted types, for example @[Int]@ or any other
-- user-defined data type.
type LiftedType = Type

type U = UnliftedType
type L = LiftedType

type role Strict representational

-- | Turn a lifted data type into an unlifted one.
-- Unlifted data types enjoy a call-by-value calling convention. E.g.,
--
-- > let f :: (a :: UnliftedType) -> Int
-- >     f _ = 42
-- > in f (Strict (error "boom" :: Int))
--
-- Will error out with @"boom"@.
--
-- Note however that most function definitions don't take argument types of kind
-- 'UnliftedType'. Use 'levCoerce' to work around that.
newtype Strict (a :: LiftedType) where
  Strict_ :: Any @UnliftedType -> Strict a

toStrict# :: a -> Strict a
toStrict# = unsafeCoerce id
{-# NOINLINE toStrict# #-} -- See Note [NOINLINE toStrict#/fromLazy#]
{-# RULES "fromStrict#.toStrict#" forall x. fromStrict# (toStrict# x) = x #-}
{-# RULES "toLazy#.toStrict#" forall x. toLazy# (toStrict# x) = unsafeCoerce id x #-}

fromStrict# :: Strict a -> a
fromStrict# = unsafeCoerce id
{-# INLINE[0] fromStrict# #-} -- See Note [NOINLINE toStrict#/fromLazy#]

pattern Strict :: a -> Strict a
pattern Strict x <- (fromStrict# -> x) where
  Strict x = toStrict# x
{-# INLINE Strict #-}
{-# COMPLETE Strict #-}


type role Lazy representational

-- | Turn an unlifted boxed type into a lifted one.
-- @Lazy a@ then enjoys a call-by-name calling convention. E.g.,
--
-- > let f :: a -> Int
-- >     f _ = 42
-- > in f (Lazy (error "boom" :: Array# Int))
--
-- Will evaluate to @42@ and not error.
newtype Lazy (a :: UnliftedType) where
  Lazy_ :: Any @LiftedType -> Lazy a

toLazy# :: a -> Lazy a
toLazy# = unsafeCoerce id
{-# INLINE[0] toLazy# #-} -- See Note [NOINLINE toStrict#/fromLazy#]

fromLazy# :: Lazy a -> a
fromLazy# = unsafeCoerce id
{-# NOINLINE fromLazy# #-} -- See Note [NOINLINE toStrict#/fromLazy#]
{-# RULES "toLazy#.fromLazy#" forall x. toLazy# (fromLazy# x) = x #-}
{-# RULES "fromStrict#.fromLazy#" forall x. fromStrict# (fromLazy# x) = unsafeCoerce id x #-}

pattern Lazy :: a -> Lazy a
pattern Lazy x <- (fromLazy# -> x) where
  Lazy x = toLazy# x
{-# INLINE Lazy #-}
{-# COMPLETE Lazy #-}


-- | Re-use existing code taking arguments lazily to take arguments 'Strict'ly
-- by coercing with 'levCoerce'.Example: 'even' can be
-- re-used on @Strict Int@:
--
-- >>> levCoerce @(Int -> Bool) @(Strict Int -> Bool) even (Strict 42)
-- True
--
-- More generally, any type of kind 'UnliftedType' can act as a (\"is-a\") type
-- of kind 'LiftedType'. This levity polymorphism subkinding axiom
-- @Unlifted <: Lifted@ is encoded in 'LevitySubsumption' and is lifted to
-- useful instances for 'Strict', 'Lazy' and '(->)'. Example with covariance in
-- the result type:
--
-- >>> levCoerce @(Int -> Strict Bool) @(Strict Int -> Bool) (\x -> Strict (even x)) (Strict 42)
-- True
--
-- A function from @Int@ to @Strict Bool@ can be called on a @Strict Int@ (e.g.,
-- the precondition strengthened) and the result can be coerced to @Bool@ (e.g.,
-- the postcondition weakened).
--
-- You can also keep on coercing in negative position of the function arrow,
-- with the variance following polarity:
--
-- > levCoerce @((Strict Int -> Int) -> Int)
-- >           @((Int -> Strict Int) -> Int)
-- >           (\f -> f (Strict 42))
-- >           (\x -> Strict x)
--
levCoerce :: LevitySubsumption a b => a -> b
levCoerce = levCoerce#

-- | Similar to 'Coercible', this type class models a subkinding relationship
-- between two types. The instances lift the @Unlifted <: Lifted@ sub-kinding
-- relationship to 'TYPE', 'Strict', 'Lazy' and then over function types.
--
-- Like for 'Coercible', the instances of this type class should ultimately be
-- compiler-generated.
class LevitySubsumption (a :: TYPE (BoxedRep l)) (b :: TYPE (BoxedRep r)) where
  levCoerce# :: a -> b

instance {-# OVERLAPPABLE #-} LevitySubsumption (a::LiftedType) a where
  levCoerce# x = x

instance {-# OVERLAPPABLE #-} LevitySubsumption (a::UnliftedType) a where
  levCoerce# x = x

instance {-# OVERLAPPING #-} LevitySubsumption (Strict a) a where
  levCoerce# (Strict a) = a

instance {-# OVERLAPPING #-} LevitySubsumption a (Lazy a) where
  levCoerce# a = Lazy a

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::L) -> (b1::L)) ((a2::L) -> (b2::L)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::L) -> (b1::L)) ((a2::L) -> (b2::U)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::L) -> (b1::L)) ((a2::U) -> (b2::L)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::L) -> (b1::L)) ((a2::U) -> (b2::U)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::L) -> (b1::U)) ((a2::L) -> (b2::L)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::L) -> (b1::U)) ((a2::L) -> (b2::U)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::L) -> (b1::U)) ((a2::U) -> (b2::L)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::L) -> (b1::U)) ((a2::U) -> (b2::U)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::U) -> (b1::L)) ((a2::L) -> (b2::L)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::U) -> (b1::L)) ((a2::L) -> (b2::U)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::U) -> (b1::L)) ((a2::U) -> (b2::L)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::U) -> (b1::L)) ((a2::U) -> (b2::U)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::U) -> (b1::U)) ((a2::L) -> (b2::L)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::U) -> (b1::U)) ((a2::L) -> (b2::U)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::U) -> (b1::U)) ((a2::U) -> (b2::L)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

instance {-# OVERLAPPING #-} (LevitySubsumption a2 a1, LevitySubsumption b1 b2) => LevitySubsumption ((a1::U) -> (b1::U)) ((a2::U) -> (b2::U)) where
  -- Specification:
  -- > levCoerce# f x = levCoerce# (f (levCoerce# x :: a1))
  levCoerce# f x = unsafeCoerce# f x

{- Note [NOINLINE toStrict#/fromLazy#]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
It is important GHC does not regard the expression `Strict x` as trivial.
This is because CorePrep will not case-bind `Strict x` in `f (Strict x)` when it
is trivial, in which case we do not get proper call-by-value for the call to `f`.

However, if we inline the Strict and the toStrict#, what we get is
`f (x |> co)`, and `x |> co` is trivial.
So, sadly we need to mark `toStrict#` as NOINLINE; in which case we get
`f (toStrict# x)`, where `toStrict# x` is non-trivial and thus properly
case-bound by CorePrep: `case toStrict# x of x' { __DEFAULT -> f x' }`.

But this means that expressions such as `toLazy# (toStrict# x)` are no longer
optimised to `x`. We fix that by introducing the rewrite rules

  forall x. fromStrict# (toStrict# x) = x
  forall x. toLazy# (toStrict# x) = unsafeCoerce id x -- will desugar to x |> co

Thus we keep the zero-cost promise.

This applies to `fromLazy#` as well. Note the following desugaring

  case x of Lazy y -> f y
  ==> {INLINE, including `fromLazy#`, CorePrep}
  f (x |> co)

Note the absence of a seq on `x`. If we do not inline `fromLazy#`, we get

  f (fromLazy# x)
  ==> {CorePrep}
  case fromLazy# x of y { __DEFAULT -> f y }

Much better. We need similar rewrite rules, however.
-}
