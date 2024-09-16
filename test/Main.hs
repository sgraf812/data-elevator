{-# OPTIONS_GHC -fplugin=Test.Inspection.Plugin #-}

{-# LANGUAGE CPP              #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MagicHash        #-}
{-# LANGUAGE UnboxedTuples    #-}
{-# LANGUAGE TemplateHaskell  #-}

module Main where

import Data.Elevator.Internal
import Test.Hspec
import Test.Inspection
import Control.Exception (evaluate, SomeException (SomeException))
import GHC.Exts
import GHC.IO
import Data.IORef
import qualified Data.Primitive as P
import qualified Issue4

main :: IO ()
main = hspec $ do
  describe "Strict" $ do
    it "strict" $ do
      evaluate
        (let a = Strict (error "boom" :: Int)
             konst :: a -> Strict b -> a
             konst x y = x
        in konst 42 a)
        `shouldThrow` \(SomeException e) -> True

  describe "Lazy" $ do
    it "lazy" $ do
      (let a = Lazy (error "boom" :: Array# Int)
           konst :: a -> Lazy b -> a
           konst x y = x
       in konst 42 a)
      `shouldBe` 42

  describe "levCoerce" $ do
    describe "Refl" $ do
      it "Int ~ Int" $ do
        levCoerce @Int @Int 42 `shouldBe` (42 :: Int)
      it "Strict Int ~ Strict Int" $ do
        case levCoerce# @_ @_ @(Strict Int) @(Strict Int) (Strict 42) of Strict x -> x  `shouldBe` (42 :: Int)
    describe "->" $ do
      it "even" $ do
        levCoerce @(Int -> Bool) @(Strict Int -> Bool) even (Strict 42) `shouldBe` True
      it "co,contra: Int -> Strict Int ~ Int -> Strict Int" $ do
        levCoerce @(Int -> Strict Int) @(Strict Int -> Int) (\x -> Strict (x+1)) (Strict 42) `shouldBe` (43 :: Int)
      it "rank2 co: (Int -> Int) -> Int ~ (Strict Int -> Int) -> Int" $ do
        levCoerce @((Strict Int -> Int) -> Int) @((Int -> Strict Int) -> Int) (\f -> f (Strict 42)) (\x -> Strict x) `shouldBe` (42 :: Int)

-- 9.2 does not allow lev poly GHC.Array#
#if __GLASGOW_HASKELL__ >= 904
  describe "Issue 4" $ do
    it "should not crash" $ do
      let arr = P.createArray 5 (even (sum [0..1000]) :: Bool) (\_arr -> return ())
      let sarr = Issue4.primArrayToStrictArray arr
      Issue4.indexStrictArray sarr 3 `shouldBe` True
#endif

-- Before 9.6, the let/app invariant is still in effect and the rewrite rules
-- error
#if __GLASGOW_HASKELL__ >= 906
from_to_strict :: Bool -> Bool
from_to_strict x = fromStrict# (toStrict# x)

from_to_strict2 :: Bool -> Bool
from_to_strict2 x = case Strict x of Strict x -> x

to_from_lazy :: Lazy a -> Lazy a
to_from_lazy x = toLazy# (fromLazy# x)

to_from_lazy2 :: Lazy a -> Lazy a
to_from_lazy2 (Lazy x) = Lazy x

inspect $ 'from_to_strict `doesNotUse` 'toStrict#
inspect $ ('from_to_strict2 `doesNotUse` 'toStrict#) { expectFail = True } -- https://gitlab.haskell.org/ghc/ghc/-/issues/25261
inspect $ 'to_from_lazy `doesNotUse` 'fromLazy#
inspect $ ('to_from_lazy2 `doesNotUse` 'fromLazy#) { expectFail = True } -- https://gitlab.haskell.org/ghc/ghc/-/issues/25261
#endif
