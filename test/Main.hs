{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE MagicHash #-}

module Main where

import Data.Elevator.Internal
import Test.Hspec
import Control.Exception (evaluate, SomeException (SomeException))
import GHC.Exts

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
