{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           P
import           Test.Tasty       (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit (Assertion, assertFailure, testCase, (@?=))

main :: IO ()
main = defaultMain $
    testGroup "unit tests"
      [ tFile ["."] "lib/list.piz"
      , tFile ["."] "prelude/ord.piz"
      , tFile ["."] "test/examples/bool.piz"
      , rFile ["."] "test/examples/mutual.piz"
      , tFile ["."] "test/examples/maybe.piz"
      , tFile ["."] "test/data/beta.piz"
      , tFile [] "examples/vierergruppe.piz"
      , tFile [] "prelude/fn.piz"
      , tFile ["."] "test/examples/ifte.piz"
      , tErr ["."] "test/data/pmfail.piz" "8:17: ⦠ Failed to match ‘{a `just}’ against ‘{a `just ⊕ `nil}’"
      ]

rFile :: [FilePath] -> FilePath -> TestTree
rFile incls fp = testCase fp $ rr incls fp

tErr :: [FilePath] -> FilePath -> String -> TestTree
tErr incls fp expected = testCase fp $ do
    res <- tMs incls fp
    case res of
        Right{} -> assertFailure "expected error."
        Left e  -> show e @?= expected

tFile :: [FilePath] -> FilePath -> TestTree
tFile incls fp = testCase fp $ do
    res <- tMs incls fp
    case res of
        Right{} -> pure ()
        Left e  -> assertFailure (show e)

rr :: [FilePath] -> FilePath -> Assertion
rr incls fp = do
    res <- rMs incls fp
    case res of
        Right{} -> pure ()
        Left e  -> assertFailure (show e)
