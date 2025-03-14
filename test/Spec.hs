{-# LANGUAGE OverloadedStrings #-}

module Main (main) where

import           P
import           Test.Tasty       (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit (assertFailure, testCase, (@?=))

main :: IO ()
main = defaultMain $
    testGroup "unit tests"
      ( tErr ["."] "test/data/pmfail.piz" "8:17: ⦠ Failed to match ‘{ρ₁ `just}’ against ‘{a `just ⊕ `nil}’"
      : [ tI fp | fp <- [ "lib/list.piz"
                        , "prelude/ord.piz"
                        , "test/examples/bool.piz"
                        , "test/examples/mutual.piz"
                        , "test/examples/maybe.piz"
                        , "test/data/beta.piz"
                        , "test/examples/ifte.piz"
                        , "test/examples/pat.piz"
                        ] ]
      ++ [ tNo fp | fp <- ["examples/vierergruppe.piz", "prelude/fn.piz" ] ])
    where tI = tFile ["."]; tNo = tFile []

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
