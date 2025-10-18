module Main (main) where

import           P
import           Test.Tasty       (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit (assertFailure, testCase, (@?=))

main :: IO ()
main = defaultMain $
    testGroup "unit tests"
        -- TODO: error line no.?
      ( tErr [] "test/data/pmfail.piz" "3:20: {a `just ⊕ `nil} ⊀ {ρ₁ `just}"
      : tErr ["."] "test/data/permeable.piz" "20:8: ‘{`nil}’ is not an acceptable argument, expected ‘{List(a) b `cons}’"
      : tErr [""] "test/data/badBool.piz" "5:12: failed to unify ‘{True}’ with ‘{True ⊕ False}’"
      : tErr [""] "test/data/badBool2.piz" "5:12: failed to unify ‘{False}’ with ‘{True ⊕ False}’"
      : [ tI fp | fp <- [ "lib/list.piz"
                        , "lib/either.piz"
                        , "lib/these.piz"
                        , "prelude/ord.piz"
                        , "prelude/bool.piz"
                        , "test/examples/mutual.piz"
                        , "test/examples/maybe.piz"
                        , "test/examples/ifte.piz"
                        , "test/examples/pat.piz"
                        , "test/data/beta.piz"
                        , "test/examples/exp.piz"
                        , "test/examples/pat2.piz"
                        ] ]
      ++ [ tNo fp | fp <- ["examples/vierergruppe.piz", "prelude/fn.piz" ] ])
    where tI = tFile ["."]; tNo = tFile []

tErr :: [FilePath] -> FilePath -> String -> TestTree
tErr incls fp expected = testCase fp $
    rRepl (tMs incls [fp]) >>= \case
        Right{} -> assertFailure "expected error."
        Left e  -> show e @?= expected

tFile :: [FilePath] -> FilePath -> TestTree
tFile incls fp = testCase fp $ do
    rRepl (tMs incls [fp]) >>= \case
        Right{} -> pure ()
        Left e  -> assertFailure (show e)
