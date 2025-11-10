module Main (main) where

import           P
import           Test.Tasty       (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit (assertFailure, testCase, (@?=))

main :: IO ()
main = defaultMain $
    testGroup "unit tests"
        -- TODO: error line no.?
      ( tENo "test/data/pmfail.piz" "3:12: {a `just ⊕ `nil} ⊀ {ρ₁ `just}"
      : tENo "test/data/badPerm.piz" "?"
      : tENo "test/examples/errorHierarchy.piz" "?"
      : tENo "test/data/badBool.piz" "3:12: failed to unify ‘{True}’ with ‘{True ⊕ False}’"
      : tENo "test/data/badBool2.piz" "3:12: failed to unify ‘{False}’ with ‘{True ⊕ False}’"
      : tE "test/data/permeable.piz" "21:8: ‘{`nil ⊕\n       List( a ) Unit `cons}’ is not an acceptable argument, expected ‘{List( a ) b `cons}’"
      : tE "test/data/badList.piz" "4:14: {List(a) b `cons ⊕ `nil} ⊀ {ρ₁ ρ₂ `cons}"
      : [ tI fp | fp <- [ "lib/list.piz"
                        , "lib/either.piz"
                        , "lib/both.piz"
                        , "prelude/ord.piz"
                        , "test/examples/maybe.piz"
                        , "test/examples/ifte.piz"
                        , "test/examples/pat.piz"
                        , "lib/numbertheory.piz"
                        , "test/data/beta.piz"
                        , "test/data/these.piz"
                        , "test/data/rec.piz"
                        , "test/examples/pat2.piz"
                        ] ]
      ++ [ tNo fp | fp <- [ "examples/vierergruppe.piz"
                          , "prelude/bool.piz"
                          , "test/examples/klein.piz"
                          , "test/examples/mutual.piz"
                          , "test/data/perm.piz"
                          , "test/examples/exp.piz"
                          , "prelude/fn.piz"
                          , "test/examples/ros.piz"
                          ] ])
    where tI = tFile ["."]; tNo = tFile []
          tE = tErr ["."]; tENo = tErr []

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
