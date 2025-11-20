module Main (main) where

import qualified Data.ByteString.Lazy       as BSL
import qualified Data.ByteString.Lazy.Char8 as ASCIIL
import           P
import           Test.Tasty                 (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit           (assertFailure, testCase, (@?=))

main :: IO ()
main = defaultMain $
    testGroup "unit"
        [ testGroup "e"
          [ eEx ["."] "test/data/list.piz" "six" "6"
          , eEx ["."] "lib/maybe.piz" "`nothing join" "`nothing"
          , eEx [] "examples/vierergruppe.piz" "`b `c mult" "`a"
          , eEx [] "prelude/bool.piz" "True False or" "True"
          , eEx [] "test/examples/mutual.piz" "5 even" "False"
          , eEx ["."] "lib/numbertheory.piz" "15 10 gcd" "5"
          ]
        , testGroup "ty"
              -- TODO: error line no.?
            ( tENo "test/data/pmfail.piz" "3:12: {a `just ⊕ `nil} ⊀ {a `just}"
            : tENo "test/data/badPerm.piz" "?"
            : tENo "test/data/univL.piz" "1:5: could not match ‘Int’ against ‘a’"
            : tENo "test/data/univR.piz" "1:8: could not match ‘Int’ against ‘a’"
            : tENo "test/examples/errorHierarchy.piz" "?"
            : tENo "test/data/badBool.piz" "3:12: failed to unify ‘{True}’ with ‘{True ⊕ False}’"
            : tENo "test/data/badBool2.piz" "3:12: failed to unify ‘{False}’ with ‘{True ⊕ False}’"
            : tE "test/data/permeable.piz" "21:8: ‘{`nil ⊕\n       List( Unit ) Unit `cons}’ is not an acceptable argument, expected ‘{List( a ) a `cons}’"
            : tE "test/data/badList.piz" "4:14: {List(a) a `cons ⊕ `nil} ⊀ {ρ₁ a `cons}"
            : tE "test/data/both.piz" "12:5: {{True ⊕ False} `left ⊕ Int `right ⊕ {True ⊕ False} Int `both} ⊀ {{True ⊕\n                                                                        False} `left ⊕\n                                                                       Int `right}"
            : [ tI fp | fp <- [ "lib/list.piz"
                              , "lib/either.piz"
                              , "lib/both.piz"
                              , "prelude/ord.piz"
                              , "test/examples/maybe.piz"
                              , "test/examples/ifte.piz"
                              , "test/examples/pat.piz"
                              , "test/data/beta.piz"
                              , "test/data/rec.piz"
                              , "test/examples/pat2.piz"
                              ] ]
            ++ [ tNo fp | fp <- [ "test/examples/klein.piz"
                                , "test/data/perm.piz"
                                , "test/examples/exp.piz"
                                , "prelude/fn.piz"
                                , "test/examples/ros.piz"
                                ] ])
        ]
    where tI = tFile ["."]; tNo = tFile []
          tE = tErr ["."]; tENo = tErr []

eEx :: [FilePath] -> FilePath -> BSL.ByteString -> String -> TestTree
eEx incls fp src expected = testCase (ASCIIL.unpack src ++ " (" ++ fp ++ ")") $
    e1 incls [fp] src >>= \case
        Left e -> assertFailure (show e)
        Right [e] -> show e @?= expected

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
