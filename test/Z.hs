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
          [ eEx "test/data/list.piz" "six" "6"
          , eEx "lib/maybe.piz" "`nothing join" "`nothing"
          , eEx "examples/vierergruppe.piz" "`b `c mult" "`a"
          , eEx "prelude/bool.piz" "True False or" "True"
          , eEx "test/examples/mutual.piz" "5 even" "False"
          , eEx "lib/numbertheory.piz" "15 10 gcd" "5"
          , eEx "prelude/ord.piz" "3 2 cmpInt 2 2 cmpInt" "`gt `eq"
          , eEx "test/examples/ros.piz" "`g complement `t complement" "`c `a"
          , eEx "test/examples/parity.piz" "`even `even add `odd `odd add" "`even `even"
          , eEx "test/examples/dep.piz" "x ors" "True"
          ]
        , testGroup "ty"
            ( tE "test/data/pmfail.piz" "test/data/pmfail.piz:3:12: {a `just ⊕ `nil} ⊀ {a `just}"
            : tE "test/data/badPerm.piz" "?"
            : tE "test/data/univL.piz" "test/data/univL.piz:1:5: could not match ‘Int’ against ‘a’"
            : tE "test/data/univR.piz" "test/data/univR.piz:1:8: could not match ‘Int’ against ‘a’"
            : tE "test/examples/errorHierarchy.piz" "?"
            : tE "test/data/badBool.piz" "test/data/badBool.piz:3:12: failed to unify ‘{True}’ with ‘{True ⊕ False}’"
            : tE "test/data/badBool2.piz" "test/data/badBool2.piz:3:12: failed to unify ‘{False}’ with ‘{True ⊕ False}’"
            : tE "test/data/permeable.piz" "test/data/permeable.piz:21:8: ‘{`nil ⊕\n                               List( Unit ) Unit `cons}’ is not an acceptable argument, expected ‘{List( a ) a `cons}’"
            : tE "test/data/badList.piz" "test/data/badList.piz:4:14: {List(a) a `cons ⊕ `nil} ⊀ {List(a) a `cons}"
            : tE "test/data/both.piz" "test/data/both.piz:12:5: {{True ⊕ False} `left ⊕ Int `right ⊕ {True ⊕\n                                                              False} Int `both} ⊀ {{True ⊕\n                                                                                   False} `left ⊕\n                                                                                  Int `right}"
            : map tF [ "lib/list.piz"
                     , "lib/either.piz"
                     , "lib/both.piz"
                     , "examples/ast.piz"
                     , "test/examples/maybe.piz"
                     , "test/examples/ifte.piz"
                     , "test/examples/pat.piz"
                     , "test/data/beta.piz"
                     , "test/data/rec.piz"
                     , "test/examples/pat2.piz"
                     , "test/examples/klein.piz"
                     , "test/data/perm.piz"
                     , "test/examples/exp.piz"
                     , "prelude/fn.piz"
                     ]
            )
        ]

eEx :: FilePath -> BSL.ByteString -> String -> TestTree
eEx fp src expected = testCase (ASCIIL.unpack src ++ " (" ++ fp ++ ")") $
    e1 ["."] [fp] src >>= \case
        Left e -> assertFailure (show e)
        Right e -> unwords (map show (reverse e)) @?= expected

tE :: FilePath -> String -> TestTree
tE fp expected = testCase fp $
    rRepl (tMs ["."] [fp]) >>= \case
        Right{} -> assertFailure "expected error."
        Left e  -> show e @?= expected

tF :: FilePath -> TestTree
tF fp = testCase fp $ do
    rRepl (tMs ["."] [fp]) >>= \case
        Right{} -> pure ()
        Left e  -> assertFailure (show e)
