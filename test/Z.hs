module Main (main) where

import qualified Data.ByteString.Lazy       as BSL
import qualified Data.ByteString.Lazy.Char8 as ASCIIL
import           P
import           Test.Tasty                 (TestTree, defaultMain, testGroup)
import           Test.Tasty.HUnit           (assertFailure, testCase, (@?=))

main :: IO ()
main = defaultMain $
    testGroup "u"
        [ testGroup "e"
          [ eEx ["test/data/list.piz"] "n sum" "6"
          , eEx ["lib/list.piz", "test/data/list.piz"] "n m concat" "{{{{{{`nil 1 `cons} 2 `cons} 3 `cons} 3 `cons} 4 `cons} 5 `cons}"
          , eEx ["lib/maybe.piz"] "`nothing join" "`nothing"
          , eEx ["examples/vierergruppe.piz"] "`b `c mult" "`a"
          , eEx ["prelude/bool.piz"] "True False or" "True"
          , eEx ["test/examples/mutual.piz"] "5 even" "False"
          , eEx ["lib/numbertheory.piz"] "15 10 gcd" "5"
          , eEx ["prelude/ord.piz"] "3 2 cmpInt 2 2 cmpInt" "`gt `eq"
          , eEx ["test/examples/ros.piz"] "`g complement `t complement" "`c `a"
          , eEx ["examples/parity.piz"] "`even `even add `odd `odd add" "`even `even"
          , eEx ["test/examples/dep.piz"] "x ors" "True"
          , eEx ["examples/fact.piz"] "7 fac" "5040"
          , eEx ["examples/peano.piz"] "`Z `S `S `Z `S `S `S mul toInt" "6"
          , eEx ["test/examples/cont.piz"] "7 fac" "5040"
          , eEx ["examples/ast.piz"] "0 \"b\" `name `var 0 \"a\" `name `var `ap 0 \"a\" `name `lam printAST" "\"λa.(b)a\""
          -- TODO: eEx multi-repl
          , eEx ["examples/systemT.piz"] "`N `N `A `N `A printTy" "\"(ℕ → ℕ) → ℕ\""
          , eEx ["examples/systemT.piz"] "`N `N `N `A `A printTy" "\"ℕ → ℕ → ℕ\""
          , eEx ["examples/systemT.piz"] "\"y\" `var \"x\" `var `S `ap \"x\" `lam printTerm" "\"λx.y(S x)\""
          , eEx ["test/examples/set.piz", "examples/set.piz"]
              "x 3 x member 6 x member 7 x member"
              "{`nil 1 {`nil 2 {{{`nil 3 `nil `branch} 5 `nil `branch} 6 {`nil 10 `nil `branch} `branch} `branch} `branch} True True False"
          ]
        , testGroup "ty"
            ( tE "test/data/pmfail.piz" "test/data/pmfail.piz:3:12: {a `just ⊕ `nil} ⊀ {a `just}"
            : tE "test/data/badPerm.piz" "?"
            : tE "test/data/univL.piz" "test/data/univL.piz:1:5: could not match ‘Int’ against ‘a’"
            : tE "test/data/univR.piz" "test/data/univR.piz:1:8: could not match ‘Int’ against ‘a’"
            : tE "test/examples/errorHierarchy.piz" "test/examples/errorHierarchy.piz:13:19: {`scope ⊕ `unificationFailed} ⊀\n(ρ₁ ⊃ {`scope})"
            : tE "test/data/badBool.piz" "test/data/badBool.piz:2:10: ‘{True}’, ‘{True ⊕ False}’ are disjoint"
            : tE "test/data/badBool2.piz" "test/data/badBool2.piz:2:10: ‘{True ⊕ False}’, ‘{True}’ are disjoint"
            : tE "test/data/permeable.piz" "test/data/permeable.piz:21:8: ‘{ `nil ⊕ List(Unit) Unit `cons\n                               }’ is not an acceptable argument, expected\n‘{List(a) a `cons}’"
            : tE "test/data/badList.piz" "test/data/badList.piz:4:14: {List(a) a `cons ⊕ `nil} ⊀ {List(a) a `cons}"
            : tE "test/data/both.piz" "test/data/both.piz:12:5: { {True ⊕ False} `left ⊕ Int `right ⊕ { True ⊕ False\n                                                               } Int `both\n                         } ⊀ {{True ⊕ False} `left ⊕ Int `right}"
            : map tF [ "lib/list.piz"
                     , "lib/either.piz"
                     , "lib/both.piz"
                     , "lib/tree.piz"
                     , "examples/ast.piz"
                     , "test/examples/maybe.piz"
                     , "test/examples/ifte.piz"
                     , "test/examples/pat.piz"
                     , "test/data/beta.piz"
                     , "test/data/rec.piz"
                     , "test/data/fingertree.piz"
                     , "test/examples/pat2.piz"
                     , "test/examples/klein.piz"
                     , "test/data/perm.piz"
                     , "test/examples/exp.piz"
                     , "prelude/fn.piz"
                     ]
            )
        ]

eEx :: [FilePath] -> BSL.ByteString -> String -> TestTree
eEx fp src expected = testCase (ASCIIL.unpack src ++ " (" ++ head fp ++ ")") $
    e1 ["."] fp src >>= \case
        Left e -> assertFailure (show e)
        Right e -> unwords (map show (reverse e)) @?= expected

wf fp z = testCase fp $ rRepl (tMs ["."] [fp]) >>= z

tE :: FilePath -> String -> TestTree
tE fp expected = wf fp h where h Right{} = assertFailure "expected error."; h (Left e) = show e @?= expected

tF :: FilePath -> TestTree
tF fp = wf fp a where a Right{} = pure (); a (Left e) = assertFailure (show e)
