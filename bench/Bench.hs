module Main (main) where

import           Criterion.Main (bench, bgroup, defaultMain, whnfIO)
import           P

main = defaultMain
    [ bgroup "t"
        [ b fp | fp <- [ "test/examples/maybe.piz"
                       , "lib/fingertree.piz"
                       , "examples/vierergruppe.piz"
                       , "examples/ast.piz"
                       ]
        ]
    , bgroup "e"
        [ be ["examples/set.piz", "test/examples/set.piz"] "x 3 x member 6 x member 7 x member"
        , be ["examples/ast.piz"] "0 \"b\" `name `var 0 \"a\" `name `var `ap 0 \"a\""
        ]
    ] where b fp = bench fp $ whnfIO $ rRepl $ tMs ["."] [fp]
            be fp x = bench (head fp) $ whnfIO $ e1 ["."] fp x
