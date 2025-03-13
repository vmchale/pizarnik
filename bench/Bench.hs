module Main (main) where

import           Criterion.Main (bench, bgroup, defaultMain, whnfIO)
import           P

main = defaultMain
    [ bgroup "t"
        [ b fp | fp <- ["test/examples/maybe.piz", "lib/list.piz", "examples/vierergruppe.piz" ] ]
    ] where b fp = bench fp $ whnfIO $ tMs ["."] fp
