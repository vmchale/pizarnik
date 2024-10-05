module Main (main) where

import           Criterion.Main (bench, bgroup, defaultMain, whnfIO)
import           P

main = defaultMain
    [ bgroup "t"
        [ bench "test/examples/ifte.piz" $ whnfIO $ tMs ["."] "test/examples/ifte.piz"
        , bench "examples/vierergruppe.piz" $ whnfIO $ tMs ["."] "examples/vierergruppe.piz"
        ]
    ]
