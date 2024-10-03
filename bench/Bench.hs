module Main (main) where

import           Criterion.Main (bench, bgroup, defaultMain, whnfIO)
import           P

main = defaultMain
    [ bgroup "r"
        [ bench "test/deps/c.piz" $ whnfIO $ rMs ["test/deps"] "test/deps/c.piz"
        , bench "lib/list.piz" $ whnfIO $ rMs ["."] "lib/list.piz"
        ]
    , bgroup "t"
        [ bench "test/examples/ifte.piz" $ whnfIO $ tMs ["."] "test/examples/ifte.piz"
        , bench "examples/vierergruppe.piz" $ whnfIO $ tMs ["."] "examples/vierergruppe.piz"
        ]
    ]
