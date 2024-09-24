module Main (main) where

import           Criterion.Main (bench, bgroup, defaultMain, whnfIO)
import           P

main = defaultMain
    [ bgroup "r"
        [ bench "test/deps/c.piz" $ whnfIO $ rMs ["test/deps"] "test/deps/c.piz"
        , bench "lib/list.piz" $ whnfIO $ rMs ["."] "lib/list.piz"
        ]
    , bgroup "t"
        [ bench "prelude/fn.piz" $ whnfIO $ tMs [] "prelude/fn.piz"
        ]
    ]
