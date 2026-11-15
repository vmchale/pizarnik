module Main (main) where

import           Control.Monad.Trans.State.Strict (evalStateT)
import qualified Data.ByteString.Lazy             as BSL
import           REPL
import           System.Console.Haskeline         (defaultSettings, runInputTBehavior, useFile)
import           System.IO                        (hClose)
import           System.IO.Silently               (silence)
import           System.IO.Temp                   (withSystemTempFile)
import           Test.Tasty                       (defaultMain, testGroup)
import           Test.Tasty.Golden                (goldenVsString)

main = defaultMain $ testGroup "REPL"
  [ gR ["examples/set.piz"] "i/ex/rot.piz" "i/o/rot.out"
  , gR ["examples/systemT.piz"] "i/ex/s.piz" "i/o/s.out"
  ]
  where
    gR src inp out = goldenVsString inp out (testRepl src inp)

testRepl :: [FilePath] -> FilePath -> IO BSL.ByteString
testRepl src fp = withSystemTempFile "REPL" $ \t h -> do
    st <- iRepl src
    silence $ flip evalStateT st $ runInputTBehavior (useFile fp) defaultSettings (loop h)
    hClose h *> BSL.readFile t

-- -<.>
