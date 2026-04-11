module Main (main) where

import           Control.Exception         (throwIO)
import qualified Data.ByteString.Lazy      as BSL
import qualified Data.Text.Lazy.Encoding   as TL
import           P
import           Prettyprinter.Render.Text (renderLazy)
import           System.FilePath           (takeBaseName, (<.>), (</>))
import           Test.Tasty                (defaultMain, testGroup)
import           Test.Tasty.Golden         (goldenVsString)

main = defaultMain $
    testGroup "o" [tP "test/examples/exp.piz"]

tP fp = goldenVsString ("fmt (" ++ fp ++ ")") o (either throwIO (pure.w).fmt fp =<< BSL.readFile fp)
  where o = "test/fmt" </> takeBaseName fp <.> "out"
        w = TL.encodeUtf8.renderLazy
