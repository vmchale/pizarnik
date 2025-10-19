module Dbg ( dT, dFmt
           , adbg
           , module P
           ) where

import           A
import           Control.Exception         (throwIO)
import           Control.Monad             ((<=<))
import qualified Data.ByteString.Lazy      as BSL
import           Data.Foldable             (traverse_)
import           P
import           Parse
import           Pr
import           Prettyprinter             (pretty)
import           Prettyprinter.Render.Text (putDoc)

adbg :: [FilePath] -> [FilePath] -> IO ()
adbg incls fp = do
    tms <- rRepl $ tMs incls fp
    case tms of
        Left err -> throwIO err
        Right ms -> traverse_ (traverse_ (rDoc.am.fst)) ms

dFmt :: BSL.ByteString -> IO ()
dFmt = (putDoc <=< either throwIO pure) . (fmap (pretty.snd).pA)

dT :: [FilePath] -> [FilePath] -> IO ()
dT incls fps = do
    res <- rRepl $ rMs incls fps
    either throwIO (rDoc.pBound.snd) res
