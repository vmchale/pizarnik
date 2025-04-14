module Dbg ( dT, dFmt
           , adbg
           , module P
           ) where

import           A
import           Control.Exception         (throwIO)
import           Control.Monad             ((<=<))
import qualified Data.ByteString.Lazy      as BSL
import           Data.Foldable             (traverse_)
import           L
import           P
import           Parse
import           Pr
import           Prettyprinter             (defaultLayoutOptions, layoutSmart, pretty)
import           Prettyprinter.Render.Text (putDoc, renderIO)
import           System.IO                 (stdout)

adbg :: [FilePath] -> FilePath -> IO ()
adbg incls fp = do
    tms <- tMs incls fp
    case tms of
        Left err -> throwIO err
        Right ms -> traverse_ (rDoc.am) ms

dFmt :: BSL.ByteString -> IO ()
dFmt = (putDoc <=< either throwIO pure) . (fmap (pretty.snd).pFmt) where pFmt = parseA 0 alexInitUserState

dT :: [FilePath] -> FilePath -> IO ()
dT incls fp = do
    res <- rMs incls fp
    either throwIO (putDoc.pBound.thd3) res

rDoc = renderIO stdout.layoutSmart defaultLayoutOptions

thd3 (_,_,z) = z
