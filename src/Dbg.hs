module Dbg ( dT, dFmt
           , module P
           ) where

import           A
import           Control.Exception         (throwIO)
import           Control.Monad             ((<=<))
import qualified Data.ByteString.Lazy      as BSL
import           Data.Foldable             (traverse_)
import           Data.Tuple.Extra          (thd3)
import           L
import           P
import           Parse
import           Pr
import           Prettyprinter             (pretty)
import           Prettyprinter.Render.Text (putDoc)

adbg :: [FilePath] -> FilePath -> IO ()
adbg incls fp = do
    tms <- tMs incls fp
    case tms of
        Left err -> throwIO err
        Right ms -> traverse_ (putDoc.am) ms

dFmt :: BSL.ByteString -> IO ()
dFmt = (putDoc <=< either throwIO pure) . (fmap (pretty.snd).pFmt) where pFmt = parseA 0 alexInitUserState

dT :: [FilePath] -> FilePath -> IO ()
dT incls fp = do
    res <- rMs incls fp
    either throwIO (putDoc.pBound.thd3) res
