module Dbg ( dT, dFmt
           , module P
           ) where

import           Control.Exception         (throwIO)
import           Control.Monad             ((<=<))
import qualified Data.ByteString.Lazy      as BSL
import           Data.Tuple.Extra          (thd3)
import           L
import           P
import           Parse
import           Pr
import           Prettyprinter             (pretty)
import           Prettyprinter.Render.Text (putDoc)

dFmt :: BSL.ByteString -> IO ()
dFmt = (putDoc <=< either throwIO pure) . (fmap (pretty.snd).pFmt) where pFmt = parseA 0 alexInitUserState

dT :: [FilePath] -> FilePath -> IO ()
dT incls fp = do
    res <- rMs incls fp
    either throwIO (putDoc.pBound.thd3) res
