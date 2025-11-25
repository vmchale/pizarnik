module Dbg ( dFmt
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
import           Prettyprinter             (pretty)
import           Prettyprinter.Render.Text (putDoc)

adbg :: [FilePath] -> [FilePath] -> IO ()
adbg incls fp = do
    tms <- rRepl $ tMs incls fp
    case tms of
        Left err -> throwIO err
        Right ms -> traverse_ (traverse_ (rDoc.am.fst3)) ms
  where
    fst3 (x,_,_)=x

dFmt :: BSL.ByteString -> IO ()
dFmt = (putDoc <=< either throwIO pure) . (fmap (pretty.snd).pA)
