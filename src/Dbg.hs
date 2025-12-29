module Dbg ( adbg
           , module P
           ) where

import           A
import           Control.Exception (throwIO)
import           Data.Foldable     (traverse_)
import           P
import           Pr
import           Prettyprinter     (pretty)

adbg :: [FilePath] -> [FilePath] -> IO ()
adbg incls fp = do
    tms <- rRepl $ tMs incls fp
    case tms of
        Left err -> throwIO err
        Right ms -> traverse_ (traverse_ (rDoc.(\(mn,m,_,_) -> pretty mn <> ":" <##> am m))) ms
