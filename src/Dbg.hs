module Dbg ( dT, dFmt, dbgR
           , adbg
           , module P
           ) where

import           A
import           Control.Exception         (throwIO)
import           Control.Monad             ((<=<))
import qualified Data.ByteString.Lazy      as BSL
import           Data.Foldable             (traverse_)
import qualified Data.IntMap               as IM
import           Data.Tree                 (Tree)
import           L
import           P
import           Parse
import           Pr
import           Prettyprinter             (Doc, defaultLayoutOptions, hardline, layoutSmart, pretty, vsep, (<+>))
import           Prettyprinter.Render.Text (putDoc, renderIO)
import           S
import           System.IO                 (stdout)

dbgR :: AlexUserState -> [Tree (F (TS AlexPosn), b)] -> IO ()
dbgR (_,_,n,_) = traverse_ (traverse_ (rDoc.(<>hardline).pBoundT.fst))
  where
    pBoundT :: IM.IntMap (ASeq (TS a)) -> Doc ann
    pBoundT = vsep.map (\(i,a) -> pretty (n IM.! i) <+> "→" <+> aT a).IM.toList

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
    either throwIO (putDoc.pBound.snd) res

rDoc = renderIO stdout.layoutSmart defaultLayoutOptions
