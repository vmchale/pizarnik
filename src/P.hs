module P ( fmt, rMs, tZ ) where

import           A
import           Control.Exception    (throwIO)
import           Control.Monad        (foldM)
import           Data.Bifunctor       (second)
import qualified Data.ByteString.Lazy as BSL
import qualified Data.IntMap          as IM
import           Data.Tree            (Tree (Node))
import           L
import           M
import           Nm
import           Parse
import           Prettyprinter        (SimpleDocStream, defaultLayoutOptions, layoutSmart, pretty)
import           R
import           TS
import           Ty

fmt :: BSL.ByteString -> Either ParseE (SimpleDocStream ann)
fmt = fmap (layoutSmart defaultLayoutOptions . pretty . snd) . pFmt
  where
    pFmt = parseA 0 alexInitUserState

pex :: MN -> Ex -> Ex -> Either (RE a) Ex
pex n (Ex bv0 bc0 a0) (Ex bv1 bc1 a1) = Ex <$> m'merge bv0 bv1 MDF <*> m'merge bc0 bc1 MDC <*> m'merge a0 a1 MDT
  where
    m'merge b0 b1 err | IM.disjoint b0 b1 = Right (b0<>b1) | otherwise = Left (err n)

tR :: IM.IntMap (M AlexPosn AlexPosn) -> Int -> [MN] -> Either (TE AlexPosn) (IM.IntMap (M AlexPosn (TS AlexPosn)))
tR rms = loop IM.empty where
    loop _ _ [] = Right IM.empty
    loop b u (MN _ (U i):mns) =
        let m@(M is _)=m'lookup i rms
            ctx=foldMap (`mnlookup` b) is
        in do
            (res, c, u') <- tM u ctx m
            IM.insert i res <$> loop (IM.insert i c b) u' mns

tr :: IM.IntMap (M a b)
   -> Tree (M a b)
tr c = go (c IM.! (-1))
  where
    go m@(M is _) = Node m ((go.(c IM.!).unU.mU)<$>is)

tZ :: [FilePath] -> FilePath -> IO (Either (TE AlexPosn) (Tree (M AlexPosn (TS AlexPosn))))
tZ incls fp = fmap tr <$> tMs incls fp

tMs :: [FilePath]
    -> FilePath -- ^ Root module
    -> IO (Either (TE AlexPosn) (IM.IntMap (M AlexPosn (TS AlexPosn))))
tMs incls fp = do
    (u, s, rms) <- io =<< rMs incls fp
    pure (tR rms u s)
  where
    io = either throwIO pure

rMs :: [FilePath] -- ^ Include dirs
    -> FilePath -- ^ Root module
    -> IO (Either (RE AlexPosn) (Int, [MN], IM.IntMap (M AlexPosn AlexPosn)))
rMs incls fp = do
    (u, MS ms ims) <- pRoot incls fp
    let s=tsort ims
    pure ((\(i,x) -> (i,s,x))<$>go ms u IM.empty s)
  where
    go _ u _ []                      = Right (u, IM.empty)
    go ms u mex (n@(MN _ (U i)):mns) = do
        exc <- foldM (pex n) eex deps
        (u',exϵ,md) <- rM u exc mp
        second (IM.insert i md) <$> go ms u' (IM.insert i exϵ mex) mns
      where
        mp@(M is _)=m'lookup i ms; deps=(`mnlookup` mex)<$>is

mnlookup (MN _ (U i)) = m'lookup i
m'lookup=IM.findWithDefault (error"Internal error: module not found.")

eex = Ex IM.empty IM.empty IM.empty
