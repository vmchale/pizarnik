module P ( Ctx, S, dbg, fmt, rMs, tMs ) where

import           A
import           Control.Exception                (Exception, throw)
import           Control.Monad                    (foldM)
import           Control.Monad.Trans.Except       (ExceptT, except, throwE, withExceptT)
import           Control.Monad.Trans.State.Strict (evalStateT)
import           Data.Bifunctor                   (second)
import qualified Data.ByteString.Lazy             as BSL
import qualified Data.IntMap                      as IM
import           Data.Tree                        (Tree (..))
import           E
import           L
import           M
import           Nm
import           Parse
import           Prettyprinter                    (SimpleDocStream, defaultLayoutOptions, layoutSmart, pretty)
import           R
import           S
import           TS
import           Ty

type EIO a = ExceptT (E a) IO

dbg :: BSL.ByteString -> [L]
dbg src =
    let ((l,_,_,_),at) = x$pAtoms alexInitUserState src
        (a,_)=x (tAS l mempty at)
    in r (Node IM.empty []) a []
  where
    x :: Exception e => Either e a -> a
    x = either throw id

fmt :: BSL.ByteString -> Either ParseE (SimpleDocStream ann)
fmt = fmap (layoutSmart defaultLayoutOptions . pretty . snd) . pFmt
  where
    pFmt = parseA 0 alexInitUserState

pex :: MN -> Ex -> Ex -> EIO a Ex
pex n (Ex bv0 bc0 a0) (Ex bv1 bc1 a1) = Ex <$> m'merge bv0 bv1 MDF <*> m'merge bc0 bc1 MDC <*> m'merge a0 a1 MDT
  where
    m'merge b0 b1 err | IM.disjoint b0 b1 = pure (b0<>b1) | otherwise = throwE (err n)

tr :: IM.IntMap (M a b)
   -> Tree (M a b)
tr c = go (c IM.! (-1))
  where
    go m@(M is _) = Node m ((go.(c IM.!).unU.mU)<$>is)

tMs :: [FilePath] -> FilePath -> EIO AlexPosn (Tree (M AlexPosn (TS AlexPosn)))
tMs incls fp = do
    (u, rm) <- rMs incls fp
    withExceptT TyE $ except $ fmap fst <$> evalStateT (tg (mempty :: Ext AlexPosn) (tr rm)) u
  where
    tg c (Node n ns) = do
        ms <- traverse (tg c) ns
        let ctx = foldMap (snd.rootLabel) ms
        Node <$> tM ctx n <*> pure ms

rMs :: [FilePath] -- ^ Include dirs
    -> FilePath -- ^ Root module
    -> EIO AlexPosn (Int, IM.IntMap (M AlexPosn AlexPosn))
rMs incls fp = do
    (u, MS ms ims) <- withExceptT PE $ pRoot incls fp
    let s=tsort ims
    go ms u IM.empty s
  where
    go _ u _ []                      = pure (u, IM.empty)
    go ms u mex (n@(MN _ (U i)):mns) = do
        exc <- foldM (pex n) eex deps
        (u',exϵ,md) <- withExceptT RE $ except $ rM u exc mp
        second (IM.insert i md) <$> go ms u' (IM.insert i exϵ mex) mns
      where
        mp@(M is _)=m'lookup i ms; deps=(`mnlookup` mex)<$>is

mnlookup (MN _ (U i)) = m'lookup i
m'lookup=IM.findWithDefault (error"Internal error: module not found.")

eex = Ex IM.empty IM.empty IM.empty
