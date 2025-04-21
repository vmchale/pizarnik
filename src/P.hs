{-# LANGUAGE TupleSections #-}

module P ( fmt, rMs, tMs ) where

import           A
import           Control.Monad                    (foldM)
import           Control.Monad.Trans.Except       (ExceptT, except, throwE, withExceptT)
import           Control.Monad.Trans.State.Strict (evalStateT)
import           Data.Bifunctor                   (bimap, first, second)
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
import           TS
import           Ty

type EIO a = ExceptT (E a) IO

fmt :: BSL.ByteString -> Either ParseE (SimpleDocStream ann)
fmt = fmap (layoutSmart defaultLayoutOptions . pretty . snd) . pA

pex :: MN -> Ex -> Ex -> EIO a Ex
pex n (Ex bv0 bc0 a0) (Ex bv1 bc1 a1) = Ex <$> m'merge bv0 bv1 MDF <*> m'merge bc0 bc1 MDC <*> m'merge a0 a1 MDT
  where
    m'merge b0 b1 err | IM.disjoint b0 b1 = pure (b0<>b1) | otherwise = throwE (err n)

tr :: IM.IntMap (M a b)
   -> Tree (M a b)
tr c = go (c IM.! (-1))
  where
    go m@(M is _) = Node m (go.(c IM.!).unU.mU<$>is)

tMs :: [FilePath] -> FilePath -> EIO AlexPosn (ReplLexerSt, Tree (M AlexPosn (TS AlexPosn), Ar))
tMs incls fp = do
    (st@(u,_,_), rm) <- rMs incls fp
    except $ (st,) <$> bimap TyE (fmap (second arit)) (evalStateT (tg (mempty :: Ext AlexPosn) (tr rm)) u)
  where
    tg c (Node n ns) = do
        ms <- traverse (tg c) ns
        let ctx = foldMap (snd.rootLabel) ms
        Node <$> tM ctx n <*> pure ms

rMs :: [FilePath] -- ^ Include dirs
    -> FilePath -- ^ Root module
    -> EIO AlexPosn (ReplLexerSt, IM.IntMap (M AlexPosn AlexPosn))
rMs incls fp = do
    ((u,t,i), MS ms ims) <- withExceptT PE $ pRoot incls fp
    let s=tsort ims
    (u',ex',m) <- go ms u undefined IM.empty s
    pure (apply ex' (u',t,i), m)
  where
    go _ u exϵ _ []                      = pure (u, exϵ, IM.empty)
    go ms u _ mex (n@(MN _ (U i)):mns) = do
        exc <- foldM (pex n) eex deps
        (u',exϵ,md) <- except $ first RE $ rM u exc mp
        second (IM.insert i md) <$> go ms u' exϵ (IM.insert i exϵ mex) mns
      where
        mp@(M is _)=m'lookup i ms; deps=(`mnlookup` mex)<$>is

    apply :: Ex -> ReplLexerSt -> ReplLexerSt
    apply (Ex ii0 _ ii1) = let ex'=ii0<>ii1 in \(u,t,i) -> (u, fmap (ex' IM.!) t, i `IM.compose` ex')

mnlookup (MN _ (U i)) = m'lookup i
m'lookup=IM.findWithDefault (error"Internal error: module not found.")

eex = Ex IM.empty IM.empty IM.empty
