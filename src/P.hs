module P ( fmt, rMs, tMs, rRepl ) where

import           A
import           Control.Monad                    (foldM)
import           Control.Monad.Except             (throwError)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (ExceptT, except, runExceptT, withExceptT)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT, get, mapStateT, put)
import           Data.Bifunctor                   (bimap, first, second)
import qualified Data.ByteString.Lazy             as BSL
import           Data.Functor                     (($>))
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

type RIO = StateT ReplLexerSt (ExceptT (E AlexPosn) IO)

fmt :: BSL.ByteString -> Either ParseE (SimpleDocStream ann)
fmt = fmap (layoutSmart defaultLayoutOptions . pretty . snd) . pA

-- FIXME: check for clashes
comb :: [M a b] -> RIO (M a b)
comb = foldM (\(M is ds) (M is' ds') -> pure (M (is++is') (ds++ds'))) (M [] [])

tMs :: [FilePath] -> [FilePath] -> RIO (Tree (M AlexPosn (TS AlexPosn), Ar))
tMs incls fp = do
    (i,c) <- rMs incls fp
    (u,_,_) <- get
    r <- comb [ c IM.! n | n <- i ]
    let tr m@(M is _) = Node m (tr.(c IM.!).unU.mU<$>is)
    lift $ except $ bimap TyE (fmap (second arit)) (evalStateT (tg (mempty :: Ext AlexPosn) (tr r)) u)
  where
    tg c (Node n ns) = do
        ms <- traverse (tg c) ns
        let ctx = foldMap (snd.rootLabel) ms
        Node <$> tM ctx n <*> pure ms

rMs :: [FilePath] -- ^ Include dirs
    -> [FilePath] -- ^ Root modules
    -> RIO ([Int], IM.IntMap (M AlexPosn AlexPosn))
rMs incls fp = do
    (rs, MS ms ims) <- mapStateT (withExceptT PE) $ pRoot incls fp
    (u,t,i) <- get
    let s=tsort ims
    (u',ex',m) <- go ms u undefined IM.empty s
    put (apply ex' (u',t,i)) $> (rs,m)
  where
    go _ u exϵ _ [] = pure (u, exϵ, IM.empty)
    go ms u _ mex (n@(MN _ (U i)):mns) = do
        exc <- exs n deps
        (u',exϵ,md) <- lift $ except $ first RE $ rM u exc mp
        second (IM.insert i md) <$> go ms u' exϵ (IM.insert i exϵ mex) mns
      where
        mp@(M is _)=m'lookup i ms; deps=(`mnlookup` mex)<$>is

    apply :: Ex -> ReplLexerSt -> ReplLexerSt
    apply (Ex ii0 _ ii1) = let ex'=ii0<>ii1 in \(u,t,i) -> (u, fmap (ex' IM.!) t, i `IM.compose` ex')

mnlookup (MN _ (U i)) = m'lookup i
m'lookup=IM.findWithDefault (error"Internal error: module not found.")

rRepl :: RIO a -> IO (Either (E AlexPosn) a)
rRepl = runExceptT.flip evalStateT (0,mempty,mempty)

exs :: MN -> [Ex] -> RIO Ex
exs n = foldM mx (Ex IM.empty IM.empty IM.empty)
  where
    mx :: Ex -> Ex -> RIO Ex
    mx (Ex bv0 bc0 a0) (Ex bv1 bc1 a1) = Ex <$> mi bv0 bv1 MDF <*> mi bc0 bc1 MDC <*> mi a0 a1 MDT
      where
        mi b0 b1 e | IM.disjoint b0 b1 = pure (b0<>b1) | otherwise = throwError (e n)
