module P ( fmt, rMs, tMs, rc, e1, rRepl, db, rDoc ) where

import           A
import           Control.Monad                    (foldM)
import           Control.Monad.Except             (liftEither, throwError)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (ExceptT, except, runExceptT, withExceptT)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT, get, mapStateT, put)
import           Data.Bifunctor                   (bimap, first, second)
import qualified Data.ByteString.Lazy             as BSL
import           Data.Foldable                    (traverse_)
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import qualified Data.IntSet                      as IS
import           Data.Tree                        (Tree (..))
import           E
import           L
import           M
import           Nm
import           Parse
import           Prettyprinter                    (Doc, SimpleDocStream, defaultLayoutOptions, hardline, layoutSmart, pretty, vsep, (<+>))
import           Prettyprinter.Render.Text        (renderIO)
import           R
import           S
import           System.IO                        (stdout)
import           TS
import           Ty

type RIO = StateT AlexUserState (ExceptT (E AlexPosn) IO)

fmt :: BSL.ByteString -> Either ParseE (SimpleDocStream ann)
fmt = fmap (layoutSmart defaultLayoutOptions . pretty . snd) . pA

db :: AlexUserState -> [Tree (IM.IntMap (ASeq (TS AlexPosn)), b)] -> IO ()
db (_,_,n,_) = traverse_ (traverse_ (rDoc.(<>hardline).pBoundT.fst))
  where
    pBoundT :: IM.IntMap (ASeq (TS a)) -> Doc ann
    pBoundT = vsep.map (\(i,a) -> pretty (n IM.! i) <+> "→" <+> pASeq a).IM.toList

rDoc = renderIO stdout.layoutSmart defaultLayoutOptions

naïve :: [Tree (F (TS a), Ar)] -> Ext a
naïve t = Ext (foldMap (\(Node (m,_) _) -> aLs<$>m) t) IM.empty (foldMap (\(Node (_,a) _) -> a) t)

e1 :: [FilePath] -> [FilePath]
   -> BSL.ByteString
   -> IO (Either (E AlexPosn) (S AlexPosn))
e1 incls fp e = rRepl $ do
    c <- tMs incls fp
    l <- get
    case pAtoms l e of
        Left err -> throwError (PE err)
        Right ((i,_,_,_),at) ->
            liftEither $ fst <$> rc i (map (fmap (first lm)) c) [] at

rc :: Int -> Ctx (TS a) -> S a -> ASeq a -> Either (E a) (S a, Int)
rc i c s at = (\case ((TS (_:_:_) _,_),_) -> Left ES; ((_,a),u) -> Right (r c (aas a) s,u)) =<< first TyE (tAS i tm s at)
  where
    tm=naïve c

-- TODO: this will need type synonyms...
tMs :: [FilePath] -> [FilePath] -> RIO [Tree (M AlexPosn (TS AlexPosn), Ar)]
tMs incls fp = do
    (i,c) <- rMs incls fp
    (u,_,_,_) <- get
    let roots = [ c IM.! unU n | n <- i ]
        tr m@(M is _) = Node m (tr.(c IM.!).unU.mU<$>is)
    lift $ except $ bimap TyE (map (fmap (second arit))) (evalStateT (traverse (tg (mempty :: Ext AlexPosn).tr) roots) u)
  where
    tg c (Node n ns) = do
        ms <- traverse (tg c) ns
        let ctx = foldMap (snd.rootLabel) ms
        Node <$> tM ctx n <*> pure ms

rMs :: [FilePath] -- ^ Include dirs
    -> [FilePath] -- ^ Root modules
    -> RIO ([U], IM.IntMap (M AlexPosn AlexPosn))
rMs incls fp = do
    (rs, MS ms ims) <- mapStateT (withExceptT PE) $ pRoot incls fp
    st <- get
    let s=tsort ims
    (st',m) <- go (IS.fromList [ unU u | u <- rs ]) ms st IM.empty s
    put st' $> (rs,m)
  where
    go _ _ st _ [] = pure (st, IM.empty)
    go rs ms (u,t,ii,m) mex (n@(MN _ (U i)):mns) = do
        exc <- exs n deps
        (u',exϵ,md) <- lift $ except $ first RE $ rM u exc mp
        let st' = (if i `IS.member` rs then apply exϵ else id) (u',t,ii,m)
        second (IM.insert i md) <$> go rs ms st' (IM.insert i exϵ mex) mns
      where
        mp@(M is _)=m'lookup i ms; deps=(`mnlookup` mex)<$>is

    apply :: Ex -> AlexUserState -> AlexUserState
    apply (Ex ii0 _ ii1) = let ex'=ii0<>ii1 in \(u,t,i,mn) -> (u, fmap (\x -> IM.findWithDefault x x ex') t, i `fw` ex',mn)
      where
        -- FIXME: performance...
        fw m a = IM.mapKeys (\k -> IM.findWithDefault k k a) m

mnlookup (MN _ (U i)) = m'lookup i
m'lookup=IM.findWithDefault (error"Internal error: module not found.")

rRepl :: RIO a -> IO (Either (E AlexPosn) a)
rRepl = runExceptT.flip evalStateT (0,mempty,mempty,mempty)

exs :: MN -> [Ex] -> RIO Ex
exs n = foldM mx (Ex IM.empty IM.empty IM.empty)
  where
    mx :: Ex -> Ex -> RIO Ex
    mx (Ex bv0 bc0 a0) (Ex bv1 bc1 a1) = Ex <$> mi bv0 bv1 MDF <*> mi bc0 bc1 MDC <*> mi a0 a1 MDT
      where
        mi b0 b1 e | IM.disjoint b0 b1 = pure (b0<>b1) | otherwise = throwError (e n)
