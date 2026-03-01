module P ( Cs, fmt, rMs, tMs, rc, e1, rRepl, db, rDoc, naïve ) where

import           A
import           Control.Monad                    (foldM)
import           Control.Monad.Except             (liftEither, throwError)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (ExceptT, except, runExceptT, withExceptT)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT, get, mapStateT, put)
import           D
import           Data.Bifunctor                   (bimap, first, second)
import qualified Data.ByteString.Lazy             as BSL
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import qualified Data.IntSet                      as IS
import           Data.Tree                        (Tree (..))
import           E
import           L
import           Loc
import           M
import           Nm
import           Parse
import           Prettyprinter                    (Doc, SimpleDocStream, defaultLayoutOptions, hardline, layoutSmart, pretty, vsep, (<+>))
import           Prettyprinter.Render.Text        (renderIO)
import           Q
import           R
import           S
import           System.IO                        (stdout)
import           TS
import           Ty

type RIO = StateT AlexUserState (ExceptT (E Loc) IO)

fmt :: FilePath -> BSL.ByteString -> Either (ParseE Loc) (SimpleDocStream ann)
fmt = (fmap (layoutSmart defaultLayoutOptions.pretty.snd) .) . pA

db :: AlexUserState -> (IM.IntMap (ASeq (TS a)), b, c) -> IO ()
db (_,_,n,_) = rDoc.(<>hardline).pBoundT
  where
    pBoundT :: (IM.IntMap (ASeq (TS a)), b, c) -> Doc ann
    pBoundT (aa,_,_) = vsep (map (\(i,a) -> pretty (n IM.! i) <+> "→" <+> pASeq a) (IM.toList aa))

rDoc = renderIO stdout.layoutSmart defaultLayoutOptions

e1 :: [FilePath] -> [FilePath]
   -> BSL.ByteString
   -> IO (Either (E Loc) (S Loc))
e1 incls fp e = rRepl $ do
    c <- tMs incls fp
    l <- get
    case pAtoms l e of
        Left err -> throwError (no<$>PE err)
        Right ((i,_,_,_),at) ->
            liftEither (fst <$> rc i (naïve c) [] (faseq no at))

-- TODO inefficient but I think this won't cause problems b/c we already renamed
naïve :: [Tree (MN Loc, M a (TS a), Cs a, Ar)] -> MC (TS a) a
naïve c = (foldMap ((lm.snd4)@<>) c, foldMap (thd4@<>) c, IM.fromDistinctAscList [(-2,0),(-1,0)] <> foldMap (fth4@<>) c)
  where snd4 (_,y,_,_)=y; thd4 (_,_,z,_)=z; fth4 (_,_,_,w)=w

rc :: Int -> MC (TS a) a -> S a -> ASeq a -> Either (E a) (S a, Int)
rc i c s at = (\case ((TS (_:_:_) _,_),_) -> Left ES; ((_,a),u) -> Right (r c (aas a) s,u)) =<< first TyE (tAS i (π c) s at)
  where
    π (b,cϵ,a) = Ext (fmap aLs b) cϵ a

-- dbgS :: S a -> Doc ann
-- dbgS = hsep.map (\a -> parens (pretty a <+> ":" <+> pretty (aL a)))

tMs :: [FilePath] -> [FilePath] -> RIO [Tree (MN Loc, M Loc (TS Loc), Cs Loc, Ar)]
tMs incls fp = do
    (i,c,mns) <- rMs incls fp
    (u,_,_,_) <- get
    let roots = [ (c `ul` n, mns `ul` n) | n <- i ]
        tr (m@(M is _), mn) = Node (mn, m) (tr.(\n -> let uϵ=mU n in (c `ul` uϵ, mns `ul` uϵ))<$>is)
    lift $ except $ bimap TyE (map (fmap (\(n,x,t)->(n,x,tds t,arit t)))) (evalStateT (traverse (tg (mempty :: Ext Loc).tr) roots) u)
  where
    tg c (Node (mn,n) ns) = do
        ms <- traverse (tg c) ns
        let ctx = foldMap (thd3.rootLabel) ms
        (mT,cϵ) <- tM ctx n
        pure (Node (mn,mT,cϵ) ms)
      where
        thd3 (_,_,z)=z
    ul x (U i) = x IM.! i

rMs :: [FilePath] -- ^ Include dirs
    -> [FilePath] -- ^ Root modules
    -> RIO ([U], IM.IntMap (M Loc Loc), IM.IntMap (MN Loc))
rMs incls fp = do
    (rs, MS ms ims) <- mapStateT (withExceptT PE) $ pRoot incls fp
    st <- get
    let s=tsort ims rs
    (st',m) <- go (IS.fromList [ unU u | u <- rs ]) ms st IM.empty s
    let dbgM=IM.fromList [ (i,mn) | mn@(MN _ (U i) _) <- s ]
    put st' $> (rs,m,dbgM)
  where
    go _ _ st _ [] = pure (st, IM.empty)
    go rs ms (u,t,ii,m) mex (n@(MN _ (U i) _):mns) = do
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

mnlookup (MN _ (U i) _) = m'lookup i
m'lookup=IM.findWithDefault (error"Internal error: module not found.")

rRepl :: RIO a -> IO (Either (E Loc) a)
rRepl = runExceptT.flip evalStateT (0,mempty,mempty,mempty)

exs :: MN Loc -> [Ex] -> RIO Ex
exs n = foldM mx (Ex IM.empty IM.empty IM.empty)
  where
    mx :: Ex -> Ex -> RIO Ex
    mx (Ex bv0 bc0 a0) (Ex bv1 bc1 a1) = Ex <$> mi bv0 bv1 MDF <*> mi bc0 bc1 MDC <*> mi a0 a1 MDT
      where
        mi b0 b1 e | IM.disjoint b0 b1 = pure (b0<>b1) | otherwise = throwError (e n)
