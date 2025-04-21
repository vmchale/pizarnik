module M ( ReplLexerSt, MS (..), pRoot ) where

import           A
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.Except       (ExceptT, except)
import           Control.Monad.Trans.State.Strict (StateT (StateT), runStateT)
import           Data.Bifunctor                   (first)
import qualified Data.ByteString.Lazy             as BSL
import qualified Data.IntMap                      as IM
import           Data.List.NonEmpty               (NonEmpty (..))
import qualified Data.Map                         as M
import qualified Data.Text                        as T
import           Data.Tuple                       (swap)
import           Imp
import           L
import           Nm
import           Parse

type MM = StateT AlexUserState (ExceptT ParseE IO)

data MS = MS (IM.IntMap (M AlexPosn AlexPosn)) [(MN, [MN])]

type ReplLexerSt = (Int, M.Map T.Text Int, IM.IntMap (Nm AlexPosn))

rMM :: MM a -> ExceptT ParseE IO (ReplLexerSt, a)
rMM = fmap (first π.swap).flip runStateT alexInitUserState where π (x,y,z,_)=(x,y,z)

pRoot :: [FilePath] -- ^ Include dirs
      -> FilePath -- ^ Root module
      -> ExceptT ParseE IO (ReplLexerSt, MS)
pRoot incls fp = rMM $ do
    m@(M is _) <- pIO fp
    let initMs=MS (IM.singleton (-1) m) [(rootn, is)]
    ([], ms) <- step initMs is
    pure ms
  where
    rootn = MN ("(root)" :| []) (U (-1))

    step :: MS -> [MN] -> MM ([MN], MS)
    step st [] = pure ([], st)
    step st@(MS mSt mDeps) (mn@(MN _ (U i)):mns)
        | i `IM.member` mSt = step st mns
        | otherwise = do
            m@(M is _) <- pMIO incls mn
            let nDeps=(mn,is):mDeps
                st'= MS (IM.insert i m mSt) nDeps
            step st' (is++mns)

mst :: (AlexUserState -> ExceptT ParseE IO (AlexUserState, a)) -> MM a
mst f = StateT $ fmap swap.f

pMIO :: [FilePath] -> MN -> MM (M AlexPosn AlexPosn)
pMIO incls mn = do {fp <- liftIO (resolveI incls mn); pIO fp}

pIO :: FilePath -> MM (M AlexPosn AlexPosn)
pIO fp = mst $ \st -> do
    contents <- liftIO $ BSL.readFile fp
    except $ pM st contents
