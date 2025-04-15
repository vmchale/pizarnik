module M ( MS (..), pRoot ) where

import           A
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.Except       (ExceptT, except)
import           Control.Monad.Trans.State.Strict (StateT (StateT), runStateT)
import qualified Data.ByteString.Lazy             as BSL
import qualified Data.IntMap                      as IM
import           Data.List.NonEmpty               (NonEmpty (..))
import           Data.Tuple                       (swap)
import           Imp
import           L
import           Nm
import           Parse

type MM = StateT AlexUserState (ExceptT ParseE IO)

data MS = MS (IM.IntMap (M AlexPosn AlexPosn)) [(MN, [MN])]

rMM :: AlexUserState -> MM a -> ExceptT ParseE IO (a, AlexUserState)
rMM = flip runStateT

pRoot :: [FilePath] -- ^ Include dirs
      -> FilePath -- ^ Root module
      -> ExceptT ParseE IO (Int, MS)
pRoot incls fp = do
    (st', m@(M is _)) <- pIO fp alexInitUserState
    let initMs=MS (IM.singleton (-1) m) [(rootn, is)]
    (([], ms), (u,_,_,_)) <- rMM st' (pP initMs incls is)
    pure (u, ms)
  where
    rootn = MN ("(root)" :| []) (U (-1))

pP :: MS -> [FilePath] -> [MN] -> MM ([MN], MS)
pP st _ [] = pure ([], st)
pP st@(MS mSt _) incls (mn@(MN _ (U i)):mns)
    | i `IM.member` mSt = pP st incls mns
    | otherwise = do
        (nMs, st') <- pMM st incls mn
        pP st' incls (nMs++mns)

pMM :: MS -> [FilePath] -> MN -> MM ([MN], MS)
pMM (MS mSt mDeps) incls mn@(MN _ (U i)) = do
    m@(M is _) <- pMIO incls mn
    let nDeps=(mn,is):mDeps
    pure (is, MS (IM.insert i m mSt) nDeps)

mst :: (AlexUserState -> ExceptT ParseE IO (AlexUserState, a)) -> MM a
mst f = StateT $ fmap swap.f

pMIO :: [FilePath] -> MN -> MM (M AlexPosn AlexPosn)
pMIO incls mn = do
    fp <- resolveI incls mn
    mst (pIO fp)

pIO :: FilePath -> AlexUserState -> ExceptT ParseE IO (AlexUserState, M AlexPosn AlexPosn)
pIO fp st = do
    contents <- liftIO $ BSL.readFile fp
    except $ pM st contents
