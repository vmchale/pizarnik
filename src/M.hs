module M ( MS (..), pRoot ) where

import           A
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.Except       (ExceptT, except)
import           Control.Monad.Trans.State.Strict (StateT (StateT))
import qualified Data.ByteString.Lazy             as BSL
import qualified Data.IntMap                      as IM
import qualified Data.Text                        as T
import           Data.Tuple                       (swap)
import           Imp
import           L
import           Loc
import           Nm
import           Parse

type R = StateT AlexUserState (ExceptT (ParseE Loc) IO)

data MS = MS (IM.IntMap (M Loc Loc)) [(MN, [MN])]

rMN :: T.Text -> R MN
rMN fp = mst $ pure.nMIdent (asMN fp)
  where
    asMN s | Just p <- T.stripSuffix ".piz" s = p
           | otherwise = error ("failed to read as module name: " ++ T.unpack s)

pRoot :: [FilePath] -- ^ Include dirs
      -> [FilePath] -- Modules
      -> R ([U], MS)
pRoot incls fps = do
    rootn <- traverse (rMN.T.pack) fps
    ms <- traverse pIO fps
    let is = map (\(M i _) -> i) ms
        rootU = map mU rootn
        initMs=MS (IM.fromList $ zip (map unU rootU) ms) (zip rootn is)
    ([], mϵ) <- step initMs (concat is)
    pure (rootU, mϵ)
  where
    step :: MS -> [MN] -> R ([MN], MS)
    step st [] = pure ([], st)
    step st@(MS mSt mDeps) (mn@(MN _ (U i)):mns)
        | i `IM.member` mSt = step st mns
        | otherwise = do
            m@(M is _) <- pMIO incls mn
            let nDeps=(mn,is):mDeps
                st'= MS (IM.insert i m mSt) nDeps
            step st' (is++mns)

mst :: (AlexUserState -> ExceptT (ParseE Loc) IO (AlexUserState, a)) -> R a
mst f = StateT $ fmap swap.f

pMIO :: [FilePath] -> MN -> R (M Loc Loc)
pMIO incls mn = do {fp <- liftIO (resolveI incls mn); pIO fp}

pIO :: FilePath -> R (M Loc Loc)
pIO fp = mst $ \st -> do {src <- liftIO (BSL.readFile fp); except (pM fp st src)}
