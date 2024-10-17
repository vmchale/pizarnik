module Ty.Clone ( cloneSig ) where

import           A
import           Control.Monad.Trans.State.Strict (State, gets, modify, runState)
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import           Nm

type BS = IM.IntMap Int
data RT = RT { maxT :: !Int, bTV, bSV :: BS }

type RM = State RT

incrMaxT :: RT -> RT
incrMaxT (RT m bv bs) = RT (m+1) bv bs

ibTV, ibSV :: RIns
ibTV i j (RT m bv bs) = RT m (IM.insert i j bv) bs
ibSV i j (RT m bv bs) = RT m bv (IM.insert i j bs)

type RIns = Int -> Int -> RT -> RT

fr :: RIns -> Nm a -> RM (Nm a)
fr g (Nm n (U i) l) = do
    modify incrMaxT
    j <- gets maxT
    modify (g i j) $> Nm n (U j) l

try :: (RT -> BS) -> RIns -> Nm a -> RM (Nm a)
try v g n@(Nm t (U i) l) = do
    st <- gets v
    case IM.lookup i st of
        Just j  -> pure (Nm t (U j) l)
        Nothing -> fr g n

tryTV, trySV :: Nm a -> RM (Nm a)
tryTV=try bTV ibTV; trySV=try bSV ibSV

cloneSig :: Int -> TS a -> (Int, TS a)
cloneSig u = (\(ts,RT uϵ _ _) -> (uϵ,ts)).flip runState (RT u IM.empty IM.empty) . cloneSigM

cloneSigM :: TS a -> RM (TS a)
cloneSigM (TS tl tr) = TS <$> traverse cT tl <*> traverse cT tr
  where
    cT t@TP{} = pure t; cT t@TT{} = pure t; cT t@TC{} = pure t
    cT (TV x n) = TV x <$> tryTV n; cT (SV x n) = SV x <$> trySV n
    cT (QT x ts) = QT x <$> cloneSigM ts
    cT (TA x t ts) = TA x <$> cT t <*> cT ts
    cT (Σ x ts) = Σ x <$> traverse (traverse cT) ts
    cT (TI x t) = TI x <$> cT t
