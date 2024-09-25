module B ( β ) where

import           A
import           Control.Monad.State.Strict (StateT, runStateT)
import           Data.Bifunctor             (second)
import qualified Data.IntMap                as IM
import           Nm
import           Ty.Clone

type Cs a=IM.IntMap ([Nm a], T a)
type Β a=IM.IntMap (T a)
data BSt a=Bs { maxb :: !Int, bb :: Β a }

data BE a

type BM a = StateT (BSt a) (Either (BE a))

β :: Int -> Cs a -> T a -> [T a] -> Either (BE a) (T a, Int)
β i c t bs = runBM i (bM c t bs) -- undefined

runBM :: Int -> BM a x -> Either (BE a) (x, Int)
runBM i = fmap (second maxb).flip runStateT (Bs i IM.empty)

bM :: Cs a -> T a -> [T a] -> BM a (T a)
bM = undefined
