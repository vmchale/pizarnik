module B ( β ) where

import           A
import           Control.Monad.State.Strict (StateT, runStateT)
import           Data.Bifunctor             (second)
import qualified Data.IntMap                as IM

type Β=IM.IntMap Int
data BSt=Bs { maxb :: !Int, bb :: Β }

data BE a

type BM a = StateT BSt (Either (BE a))

β :: Int -> T a -> T a -> T a
β = undefined

runBM :: Int -> BM a x -> Either (BE a) (x, Int)
runBM i = fmap (second maxb).flip runStateT (Bs i IM.empty)

bM :: T a -> T a -> BM a (T a)
bM = undefined
