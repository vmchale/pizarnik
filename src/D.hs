module D ( Ar, Cs ) where

import           A
import qualified Data.IntMap as IM
import           Nm

type Ar = IM.IntMap Int
type Cs a = IM.IntMap ([Nm a], T a)
