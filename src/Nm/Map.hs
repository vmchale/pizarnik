module Nm.Map ( insert
              , fromList
              ) where

import qualified Data.IntMap as IM
import           Nm

fromList :: [(Nm a, b)] -> IM.IntMap b
fromList xs = IM.fromList [ (i,x) | (Nm _ (U i) _, x) <- xs ]

insert :: Nm a -> b -> IM.IntMap b -> IM.IntMap b
insert (Nm _ (U i) _) = IM.insert i
