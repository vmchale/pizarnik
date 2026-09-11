module Nm.Set ( singleton
              , insert
              , (∈)
              ) where

import qualified Data.IntSet as IS
import           Nm

infix 4 ∈

singleton (Nm _ (U i) _) = IS.singleton i
insert (Nm _ (U i) _) = IS.insert i
(∈) (Nm _ (U i) _) = IS.member i
