module Nm.Set ( singleton
              , insert
              , member
              ) where

import qualified Data.IntSet as IS
import           Nm

infix 4 `member`

singleton (Nm _ (U i) _) = IS.singleton i
insert (Nm _ (U i) _) = IS.insert i
member (Nm _ (U i) _) = IS.member i
