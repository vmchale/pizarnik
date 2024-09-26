module B ( Cs, β ) where

import           A
import qualified Data.IntMap as IM
import           Nm

type Cs a=IM.IntMap ([Nm a], T a); type Β a=IM.IntMap (T a)

β :: Cs a -> Nm a -> [T a] -> T a
β c n bs = let (vs,t) = lC n c in bS (IM.fromList$zipWith (\(Nm _ (U u) _) b -> (u,b)) vs bs) t

lC :: Nm a -> Cs a -> ([Nm a], T a)
lC (Nm _ (U i) _) = IM.findWithDefault (error "Internal error. Constructor not in scope?") i

bS :: Β a -> T a -> T a
bS st (TV _ (Nm _ (U j) _)) = IM.findWithDefault (error "Type constructor not fully applied?") j st
bS st (TA x t0 t1) = TA x (bS st t0) (bS st t1)
bS st (TI x t) = TI x (bS st t)
bS _ t@TT{} = t; bS _ t@TP{} = t
bS st (Σ x tss) = Σ x (map (map (bS st)) tss)
bS st (QT x sig) = QT x (mapTS (bS st) sig)
-- TODO: renamer for nested application
