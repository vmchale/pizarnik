{-# LANGUAGE OverloadedStrings #-}

module B ( Cs, BE, β ) where

import           A
import qualified Data.IntMap   as IM
import qualified Data.Set      as S
import           Nm
import           Prettyprinter (Pretty (pretty), (<+>))

type Cs a=IM.IntMap ([Nm a], T S.Set a); type Β a=IM.IntMap (T S.Set a)

newtype BE a = TCA (Nm a)

instance Pretty a => Pretty (BE a) where pretty (TCA n) = pretty (loc n) <> ":" <+> "Type constructor not fully applied"

β :: Cs a -> Nm a -> [T S.Set a] -> Either (BE a) (T S.Set a)
β c n bs = let (vs,t) = lC n c in bS (IM.fromList$zipWith (\(Nm _ (U u) _) b -> (u,b)) vs bs) t

lC :: Nm a -> Cs a -> ([Nm a], T S.Set a)
lC (Nm _ (U i) _) = IM.findWithDefault (error "Internal error. Constructor not in scope?") i

bS :: Β a -> T S.Set a -> Either (BE a) (T S.Set a)
bS st (TV _ n@(Nm _ (U j) _)) =
    case IM.lookup j st of
        Nothing -> Left $ TCA n
        Just t  -> Right t
-- guard against TCA when substituting (but guarding against recursion)
bS st (TA x t0 t1) = TA x <$> bS st t0 <*> bS st t1
bS st (TI x t) = TI x <$> bS st t
bS _ t@TT{} = pure t; bS _ t@TP{} = pure t
bS st (Σ x tss) = Σ x <$> tS (traverse (bS st)) tss
bS st (QT x sig) = QT x <$> tTS (bS st) sig
-- TODO: rename/nested application?

tS f = fmap S.fromList . traverse f . S.toList
