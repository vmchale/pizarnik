{-# LANGUAGE OverloadedStrings #-}

module A ( A (..)
         , B (..)
         , L (..)
         , Prim (..)
         , T (..), TS (..)
         , TSeq
         , D (..)
         , M (..)
         , SL (..), ASeq
         , taseq
         , tTS
         , pSeq
         ) where

import qualified Data.Text     as T
import           Nm
import           Pr
import           Prettyprinter (Doc, Pretty (..), align, braces, brackets, concatWith, dquotes, group, hardline, hsep, line, tupled, (<+>))

data B = Dip | Dup | Un
       | Plus | Minus | Mul | Div
       | Swap | Eq | Gt | Lt
       | Doll

-- cons?
-- polymorphic/recursive types

instance Pretty B where
    pretty Dip = "dip"; pretty Dup = "dup"; pretty Un = "_"
    pretty Plus = "+"; pretty Minus = "-"; pretty Mul = "*"; pretty Div = "%"
    pretty Swap = "swap"; pretty Eq = "="; pretty Gt = ">"; pretty Lt = "<"
    pretty Doll = "$"

data L = I !Integer | R !Double | Str !T.Text | BL !Bool

instance Pretty L where
    pretty (I i) = pretty i; pretty (R x) = pretty x; pretty (Str s) = dquotes (pretty s)
    pretty (BL b) = pretty b

data SL a b = SL { aLs :: a, aas :: [b] }
type ASeq a = SL a (A a)

data A a = B { aL :: a, builtin :: !B }
         | Q { aL :: a, aqs :: ASeq a } | L { aL :: a, lita :: L }
         | Pat { aL :: a, arms :: SL a (ASeq a) }
         | C { aL :: a, tagn :: Nm a } | V { aL :: a, fn :: Nm a }
         | Inv { aL :: a, inva :: A a }

faseq :: (a -> b) -> ASeq a -> ASeq b
faseq f (SL x xs) = SL (f x) (map (f<$>) xs)

taseq :: Applicative m => (a -> m b) -> ASeq a -> m (ASeq b)
taseq f (SL x xs) = SL <$> f x <*> f2 f xs where f2 g = traverse (traverse g)

instance Functor A where
    fmap f (B x b) = B (f x) b; fmap f (L x l) = L (f x) l
    fmap f (C x n) = C (f x) (f<$>n); fmap f (V x n) = V (f x) (f<$>n)
    fmap f (Q x as) = Q (f x) (faseq f as)
    fmap f (Pat x (SL y ys)) = Pat (f x) (SL (f y) (map (faseq f) ys))
    fmap f (Inv x a) = Inv (f x) (f<$>a)

instance Foldable A where

instance Traversable A where
    traverse f (B x b) = B <$> f x <*> pure b; traverse f (L x l) = L <$> f x <*> pure l
    traverse f (C x n) = C <$> f x <*> traverse f n; traverse f (V x n) = V <$> f x <*> traverse f n
    traverse f (Q x as) = Q <$> f x <*> taseq f as
    traverse f (Pat x (SL y ys)) = Pat <$> f x <*> (SL <$> f y <*> traverse (taseq f) ys)
    traverse f (Inv x a) = Inv <$> f x <*> traverse f a

data Prim = Int | Bool | String deriving (Eq, Ord)

instance Pretty Prim where pretty Int="Int"; pretty Bool="Bool"; pretty String="String"

data TS a = TS { tlefts, trights :: TSeq a }
type TSeq a = [T a]

tTS f (TS l r) = TS <$> traverse f l <*> traverse f r

data T a = TV { tL :: a, tvar :: Nm a } | TP { tL :: a, primty :: Prim }
         | QT { tL :: a, tq :: TS a } | SV { tL :: a, tSs :: Nm a }
         | TT { tL :: a, tagty :: Nm a } | Σ { tL :: a, tΣ :: [TSeq a] }
         | TA { tL :: a, tA0, tA1 :: T a } | TC { tL :: a, tCon :: Nm a }
         | TI { tL :: a, tI :: T a }

instance Eq (T a) where

instance Ord (T a) where
    compare (TT _ tt0) (TT _ tt1) = compare tt0 tt1
    compare TT{} _ = GT; compare _ TT{} = LT
    compare (TV _ n0) (TV _ n1) = compare n0 n1
    compare TV{} _ = GT; compare _ TV{} = LT
    compare (TP _ p0) (TP _ p1) = compare p0 p1
    compare TP{} _ = GT; compare _ TP{} = LT
    compare (SV _ n0) (SV _ n1) = compare n0 n1
    compare SV{} _ = GT; compare _ SV{} = LT
    compare (TC _ c0) (TC _ c1) = compare c0 c1
    compare TC{} _ = GT; compare _ TC{} = LT
    compare (TA _ t0 t0') (TA _ t1 t1') = case compare t0 t1 of {EQ -> compare t0' t1'; o -> o}
    compare TA{} _ = GT; compare _ TA{} = LT
    compare (TI _ t0) (TI _ t1) = compare t0 t1
    compare TI{} _ = GT; compare _ TI{} = LT

data D a b = TD a (Nm a) [Nm a] (T a) | F b (Nm b) (TS a) (ASeq b)

instance Functor (D a) where fmap _ (TD x n vs t) = TD x n vs t; fmap f (F x n ts as) = F (f x) (f<$>n) ts (faseq f as)

instance Pretty (D a b) where
    pretty (F _ n t as)  = pretty n <+> align (":" <+> pretty t <#> ":=" <+> brackets (pASeq as))
    pretty (TD _ n vs t) = "type" <+> pretty n <+> pSeq vs <+> "=" <+> pretty t <> ";"

data M a b = M [MN] [D a b]

instance Pretty (M a b) where
    pretty (M [] ds) = pDs ds
    pretty (M ms ds) = concatWith (<#>) (pI<$>ms) <##> pDs ds

pDs ds = "%-" <##> concatWith (<##>) (pretty<$>ds) <> hardline
pI n = "@i" <+> pretty n

instance Pretty (TS a) where
    pretty (TS [] tr) = "--" <+> pSeq tr; pretty (TS tl []) = pSeq tl <+> "--"
    pretty (TS tl tr) = pSeq tl <+> "--" <+> pSeq tr

instance Show (TS a) where show=show.pretty

tunroll :: T a -> [T a]
tunroll (TA _ t t') = t:tunroll t'
tunroll t           = [t]

instance Pretty (T a) where
    pretty (TV _ n) = pretty n; pretty (TP _ pty) = pretty pty; pretty (TC _ n) = pretty n
    pretty (QT _ ts) = brackets (pretty ts); pretty (SV _ n) = pretty n
    pretty (TT _ n) = pretty n; pretty (Σ _ ts) = braces (pΣ (hsep.fmap pretty<$>ts))
    pretty (TA _ t t') = pretty t <+> tupled (pretty<$>tunroll t')
    pretty (TI _ t) = pretty t <+> "⁻¹"

pΣ = concatWith (\x y -> x <+> "⊕" <+> y)

instance Show (T a) where show=show.pretty

instance Pretty (A a) where
    pretty (B _ b) = pretty b; pretty (Q _ as) = brackets (pASeq as)
    pretty (L _ l) = pretty l; pretty (Pat _ as) = group (braces (align (pA (map pASeq (aas as)))))
    pretty (C _ n) = pretty n; pretty (V _ n) = pretty n; pretty (Inv _ a) = pretty a <> "⁻¹"

pSeq :: Pretty a => [a] -> Doc ann
pSeq = hsep.fmap pretty

pASeq :: ASeq a -> Doc ann
pASeq = pSeq.aas

pA = concatWith (\x y -> x <+> "&" <> line <> y)

instance Show (A a) where show=show.pretty
