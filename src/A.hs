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
         , am
         , tTS
         , pSeq
         ) where

import qualified Data.Text     as T
import           Nm
import           Nm.Map        (NmMap)
import qualified Nm.Map        as Nm
import           Pr
import qualified Data.Set as S
import           Prettyprinter (Doc, Pretty (..), align, braces, brackets, concatWith, dquotes, fillSep, group, hardline, hsep, line, parens, punctuate, tupled, (<+>))

infixl 9 <:>

data B = Dip | Dup | Un
       | Plus | Minus | Mul | Div
       | Swap | Eq | Gt | Lt
       | Doll

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

aT :: SL b (A (TS a)) -> Doc ann
aT = align.fillSep.fmap ana.aas

(<:>) x y = x <+> ":" <+> y

ana :: A (TS b) -> Doc ann
ana (B t a) = parens (pretty a <:> pretty t); ana (L t a) = parens (pretty a <:> pretty t)
ana (C t a) = parens (pretty a <:> pretty t); ana (V t a) = parens (pretty a <:> pretty t)
ana (Inv t a) = parens (pretty a <> "⁻¹" <:> pretty t); ana (Q t a) = parens (brackets (aT a) <:> pretty t)
ana (Pat t a) = group (braces (align (pA (map aT (aas a))))) <:> pretty t

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

data TS a = TS { tlefts, trights :: TSeq a } deriving (Eq, Ord)
type TSeq a = [T a]

tTS f (TS l r) = TS <$> traverse f l <*> traverse f r

data T a = TV { tL :: a, tvar :: Nm a } | TP { tL :: a, primty :: Prim }
         | QT { tL :: a, tq :: TS a } | SV { tL :: a, tSs :: Nm a }
         | TT { tL :: a, tagty :: Nm a } | Σ { tL :: a, tΣ :: NmMap (TSeq a) }
         | TA { tL :: a, tA0, tA1 :: T a } | TC { tL :: a, tCon :: Nm a }
         | TI { tL :: a, tI :: T a } | RV { tL :: a, tvar :: Nm a, uS :: S.Set (T a) }

instance Eq (T a) where
    (==) (TV _ n0) (TV _ n1) = n0==n1; (==) (TP _ t0) (TP _ t1) = t0==t1
    (==) (TT _ t0) (TT _ t1) = t0==t1; (==) (SV _ v0) (SV _ v1) = v0==v1
    (==) (TC _ n0) (TC _ n1) = n0==n1; (==) (TI _ t0) (TI _ t1) = t0==t1

instance Ord (T a) where
    compare (TV _ n0) (TV _ n1) = compare n0 n1; compare (TP _ t0) (TP _ t1) = compare t0 t1
    compare (TT _ t0) (TT _ t1) = compare t0 t1; compare (SV _ n0) (SV _ n1) = compare n0 n1
    compare (TC _ n0) (TC _ n1) = compare n0 n1; compare (TI _ t0) (TI _ t1) = compare t0 t1

data D a b = TD a (Nm a) [Nm a] (T a) | F b (Nm b) (TS a) (ASeq b)

anD :: D a (TS b) -> Doc ann
anD (F _ n t as) = pretty n <+> align (":" <+> pretty t <#> ":=" <+> brackets (align (fillSep (map ana (aas as)))))
anD d@TD{}       = pretty d

instance Functor (D a) where fmap _ (TD x n vs t) = TD x n vs t; fmap f (F x n ts as) = F (f x) (f<$>n) ts (faseq f as)

instance Pretty (D a b) where
    pretty (F _ n t as)  = pretty n <+> align (":" <+> pretty t <#> ":=" <+> brackets (pASeq as))
    pretty (TD _ n vs t) = "type" <+> pretty n <+> pSeq vs <+> "=" <+> pretty t <> ";"

am :: M a (TS b) -> Doc ann
am (M _ ds) = concatWith (<##>) (anD<$>ds) <> hardline

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

-- ⊂
instance Pretty (T a) where
    pretty (TV _ n) = pretty n; pretty (TP _ pty) = pretty pty; pretty (TC _ n) = pretty n
    pretty (QT _ ts) = brackets (pretty ts); pretty (SV _ n) = pretty n
    pretty (TT _ n) = pretty n; pretty (Σ _ ts) = braces (pΣ (hsep.(\(u,tsϵ) -> map pretty tsϵ++[pretty u])<$>Nm.toList ts))
    pretty (TA _ t t') = pretty t <> tupled (pretty<$>tunroll t')
    pretty (TI _ t) = pretty t <+> "⁻¹"
    pretty (RV _ n s) = parens (pretty n <+> "⊃" <+> braces (mconcat (punctuate ", " (pretty<$>S.toList s))))

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
