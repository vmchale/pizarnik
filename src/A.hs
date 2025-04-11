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
         , unA
         , am
         , tTS
         , pSeq
         ) where

import           Control.Monad.Trans.State.Strict (State, evalState, get, modify, put)
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import qualified Data.Set                         as S
import qualified Data.Text                        as T
import           Nm
import           Nm.Map                           (NmMap, nmlist)
import qualified Nm.Map                           as Nm
import           Pr
import           Prettyprinter                    (Doc, Pretty (..), align, braces, brackets, concatWith, dquotes, fillSep, flatAlt, group, hardline, hsep, line, parens, pipe,
                                                   punctuate, space, tupled, (<+>))

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

data L = I !Integer | R !Double | Str !T.Text

instance Pretty L where
    pretty (I i) = pretty i; pretty (R x) = pretty x; pretty (Str s) = dquotes (pretty s)

data RR = RR !Char !Char
data W = W (RR->T.Text) (RR->RR)

class PT a where pp :: a -> State (S.Set T.Text, IM.IntMap T.Text, RR) a

class P0 a where p0 :: a -> Doc ann

ppt :: PT a => a -> a
ppt = flip evalState (S.empty, IM.empty, RR 'a' 'A').pp

vr = W (\(RR x _) -> T.singleton x) (\(RR v s) -> RR (succ v) s)
sr = W (\(RR _ x) -> T.pack ['\'',x]) (\(RR v s) -> RR v (succ s))

fr :: W -> Nm a -> State (S.Set T.Text, IM.IntMap T.Text, RR) (Nm a)
fr s (Nm t (U i) l) = do
    (ms,u,c) <- get
    case IM.lookup i u of
        Just n                 -> pure (Nm n (U i) l)
        _ | t `S.notMember` ms -> put (S.insert t ms, IM.insert i t u, c) $> Nm t (U i) l
        _                      -> do {t' <- next s; modify (bimap12 (S.insert t') (IM.insert i t')) $> Nm t' (U i) l}
  where bimap12 f g ~(x,y,z) = (f x,g y,z)

next l@(W g s) = do
    (ms,_,c) <- get
    let t=g c in if t `S.notMember` ms
                      then pure t
                      else modify (third3 s) *> next l
  where third3 f ~(x,y,z) = (x,y,f z)

data SL a b = SL { aLs :: a, aas :: [b] }
type ASeq a = SL a (A a)

data A a = B { aL :: a, builtin :: !B }
         | Q { aL :: a, aqs :: ASeq a } | L { aL :: a, lita :: L }
         | Pat { aL :: a, arms :: SL a (ASeq a) }
         | C { aL :: a, tagn :: Nm a } | V { aL :: a, fn :: Nm a }
         | Inv { aL :: a, inva :: A a }

aT :: SL b (A (TS a)) -> Doc ann
aT = align.fillSep.map ana.aas

(<:>) x y = x <+> ":" <+> y

ana :: A (TS b) -> Doc ann
ana (B t a) = parens (pretty a <:> p0 t); ana (L t a) = parens (pretty a <:> p0 t)
ana (C t a) = parens (pretty a <:> p0 t); ana (V t a) = parens (pretty a <:> p0 t)
ana (Inv t a) = parens (pretty a <> "⁻¹" <:> p0 t); ana (Q t a) = parens (brackets (aT a) <:> p0 t)
ana (Pat t a) = group (braces (align (pA (map aT (aas a))))) <:> p0 t

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

instance Foldable A where foldr=undefined

instance Traversable A where
    traverse f (B x b) = B <$> f x <*> pure b; traverse f (L x l) = L <$> f x <*> pure l
    traverse f (C x n) = C <$> f x <*> traverse f n; traverse f (V x n) = V <$> f x <*> traverse f n
    traverse f (Q x as) = Q <$> f x <*> taseq f as
    traverse f (Pat x (SL y ys)) = Pat <$> f x <*> (SL <$> f y <*> traverse (taseq f) ys)
    traverse f (Inv x a) = Inv <$> f x <*> traverse f a

data Prim = Int | String deriving (Eq, Ord)

instance Pretty Prim where pretty Int="Int"; pretty String="String"

data TS a = TS { tlefts, trights :: TSeq a } deriving (Eq, Ord)
type TSeq a = [T a]

tTS f (TS l r) = TS <$> traverse f l <*> traverse f r

data T a = TV { tL :: a, tvar :: Nm a } | TP { tL :: a, primty :: Prim }
         | QT { tL :: a, tq :: TS a } | SV { tL :: a, tSs :: Nm a }
         | TT { tL :: a, tagty :: Nm a } | Σ { tL :: a, tΣ :: NmMap (TSeq a) }
         | TA { tL :: a, tA0, tA1 :: T a } | TC { tL :: a, tCon :: Nm a }
         -- TODO: scope RV by "arms" so that { J(a) `a } and { J(Int) `a } produce a=Int
         -- (still allow a, b etc. as "heads"...)
         -- hm need some examples
         | TI { tL :: a, tI :: T a } | Ρ { tL :: a, tvar :: Nm a, tΡ :: NmMap (TSeq a), uS :: S.Set (T a) }
         | UU { tL :: a, uts :: [T a] }

instance PT (T a) where
    pp t@TP{}          = pure t
    pp t@TT{}          = pure t
    pp t@TC{}          = pure t
    pp t@Ρ{}           = pure t
    pp (TV x n)        = TV x <$> fr vr n
    pp (SV x n)        = SV x <$> fr sr n
    pp (TI x t)        = TI x <$> pp t
    pp (TA x t₀ t₁)    = TA x <$> pp t₀ <*> pp t₁
    pp (QT x (TS l r)) = QT x <$> (TS <$> traverse pp l <*> traverse pp r)
    pp (UU x ts)       = UU x <$> traverse pp ts
    pp (Σ x a)         = Σ x <$> traverse (traverse pp) a

instance PT (TS a) where pp (TS l r) = TS <$> traverse pp l <*> traverse pp r

unA :: T a -> Maybe (T a, [T a])
unA t | (th@TC{}:a) <- tunroll t = Just (th,a) | otherwise = Nothing

instance Eq (T a) where
    (==) (TV _ n0) (TV _ n1) = n0==n1; (==) (TP _ t0) (TP _ t1) = t0==t1
    (==) (TT _ t0) (TT _ t1) = t0==t1; (==) (SV _ v0) (SV _ v1) = v0==v1
    (==) (TC _ n0) (TC _ n1) = n0==n1; (==) (TI _ t0) (TI _ t1) = t0==t1
    (==) (TA _ t0 t1) (TA _ t0' t1') = t0==t0'&&t1==t1'
    (==) (QT _ ts0) (QT _ ts1) = ts0==ts1; (==) (Σ _ w0) (Σ _ w1) = w0==w1
    (==) (Ρ _ n0 σ0 ρ0) (Ρ _ n1 σ1 ρ1) = n0==n1&&σ0==σ1&&ρ0==ρ1
    (==) UU{} _ = undefined; (==) _ UU{} = undefined
    (==) _ _ = False

instance Ord (T a) where
    compare (TV _ n0) (TV _ n1) = compare n0 n1; compare (TP _ t0) (TP _ t1) = compare t0 t1
    compare (TT _ t0) (TT _ t1) = compare t0 t1; compare (SV _ n0) (SV _ n1) = compare n0 n1
    compare (TC _ n0) (TC _ n1) = compare n0 n1; compare (TI _ t0) (TI _ t1) = compare t0 t1
    compare (QT _ t0) (QT _ t1) = compare t0 t1; compare (Σ _ as) (Σ _ as') = compare as as'
    compare (TA _ t0 t0') (TA _ t1 t1') = compare [t0,t1] [t0',t1']
    compare (Ρ _ n0 σ0 ρ0) (Ρ _ n1 σ1 ρ1) = case compare n0 n1 of EQ -> case compare σ0 σ1 of {EQ -> compare ρ0 ρ1; o -> o}; o -> o
    compare UU{} _ = undefined; compare _ UU{} = undefined
    compare TV{} _ = GT; compare _ TV{} = LT; compare TP{} _ = GT; compare _ TP{} = LT
    compare TT{} _ = GT; compare _ TT{} = LT; compare SV{} _ = GT; compare _ SV{} = LT
    compare TC{} _ = GT; compare _ TC{} = LT; compare Ρ{} _ = GT; compare _ Ρ{} = LT
    compare TA{} _ = GT; compare _ TA{} = LT; compare Σ{} _ = GT; compare _ Σ{} = LT
    compare TI{} _ = GT; compare _ TI{} = LT

data D a b = TD a (Nm a) [Nm a] (T a) | F b (Nm b) (TS a) (ASeq b)

anD :: D a (TS b) -> Doc ann
anD (F _ n t as) = pretty n <+> align (":" <+> p0 t <#> ":=" <+> brackets (aT as))
anD d@TD{}       = pretty d

instance Pretty (D a b) where
    pretty (F _ n t as)  = pretty n <+> align (":" <+> p0 t <#> ":=" <+> brackets (pASeq as))
    pretty (TD _ n vs t) = "type" <+> pretty n <> (if null vs then mempty else space <> hsep (pretty<$>vs)) <+> "=" <+> p0 t <> ";"

am :: M a (TS b) -> Doc ann
am (M _ ds) = concatWith (<##>) (anD<$>ds) <> hardline

data M a b = M [MN] [D a b]

instance Pretty (M a b) where
    pretty (M [] ds) = pDs ds
    pretty (M ms ds) = concatWith (<#>) (pI<$>ms) <##> pDs ds

pDs ds = "%-" <##> concatWith (<##>) (pretty<$>ds) <> hardline
pI n = "@i" <+> pretty n

instance P0 (TS a) where
    p0 (TS [] tr) = "--" <+> pSeq tr; p0 (TS tl []) = pSeq tl <+> "--"
    p0 (TS tl tr) = pSeq tl <+> "--" <+> pSeq tr

instance Pretty (TS a) where pretty=p0.ppt
instance Show (TS a) where show=show.pretty

-- §16.6 Hutton
tunroll :: T a -> [T a]
tunroll = flip tg [] where tg (TA _ t t') s = tg t (t':s)
                           tg t s           = t:s

instance P0 (T a) where
    p0 (TV _ n) = pretty n; p0 (TP _ pty) = pretty pty; p0 (TC _ n) = pretty n
    p0 (QT _ ts) = brackets (p0 ts); p0 (SV _ n) = pretty n
    p0 (TT _ n) = pretty n; p0 (Σ _ ts) = pΣ (pNM (hsep.(\(u,tsϵ) -> map p0 tsϵ++[pretty u])) ts)
    p0 t@TA{} | (h:a) <- tunroll t = p0 h <> tupled (p0<$>a)
    p0 (TI _ t) = p0 t <+> "⁻¹"
    p0 (Ρ _ n σ s) | Nm.null σ = pρ n (pa s)
    p0 (Ρ _ n σ s) | S.null s = pρ n (pΡ σ)
    p0 (Ρ _ n σ s) = pρ n (pΡ σ++(pipe:(pa s)))
    p0 (UU _ t) = concatWith (\x y -> x <+> "∪" <+> y) (p0<$>t)

pρ n [] = pretty n
pρ n b  = parens (pretty n <+> "⊃" <+> braces (mconcat b))

pa :: S.Set (T a) -> [Doc ann]
pa = punctuate ", ".map p0.S.toList

pΣ = group.align.braces.fillSep.punctuate (flatAlt " ⊕" " ⊕")

pΡ :: NmMap (TSeq a) -> [Doc ann]
pΡ = punctuate ", ".pNM (\(n,t) -> pretty n <> case t of {[] -> mempty; _ -> ":" <+> hsep (map p0 t)})

pNM g = map g . nmlist

instance Pretty (T a) where pretty=p0.ppt
instance Show (T a) where show=show.pretty

instance Pretty (A a) where
    pretty (B _ b) = pretty b; pretty (Q _ as) = brackets (pASeq as)
    pretty (L _ l) = pretty l; pretty (Pat _ as) = group (braces (align (pA (map pASeq (aas as)))))
    pretty (C _ n) = pretty n; pretty (V _ n) = pretty n; pretty (Inv _ a) = pretty a <> "⁻¹"

pA = concatWith (\x y -> x <+> "&" <> line <> y)

pSeq :: P0 a => [a] -> Doc ann
pSeq = hsep.map p0

pASeq :: ASeq a -> Doc ann
pASeq = hsep.map pretty.aas

instance Show (A a) where show=show.pretty
