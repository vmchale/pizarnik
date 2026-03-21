module A ( A (..)
         , B (..)
         , L (..)
         , Prim (..)
         , T (..), TS (..), ʙ
         , TSeq
         , D (..)
         , M (..)
         , SL (..), ASeq
         , (--:)
         , faseq
         , PT (..)
         , ppt, psv
         , tun
         , am
         , tTS
         , pASeq
         ) where

import           Control.Monad.Trans.State.Strict (State, evalState, get, modify, put)
import           Data.Bifunctor                   (Bifunctor (bimap, second))
import           Data.Functor                     (($>))
import qualified Data.IntMap                      as IM
import qualified Data.Set                         as S
import qualified Data.Text                        as T
import           G
import           Nm
import           Nm.Map                           (NmMap, nmlist)
import qualified Nm.Map                           as Nm
import           Pr
import           Prettyprinter                    (Doc, Pretty (..), align, braces, brackets, concatWith, dquotes, fillSep, group, hardline, hsep, parens, punctuate, space, tupled,
                                                   (<+>))

infixl 9 <:>
infixr 0 --:

data B = Dip | Dup | Un
       | Plus | Minus | Mul | Div
       | Rem | Eq | Gt | Lt
       | Ap | Cat

instance Pretty B where
    pretty Dip = "dip"; pretty Dup = "dup"; pretty Un = "_"
    pretty Plus = "+"; pretty Minus = "-"; pretty Mul = "*"; pretty Div = "%"
    pretty Eq = "="; pretty Gt = ">"; pretty Lt = "<"; pretty Rem = "rem"
    pretty Ap = "$"; pretty Cat = "strcat"

data L = I !Integer | R !Double | Str !T.Text | S !Sn

instance Pretty L where
    pretty (I i) = pretty i; pretty (R x) = pretty x
    pretty (S p) = pretty p; pretty (Str s) = dquotes (pretty s)

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

data A a = B { aL :: a, builtin :: !B } | Q { aL :: a, aqs :: ASeq a }
         | L { aL :: a, lita :: L } | C { aL :: a, tagn :: Nm a }
         | V { aL :: a, fn :: Nm a } | Inv { aL :: a, inva :: A a }
         | Pat { aL :: a, arms :: SL a (ASeq a) } | Ca { aL :: a, acs :: [A a] }

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

instance Functor A where
    fmap f (B x b) = B (f x) b; fmap f (L x l) = L (f x) l
    fmap f (C x n) = C (f x) (f<$>n); fmap f (V x n) = V (f x) (f<$>n)
    fmap f (Q x as) = Q (f x) (faseq f as)
    fmap f (Pat x (SL y ys)) = Pat (f x) (SL (f y) (map (faseq f) ys))
    fmap f (Inv x a) = Inv (f x) (f<$>a)

data Prim = Int | StrT deriving Eq

instance Pretty Prim where pretty Int="Int"; pretty StrT="Str"

data TS a = TS { tlefts, trights :: TSeq a }
type TSeq a = [T a]

-- TODO: :-- at data level
(--:) = TS

instance Functor TS where fmap f (TS l r) = TS (map (fmap f) l) (map (fmap f) r)

tTS f (TS l r) = TS <$> traverse f l <*> traverse f r

data T a = TV { tL :: a, tvar :: Nm a } | TP { tL :: a, primty :: Prim }
         | QT { tL :: a, tq :: TS a } | SV { tL :: a, tSs :: Nm a }
         | TT { tL :: a, tagty :: Nm a } | Σ { tL :: a, tΣ :: NmMap (TSeq a) }
         | TA { tL :: a, tA0, tA1 :: T a } | TC { tL :: a, tCon :: Nm a }
         | Ρ { tL :: a, tvar :: Nm a, tΡ :: NmMap (TSeq a) }
         | UU { tL :: a, uts :: [T a] }

instance Functor T where
    fmap f (TT x n) = TT (f x) (f<$>n); fmap f (TV x n) = TV (f x) (f<$>n)
    fmap f (SV x n) = SV (f x) (f<$>n); fmap f (TC x n) = TC (f x) (f<$>n)
    fmap f (TP x l) = TP (f x) l
    fmap f (Σ x σ)   = Σ (f x) (map (fmap f)<$>σ)
    fmap f (Ρ x n σ) = Ρ (f x) (f<$>n) (map (fmap f)<$>σ)
    fmap f (TA x t₀ t₁) = TA (f x) (f<$>t₀) (f<$>t₁)
    fmap f (QT x ts)    = QT (f x) (fmap f ts)
    fmap f (UU x ts)    = UU (f x) (map (fmap f) ts)

psv=fr sr

instance PT (T a) where
    pp t@(TP{};TT{};TC{}) = pure t
    pp (Ρ x n σ)          = Ρ x n <$> traverse (traverse pp) σ
    pp (TV x n)           = TV x <$> fr vr n
    pp (SV x n)           = SV x <$> fr sr n
    pp (TA x t₀ t₁)       = TA x <$> pp t₀ <*> pp t₁
    pp (QT x (TS l r))    = QT x <$> (TS <$> traverse pp l <*> traverse pp r)
    pp (UU x ts)          = UU x <$> traverse pp ts
    pp (Σ x a)            = Σ x <$> traverse (traverse pp) a

instance PT (TS a) where pp (TS l r) = TS <$> traverse pp l <*> traverse pp r

ʙ :: a -> T a
ʙ x = Σ x (Nm.fromDistinctAscList [(true x, []), (false x, [])])

-- Hutton §16.6
tun :: T a -> Maybe (T a, [T a])
tun = g [] where g s th@TC{}      = Just (th, s)
                 g s (TA _ t0 t1) = g (t1:s) t0
                 g _ _            = Nothing

data D a b = TD a (Nm a) [Nm a] (T a) | F b (Nm b) (TS a) (ASeq b)

instance Functor (D a) where fmap=second

instance Bifunctor D where
    bimap f _ (TD x n v t) = TD (f x) (fmap f n) (map (fmap f) v) (fmap f t)
    bimap f g (F x n t as) = F (g x) (fmap g n) (fmap f t) (faseq g as)

anD :: D a (TS b) -> Doc ann
anD (F _ n t as) = pretty n <+> align (":" <+> p0 t <#> ":=" <+> brackets (aT as))
anD d@TD{}       = pretty d

instance Pretty (D a b) where
    pretty (F _ n t as)  = pretty n <+> align (":" <+> p0 t <#> ":=" <+> brackets (pASeq as))
    pretty (TD _ n vs t) = "type" <+> pretty n <> (if null vs then mempty else space <> hsep (pretty<$>vs)) <+> "=" <+> p0 t <> ";"

am :: M a (TS b) -> Doc ann
am (M _ ds) = concatWith (<##>) (anD<$>ds) <> hardline

data M a b = M [MN a] [D a b]

instance Functor (M a) where fmap=second

instance Bifunctor M where
    bimap f g (M is d) = M (map (f<$>) is) (map (bimap f g) d)

instance Pretty (M a b) where
    pretty (M [] ds) = pDs ds
    pretty (M ms ds) = concatWith (<#>) (pI<$>ms) <##> pDs ds

pDs ds = concatWith (<##>) (pretty<$>ds) <> hardline
pI n = "@" <> pretty n

instance P0 (TS a) where
    p0 (TS [] tr) = "--" <+> pSeq tr; p0 (TS tl []) = pSeq tl <+> "--"
    p0 (TS tl tr) = pSeq tl <.> "--" <+> pSeq tr

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
    p0 t@TA{} | (h:a) <- tunroll t = p0 h <> parens (hsep (p0<$>a))
    p0 (Ρ _ n σ) = pρ n (pΡ σ)
    p0 (UU _ t) = concatWith (\x y -> x <+> "∪" <+> y) (p0<$>t)

pρ n [] = pretty n
pρ n b  = parens (pretty n <+> "⊃" <+> braces (mconcat b))

pΣ = group.align.braces.fillSep.punctuate " ⊕"

pΡ :: NmMap (TSeq a) -> [Doc ann]
pΡ = punctuate ", ".pNM (\(n,t) -> pretty n <> case t of {[] -> mempty; _ -> ":" <+> hsep (map p0 t)})

pNM g = map g . nmlist

instance Pretty (T a) where pretty=p0.ppt
instance Show (T a) where show=show.pretty

instance Pretty (A a) where
    pretty (B _ b) = pretty b; pretty (Q _ as) = brackets (pASeq as)
    pretty (L _ l) = pretty l; pretty (Pat _ as) = group (braces (align (pA (map pASeq (aas as)))))
    pretty (C _ n) = pretty n; pretty (V _ n) = pretty n; pretty (Inv _ a) = pretty a <> "⁻¹"
    pretty (Ca _ as) = braces (hsep (pretty<$>reverse as))

pA = concatWith (\x y -> x <> softline <> "&" <+> y)

pSeq :: P0 a => [a] -> Doc ann
pSeq = hsep.map p0

pASeq :: ASeq a -> Doc ann
pASeq = hsep.map pretty.aas

instance Show (A a) where show=show.pretty
