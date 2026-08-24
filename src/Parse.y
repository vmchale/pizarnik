{

    module Parse ( pA
                 , pM
                 , pAtoms
                 , ParseE
                 ) where

import A
import Control.Arrow ((&&&))
import Control.Exception (Exception)
import Control.Monad.Trans.Except (ExceptT, runExceptT, throwE)
import Control.Monad.Trans.Class (lift)
import Data.Bifunctor (bimap, second)
import qualified Data.ByteString.Lazy as BSL
import Data.Functor (($>))
import qualified Data.IntMap as IM
import qualified Data.Text as T
import Data.Typeable (Typeable)
import G
import L
import Loc
import Nm hiding (loc)
import qualified Nm
import Nm.Map (NmMap)
import qualified Nm.Map as Nm
import Prettyprinter (Pretty (..), (<+>), concatWith, squotes)

}

%name parseM M
%name parseASeq ASeq
%tokentype { Tok AlexPosn }
%error { parseErr }
%error.expected
%monad { Parse } { (>>=) } { pure }
%lexer { lift alexMonadScan >>= } { EOF _ }

%token

    colon { TokS $$ Colon }
    sig { TokS $$ Sig }
    defEq { TokS $$ DefEq }
    lbracket { TokS $$ LBracket }
    rbracket { TokS $$ RBracket }
    lparen { TokS $$ LParen }
    rparen { TokS $$ RParen }
    lbrace { TokS $$ LBrace }
    rbrace { TokS $$ RBrace }
    semicolon { TokS $$ Semicolon }
    comma { TokS $$ Comma }
    amp { TokS $$ Amp }
    un { TokS $$ Up }
    eq { TokS $$ L.Eq }
    gt { TokS $$ L.Gt }
    lt { TokS $$ L.Lt }
    oplus { TokS $$ DSum }
    inv { TokS $$ PInv }
    und { TokS $$ Under }

    plus { TokS $$ Add }
    minus { TokS $$ Sub }
    mul { TokS $$ L.Mul }
    div { TokS $$ L.Div }
    idiv { TokS $$ L.IDiv }

    ilit { $$@(TokI _ _ _) }

    stringTy { TokB $$ L.String }
    intTy { TokB $$ L.Int }
    boolTy { TokB $$ L.Bool }

    dip { TokB $$ L.Dip }
    dup { TokB $$ L.Dup }
    rem { TokB $$ L.Rem }
    doll { TokB $$ Doll }
    cat { TokB $$ L.Cat }

    str { $$@(TokStr _ _) }

    name { TokN _ $$ }
    tyname { TokTN _ $$ }
    sv { TokSV _ $$ }
    modname { TokMN _ $$ }
    tag { TokT _ $$ }

    i { TokKw $$ L.I }
    type { TokKw $$ Ty }

    com { TokCom _ $$ }

%%

many(p)
    : many(p) p { $2 : $1 }
    | { [] }

some(p)
    : some(p) p { $2 : $1 }
    | p { [$1] }

seq(p,q) : p q { $2 }

sepBy(p,q)
    : sepBy(p,q) q p { $3 : $1 }
    | p { [$1] }

sepTup(p,q)
    : sepTup(p,q) q p { $3 : $1 }
    | p q p { [$3, $1] }

brackets(p) : lbracket p rbracket { ($1, $2) }
braces(p) : lbrace p rbrace { ($1, $2) }

Arm :: { (Nm AlexPosn, TSeq AlexPosn) }
    : some(T) {% case head $1 of {TT _ n -> pure (n, reverse (tail $1)); _ -> throwE.AnonymousArm =<< lift get_pos } }

TS :: { TS AlexPosn }
   : many(T) sig many(T) { TS (reverse $1) (reverse $3) }

T :: { T AlexPosn }
  : name { TV (Nm.loc $1) $1 }
  | sv { SV (Nm.loc $1) $1 }
  | tyname { TC (Nm.loc $1) $1 }
  | intTy { TP $1 A.Int }
  | boolTy { ʙ $1 }
  | stringTy { TP $1 A.StrT }
  | tag { TT (Nm.loc $1) $1 }
  | brackets(TS) { uncurry QT $1 }
  | T lparen sepBy(T,comma) rparen { roll $1 (reverse $3) }
  | braces(sepBy(Arm,oplus)) { uncurry Σ (σparsed (snd $1)) }
  | T un T { UU $2 [$1,$3] }

Cyc :: { (AlexPosn, [Int]) }
    : lparen ilit rparen { ($1, digits $2) }

A :: { A AlexPosn }
  : dip { B $1 A.Dip }
  | dup { B $1 A.Dup } | und { B $1 Un }
  | plus { B $1 Plus } | minus { B $1 Minus }
  | mul { B $1 A.Mul } | idiv { B $1 A.Div }
  | eq { B $1 A.Eq }  | gt { B $1 A.Gt }
  | lt { B $1 A.Lt } | rem { B $1 A.Rem }
  | doll { B $1 Ap } | cat { B $1 A.Cat }
  | name { V (Nm.loc $1) $1 }
  | tag inv { Inv (Nm.loc $1) (C (Nm.loc $1) $1) }
  | tag { C (Nm.loc $1) $1 }
  | brackets(many(A)) { Q (fst $1) (SL (fst $1) (reverse (snd $1))) }
  | braces(sepBy(some(A),amp)) { Pat (fst $1) (SL (fst $1) (reverse (map (\as -> let as'=reverse as in SL (aL$head as') as') (snd $1)))) }
  | ilit { L (loc $1) (A.I (int $1)) }
  | str { L (loc $1) (Str (str $1)) }
  | some(Cyc) { L (fst $ head $1) (S $ iperm (map snd $1)) }

ASeq :: { ASeq AlexPosn }
     : many(A) {% fmap SL (lift get_pos) <*> pure (reverse $1) }

DC :: { D Ann Ann }
   : D { bimap (\x -> Ann x Nothing) (\x -> Ann x Nothing) $1 }

D :: { D AlexPosn AlexPosn }
  : name colon TS defEq brackets(many(A)) { F $2 $1 $3 (SL $4 (reverse (snd $5))) }
  | type tyname many(name) eq T semicolon { TD $1 $2 (reverse $3) $5 }

Imp :: { MN Ann }
    : i modname { (unc $2) }
    | com i modname { let l=ann $3 in $3 { ann = Ann l (Just $1) } }
    | i com modname { let l=ann $3 in $3 { ann = Ann l (Just $2) } }

M :: { M AlexPosn AlexPosn }
  : many(seq(i,modname)) many(D) { M (reverse $1) (reverse $2) }

{

data Ann = Ann AlexPosn (Maybe T.Text)

unc :: Functor f => f AlexPosn -> f Ann
unc = fmap (\loc -> Ann loc Nothing)

σparsed = (locArms &&& mkΣ).reverse

locArms :: [(Nm a, TSeq a)] -> a
locArms = Nm.loc . fst . head

mkΣ = Nm.fromList

iperm :: [[Int]] -> Sn
iperm cs =
    let xn=sn (maximum (concat cs))
    in z xn cs
  where
    zy n@(i:_) = g n where
        g :: [Int] -> Sn -> Sn
        g [j] = setIx j i
        g (k:js@(j:_)) = g js.setIx k j

    z s (c:cs) = z (zy c s) cs; z s [] = s

roll :: T a -> [T a] -> T a
roll t []      = t
roll t (t':ts) = roll (TA (tL t) t t') ts

parseErr :: Tok AlexPosn -> [String] -> Parse a
parseErr t = throwE.Unexpected t

data ParseE a = Unexpected !(Tok a) [String] | LexErr String | AnonymousArm !a deriving Functor

instance Pretty a => Pretty (ParseE a) where
    pretty (Unexpected t v) = ep (loc t) ("Unexpected" <+> pretty t <> "." <+> "Expected one of" <+> concatWith (\x y -> x <> ", " <> y) (squotes.pretty<$>v))
    pretty (LexErr s)       = pretty (T.pack s)
    pretty (AnonymousArm l) = ep l "Sum type variants must be terminated by a tag"

ep l = ((pretty l <> ":") <+>)

instance Pretty a => Show (ParseE a) where show=show.pretty

instance (Pretty a, Typeable a) => Exception (ParseE a)

type Parse = ExceptT (ParseE AlexPosn) Alex

loca :: FilePath -> Either (ParseE AlexPosn) (x, M AlexPosn AlexPosn) -> Either (ParseE Loc) (x, M Loc Loc)
loca fp = bimap (fmap gr) (second (bimap gr gr))
  where
    gr (AlexPn _ l c) = Loc fp l c

pM fp = (loca fp .) . runParseSt parseM 0
pAtoms = runParseSt parseASeq 0

pA fp = pM fp alexInitUserState

runParseSt :: Parse a -> Int -> AlexUserState -> BSL.ByteString -> Either (ParseE AlexPosn) (AlexUserState, a)
runParseSt parser scd u bs = liftErr $ withAlexSt bs scd u (runExceptT parser)

liftErr :: Either String (b, Either (ParseE e) c) -> Either (ParseE e) (b, c)
liftErr (Left err)            = Left (LexErr err)
liftErr (Right (_, Left err)) = Left err
liftErr (Right (i, Right x))  = Right (i, x)

}
