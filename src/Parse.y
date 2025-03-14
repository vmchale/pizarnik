{

    module Parse ( parseA
                 , pM
                 , ParseE
                 )  where

import A
import Control.Arrow ((&&&))
import Control.Exception (Exception)
import Control.Monad.Except (ExceptT, runExceptT, throwError)
import Control.Monad.Trans.Class (lift)
import qualified Data.ByteString.Lazy as BSL
import qualified Data.IntMap as IM
import qualified Data.Text as T
import L
import Nm hiding (loc)
import qualified Nm
import Nm.Map (NmMap)
import qualified Nm.Map as Nm
import Prettyprinter (Pretty (..), (<+>), concatWith, squotes)

}

%name parseM M
%tokentype { Tok }
%error { parseErr }
%error.expected
%monad { Parse } { (>>=) } { pure }
%lexer { lift alexMonadScan >>= } { EOF _ }

%token

    imp { TokS $$ IT }
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

    ilit { $$@(TokI _ _) }

    stringTy { TokB $$ L.String }
    intTy { TokB $$ L.Int }
    boolTy { TokB $$ L.Bool }

    dip { TokB $$ L.Dip }
    dup { TokB $$ L.Dup }
    swap { TokB $$ L.Swap }
    doll { TokB $$ L.Doll }

    name { TokN _ $$ }
    tyname { TokTN _ $$ }
    sv { TokSV _ $$ }
    modname { TokMN _ $$ }
    tag { TokT _ $$ }

    i { TokKw $$ L.I }
    type { TokKw $$ Ty }

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
parens(p) : lparen p rparen { $2 }

Arm :: { (Nm AlexPosn, TSeq AlexPosn) }
    : some(T) {% case head $1 of {TT _ n -> pure (n, reverse (tail $1)); _ -> throwError =<< fmap AnonymousArm (lift get_pos) } }

TDef :: { T AlexPosn }
     : braces(sepBy(Arm,oplus)) { uncurry Σ (σparsed (snd $1)) }
     | T { $1 }

TS :: { TS AlexPosn }
   : many(T) sig many(T) { TS (reverse $1) (reverse $3) }

T :: { T AlexPosn }
  : name { TV (Nm.loc $1) $1 }
  | sv { SV (Nm.loc $1) $1 }
  | tyname { TC (Nm.loc $1) $1 }
  | intTy { TP $1 A.Int }
  | boolTy { let tt=pret $1; ft=pref $1 in Σ $1 (Nm.fromList [(tt,[]), (ft,[])]) }
  | stringTy { TP $1 A.String }
  | tag { TT (Nm.loc $1) $1 }
  | lbracket TS rbracket { QT $1 $2 }
  | T parens(sepBy(T,comma)) { troll $1 (reverse $2) }
  | braces(sepBy(Arm,oplus)) { uncurry Σ (σparsed (snd $1)) }

A :: { A AlexPosn }
  : dip { B $1 A.Dip } | swap { B $1 A.Swap }
  | dup { B $1 A.Dup } | und { B $1 Un }
  | plus { B $1 Plus } | minus { B $1 Minus }
  | mul { B $1 A.Mul } | idiv { B $1 A.Div }
  | eq { B $1 A.Eq } | doll { B $1 A.Doll }
  | gt { B $1 A.Gt } | lt { B $1 A.Lt }
  | name { V (Nm.loc $1) $1 }
  | tag inv { Inv (Nm.loc $1) (C (Nm.loc $1) $1) }
  | tag { C (Nm.loc $1) $1 }
  | brackets(many(A)) { Q (fst $1) (SL (fst $1) (reverse (snd $1))) }
  | braces(sepBy(some(A),amp)) { Pat (fst $1) (SL (fst $1) (reverse (map (\as -> let as'=reverse as in SL (aL$head as') as') (snd $1)))) }
  | ilit { L (loc $1) (A.I (int $1)) }

D :: { D AlexPosn AlexPosn }
  : name colon TS defEq brackets(many(A)) { F $2 $1 $3 (SL $4 (reverse (snd $5))) }
  | type tyname many(name) eq TDef semicolon { TD $1 $2 (reverse $3) $5 }

M :: { M AlexPosn AlexPosn }
  : many(seq(i,modname)) imp many(D) { M (reverse $1) (reverse $3) }
  | many(D) { M [] (reverse $1) }

{

σparsed = (locArms &&& mkΣ).reverse

locArms :: [(Nm a, TSeq a)] -> a
locArms = Nm.loc . fst . head

mkΣ = Nm.fromList

troll :: T a -> [T a] -> T a
troll t []      = t
troll t (t':ts) = troll (TA (tL t) t t') ts

parseErr :: Tok -> [String] -> Parse a
parseErr t = throwError . Unexpected t

data ParseE = Unexpected !Tok [String] | LexErr String | AnonymousArm !AlexPosn

instance Pretty ParseE where
    pretty (Unexpected t v) = pretty (loc t) <+> "Unexpected" <+> pretty t <> "." <+> "Expected one of" <+> concatWith (\x y -> x <> ", " <> y) (squotes.pretty<$>v)
    pretty (LexErr s)       = pretty (T.pack s)
    pretty (AnonymousArm l) = pretty l <+> "Sum type variants must be terminated by a tag"

instance Show ParseE where show=show.pretty

instance Exception ParseE

type Parse = ExceptT ParseE Alex

pM = parseA 0

parseA :: Int -> AlexUserState -> BSL.ByteString -> Either ParseE (AlexUserState, M AlexPosn AlexPosn)
parseA = runParseSt parseM

runParseSt :: Parse a -> Int -> AlexUserState -> BSL.ByteString -> Either ParseE (AlexUserState, a)
runParseSt parser scd u bs = liftErr $ withAlexSt bs scd u (runExceptT parser)

liftErr :: Either String (b, Either ParseE c) -> Either ParseE (b, c)
liftErr (Left err)            = Left (LexErr err)
liftErr (Right (_, Left err)) = Left err
liftErr (Right (i, Right x))  = Right (i, x)

}
