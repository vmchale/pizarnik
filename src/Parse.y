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
import qualified Data.ByteString.Lazy as BSL
import Data.Functor (($>))
import qualified Data.IntMap as IM
import qualified Data.Text as T
import G
import L
import Nm hiding (loc)
import qualified Nm
import Nm.Map (NmMap)
import qualified Nm.Map as Nm
import Prettyprinter (Pretty (..), (<+>), concatWith, squotes)

}

%name parseM M
%name parseASeq ASeq
%tokentype { Tok }
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

    str { $$@(TokStr _ _) }

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
  | stringTy { TP $1 A.String }
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
  | doll { B $1 Ap }
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

D :: { D AlexPosn AlexPosn }
  : name colon TS defEq brackets(many(A)) { F $2 $1 $3 (SL $4 (reverse (snd $5))) }
  | type tyname many(name) eq T semicolon { TD $1 $2 (reverse $3) $5 }

M :: { M AlexPosn AlexPosn }
  : many(seq(i,modname)) many(D) { M (reverse $1) (reverse $2) }

{

σparsed = (locArms &&& mkΣ).reverse

locArms :: [(Nm a, TSeq a)] -> a
locArms = Nm.loc . fst . head

mkΣ = Nm.fromList

iperm :: [[Int]] -> Sn
iperm cs =
    let xn=sn (maximum (concat cs))
    in thread (map zy cs) xn
  where
    zy n@(i:_) = g n where
        g :: [Int] -> Sn -> Sn
        g [j] = setIx j i
        g (k:js@(j:_)) = g js.setIx k j

    thread=foldr (.) id

roll :: T a -> [T a] -> T a
roll t []      = t
roll t (t':ts) = roll (TA (tL t) t t') ts

parseErr :: Tok -> [String] -> Parse a
parseErr t = throwE.Unexpected t

data ParseE = Unexpected !Tok [String] | LexErr String | AnonymousArm !AlexPosn

instance Pretty ParseE where
    pretty (Unexpected t v) = pretty (loc t) <+> "Unexpected" <+> pretty t <> "." <+> "Expected one of" <+> concatWith (\x y -> x <> ", " <> y) (squotes.pretty<$>v)
    pretty (LexErr s)       = pretty (T.pack s)
    pretty (AnonymousArm l) = pretty l <+> "Sum type variants must be terminated by a tag"

instance Show ParseE where show=show.pretty

instance Exception ParseE

type Parse = ExceptT ParseE Alex

pM = runParseSt parseM 0
pAtoms = runParseSt parseASeq 0

pA = pM alexInitUserState

runParseSt :: Parse a -> Int -> AlexUserState -> BSL.ByteString -> Either ParseE (AlexUserState, a)
runParseSt parser scd u bs = liftErr $ withAlexSt bs scd u (runExceptT parser)

liftErr :: Either String (b, Either ParseE c) -> Either ParseE (b, c)
liftErr (Left err)            = Left (LexErr err)
liftErr (Right (_, Left err)) = Left err
liftErr (Right (i, Right x))  = Right (i, x)

}
