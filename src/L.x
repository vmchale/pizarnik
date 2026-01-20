{
    module L ( AlexUserState
             , AlexPosn (..)
             , Alex (..)
             , Tok (..)
             , Sym (..)
             , Kw (..)
             , B (..)
             , alexMonadScan
             , alexInitUserState
             , withAlexSt
             , nMIdent
             -- * Lexer states
             , get_pos
             ) where

import Data.Bifunctor (first)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as ASCII
import qualified Data.ByteString.Lazy as BSL
import Data.Functor (($>))
import qualified Data.IntMap as IM
import qualified Data.List.NonEmpty as NE
import qualified Data.Map as M
import qualified Data.Text as T
import Data.Text.Encoding (decodeUtf8)
import Nm
import Pr (sq)
import Prettyprinter (Pretty (..), (<+>), dquotes)

}

%wrapper "monadUserState-bytestring"

$digit = [0-9]

$lowercase = [a-z]
$uppercase = [A-Z]

$latin = [$lowercase $uppercase]
$follow_char = [$latin $digit \_\-]

@dir = ($follow_char+ \/)

@name = $lowercase $follow_char*
@tyname = $uppercase $follow_char*
@tag = $latin [$latin $digit]*
@modname = @dir* $follow_char+

tokens :-

    <0,imp> {
        $white+                 ;
        "#".*                   ;
    }

    <imp> {
        @modname                { tok (\p s -> TokMN p <$> aus (nMIdent (mkText s))) `andBegin` 0 }
    }

    <0> {

        "@"                     { kw I `andBegin` imp }

        $digit+                 { tok (\p s -> alex $ TokI p (readDigits s) (iperm s)) }

        "+"                     { sym Add }
        "-"                     { sym Sub }
        "*"                     { sym Mul }
        "/"                     { sym Div }
        "%"                     { sym IDiv }

        :                       { sym Colon }
        "["                     { sym LBracket }
        "]"                     { sym RBracket }
        "("                     { sym LParen }
        ")"                     { sym RParen }
        ";"                     { sym Semicolon }
        ","                     { sym Comma }
        "{"                     { sym LBrace }
        "}"                     { sym RBrace }
        &                       { sym Amp }
        :=                      { sym DefEq }
        ≔                       { sym DefEq }
        "--"                    { sym Sig }
        ⊕                       { sym DSum }
        "+."                    { sym DSum }
        ∪                       { sym Up }
        ⁻¹                      { sym PInv }
        \^                      { sym PInv }
        =                       { sym Eq }
        _                       { sym Under }
        "<"                     { sym Lt }
        ">"                     { sym Gt }

        dip                     { builtin Dip }
        dup                     { builtin Dup }
        rem                     { builtin Rem }
        strcat                  { builtin Cat }
        "$"                     { builtin Doll }

        type                    { kw Ty }

        Int                     { builtin Int }
        Bool                    { builtin Bool }
        Str                     { builtin String }

        True                    { tok (\p _ -> alex $ TokT p (true p)) }
        False                   { tok (\p _ -> alex $ TokT p (false p)) }

        \" [^\"]* \"            { tok (\p s -> alex $ TokStr p (T.tail$T.init$mkText s)) }

        @name                   { tok (\p s -> TokN p <$> nIdent p (mkText s)) }
        @tyname                 { tok (\p s -> TokTN p <$> nIdent p (mkText s)) }
        '@tyname                { tok (\p s -> TokSV p <$> nIdent p (mkText s)) }
        "`"@tag                 { tok (\p s -> TokT p <$> nIdent p (mkText s)) }

    }

{

mkText :: BSL.ByteString -> T.Text
mkText = decodeUtf8 . BSL.toStrict

iperm :: BSL.ByteString -> [Int]
iperm = map (fromIntegral.(subtract 48)).BSL.unpack

readDigits :: BSL.ByteString -> Integer
readDigits = BSL.foldl' (\seed x -> 10*seed + fromIntegral (x-48)) 0

alex :: a -> Alex a
alex = pure

tok f (p,_,s,_) l = f p (BSL.take l s)

constructor c t = tok (\p _ -> alex (c p t))

sym = constructor TokS; kw = constructor TokKw
builtin = constructor TokB

type AlexUserState = (Int, M.Map T.Text Int, IM.IntMap (Nm AlexPosn), IM.IntMap MN)

alexInitUserState :: AlexUserState
alexInitUserState = (0, mempty, mempty, mempty)

aus :: (AlexUserState -> (AlexUserState, a)) -> Alex a
aus f = Alex (Right . (\s -> let (s', x) = f (alex_ust s) in (s { alex_ust = s' }, x)))

get_pos :: Alex AlexPosn
get_pos = Alex $ \st -> Right (st, alex_pos st)

nMIdent :: T.Text -> AlexUserState -> (AlexUserState, MN)
nMIdent t = \st@(max', ns, us, ums) ->
    case M.lookup t ns of
        Just i -> (st, MN d (U i))
        Nothing -> let i=max'+1; nM=MN d (U i)
                   in ((i, M.insert t i ns, us, IM.insert i nM ums), nM)
    where d = NE.fromList (T.splitOn "/" t)

nIdent :: AlexPosn -> T.Text -> Alex (Nm AlexPosn)
nIdent pos t = aus $ \pre@(max', ns, us, ums) ->
    case M.lookup t ns of
        Just i  -> (pre, Nm t (U i) pos)
        Nothing -> let i = max'+1; nNm = Nm t (U i) pos
                   in ((i, M.insert t i ns, IM.insert i nNm us, ums), nNm)

alexEOF = EOF <$> get_pos

instance Pretty AlexPosn where
    pretty (AlexPn _ l col) = pretty l <> ":" <> pretty col

data Sym = Add | Sub | Mul | Div | IDiv
         | Colon | LBracket | RBracket
         | DefEq | Sig | DSum | Up | PInv
         | Amp | Semicolon | LBrace | RBrace
         | Eq | Gt | Lt | Comma | Under
         | LParen | RParen

instance Pretty Sym where
    pretty Add = "+"; pretty Sub = "-"; pretty Mul = "*"; pretty Div = "/"
    pretty Colon = ":"; pretty LBracket = "["; pretty RBracket = "]"
    pretty DefEq = ":="; pretty Sig = "--"; pretty DSum = "⊕"; pretty Up = "∪"
    pretty PInv = "⁻¹"; pretty Amp = "&"; pretty Semicolon = ";"
    pretty LBrace = "{"; pretty RBrace = "}"; pretty Eq = "="
    pretty LParen = "("; pretty RParen = ")"
    pretty Comma = ","; pretty Under = "_"; pretty Gt = ">"
    pretty Lt = "<"; pretty IDiv = "%"

data Kw = I | Ty

instance Pretty Kw where pretty I="@"; pretty Ty="type"

data B = Dup | Dip | Doll | Rem
       | Int | Bool | String | Cat

instance Pretty B where
    pretty Dup = "dup"; pretty Dip = "dip"; pretty Doll = "$"
    pretty Int = "Int"; pretty Bool = "Bool"; pretty String = "Str"
    pretty Rem = "rem"; pretty Cat = "strcat"

data Tok a = EOF { loc :: a }
           | TokI { loc :: a, int :: Integer, digits :: [Int] }
           | TokS { loc :: a, tokSym :: !Sym }
           | TokN { loc :: a, name :: !(Nm AlexPosn) }
           | TokB { loc :: a, tokB :: !B }
           | TokT { loc :: a, tag :: !(Nm AlexPosn) }
           | TokTN { loc :: a, tyname :: !(Nm AlexPosn) }
           | TokSV { loc :: a, svn :: !(Nm AlexPosn) }
           | TokMN { loc :: a, modname :: !MN }
           | TokKw { loc :: a, tokKw :: !Kw }
           | TokStr { loc :: a, str :: T.Text }
           deriving Functor

instance Pretty (Tok a) where
    pretty EOF{}        = "(eof)"
    pretty (TokI _ i _) = pretty i
    pretty (TokS _ s)   = pretty s
    pretty (TokN _ n)   = "identifier" <+> sq n
    pretty (TokMN _ m)  = "module" <+> sq m
    pretty (TokTN _ tn) = pretty tn
    pretty (TokSV _ sn) = pretty sn
    pretty (TokB _ b)   = "builtin" <+> sq b
    pretty (TokT _ t)   = pretty t
    pretty (TokKw _ k)  = "keyword" <+> sq k
    pretty (TokStr _ s) = dquotes (pretty s)

withAlexSt :: BSL.ByteString -> Int -> AlexUserState -> Alex a -> Either String (AlexUserState, a)
withAlexSt inp scd ust (Alex f) = first alex_ust <$> f
    (AlexState { alex_bpos = 0
               , alex_pos = alexStartPos
               , alex_inp = inp
               , alex_chr = '\n'
               , alex_ust = ust
               , alex_scd = scd
               })

}
