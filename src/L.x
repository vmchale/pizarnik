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
             -- * Lexer states
             , postImp
             , get_pos
             ) where

import Control.Arrow ((&&&))
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
import Prettyprinter (Pretty (..), (<+>))

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
@tag = $latin+
@modname = @dir* $follow_char+

tokens :-

    <0>    {

        "@i"                    { kw I }
        "%-"                    { sym IT `andBegin` postImp }

        @modname                { tok (\p s -> TokMN p <$> nMIdent (mkText s)) }

    }

    <0,postImp> {

        $white+                 ;
        "#".*                   ;
    }

    <postImp> {

        $digit+                 { tok (\p s -> alex $ TokI p (readDigits $ BSL.toStrict s)) }

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
        ⁻¹                      { sym PInv }
        =                       { sym Eq }
        _                       { sym Under }
        "<"                     { sym Lt }
        ">"                     { sym Gt }
        -- 𝟙

        dip                     { builtin Dip }
        dup                     { builtin Dup }
        swap                    { builtin Swap }
        "$"                     { builtin Doll }

        "type"                  { kw Ty }

        Int                     { builtin Int }
        Bool                    { builtin Bool }
        String                  { builtin String }

        True                    { builtin TrueTok }
        False                   { builtin FalseTok }

        @name                   { tok (\p s -> TokN p <$> nIdent p (mkText s)) }
        @tyname                 { tok (\p s -> TokTN p <$> nIdent p (mkText s)) }
        '@tyname                { tok (\p s -> TokSV p <$> nIdent p (mkText s)) }
        "`"@tag                 { tok (\p s -> TokT p <$> nIdent p (mkText s)) }
        -- ⊲
        -- ⊳

    }

{

mkText :: BSL.ByteString -> T.Text
mkText = decodeUtf8 . BSL.toStrict

readDigits :: BS.ByteString -> Integer
readDigits = ASCII.foldl' (\seed x -> 10 * seed + f x) 0
    where f '0' = 0; f '1' = 1; f '2' = 2; f '3' = 3;
          f '4' = 4; f '5' = 5; f '6' = 6; f '7' = 7;
          f '8' = 8; f '9' = 9
          f c   = error (c:" is not a valid digit!")

alex :: a -> Alex a
alex = pure

tok f (p,_,s,_) l = f p (BSL.take l s)

constructor c t = tok (\p _ -> alex (c p t))

sym = constructor TokS
builtin = constructor TokB
kw = constructor TokKw

type AlexUserState = (Int, M.Map T.Text Int, IM.IntMap (Nm AlexPosn), IM.IntMap MN)

alexInitUserState :: AlexUserState
alexInitUserState = (0, mempty, mempty, mempty)

aus :: (AlexUserState -> (AlexUserState, a)) -> Alex a
aus f = Alex (Right . mapu f)
  where mapu g s = let (s', x) = g (alex_ust s) in (s { alex_ust = s' }, x)

gets_alex :: (AlexState -> a) -> Alex a
gets_alex f = Alex (Right . (id &&& f))

get_pos :: Alex AlexPosn
get_pos = gets_alex alex_pos

nMIdent :: T.Text -> Alex MN
nMIdent t = aus $ \st@(max', ns, us, ums) ->
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
         | DefEq | Sig | DSum | PInv
         | Amp | Semicolon | LBrace | RBrace
         | Eq | IT | LParen | RParen
         | Comma | Under | Gt | Lt

instance Pretty Sym where
    pretty Add = "+"; pretty Sub = "-"; pretty Mul = "*"; pretty Div = "/"
    pretty Colon = ":"; pretty LBracket = "["; pretty RBracket = "]"
    pretty DefEq = ":="; pretty Sig = "--"; pretty DSum = "⊕"
    pretty PInv = "⁻¹"; pretty Amp = "&"; pretty Semicolon = ";"
    pretty LBrace = "{"; pretty RBrace = "}"; pretty Eq = "="
    pretty IT = "%-"; pretty LParen = "("; pretty RParen = ")"
    pretty Comma = ","; pretty Under = "_"; pretty Gt = ">"
    pretty Lt = "<"; pretty IDiv = "%"

data Kw = I | Ty

instance Pretty Kw where pretty I="@i"; pretty Ty="type"

data B = Dup | Dip | Swap | Doll
       | Int | Bool | String
       | TrueTok | FalseTok

instance Pretty B where
    pretty Dup = "dup"; pretty Dip = "dip"; pretty Doll = "$"
    pretty Int = "Int"; pretty Bool = "Bool"; pretty String = "String"
    pretty Swap = "swap"; pretty TrueTok = "True"; pretty FalseTok = "False"

data Tok = EOF { loc :: AlexPosn }
         | TokI { loc :: AlexPosn, int :: Integer }
         | TokS { loc :: AlexPosn, tokSym :: !Sym }
         | TokN { loc :: AlexPosn, name :: !(Nm AlexPosn) }
         | TokB { loc :: AlexPosn, tokB :: !B }
         | TokT { loc :: AlexPosn, tag :: !(Nm AlexPosn) }
         | TokTN { loc :: AlexPosn, tyname :: !(Nm AlexPosn) }
         | TokSV { loc :: AlexPosn, svn :: !(Nm AlexPosn) }
         | TokMN { loc :: AlexPosn, modname :: !MN }
         | TokKw { loc :: AlexPosn, tokKw :: !Kw }

instance Pretty Tok where
    pretty EOF{}        = "(eof)"
    pretty (TokI _ i)   = pretty i
    pretty (TokS _ s)   = pretty s
    pretty (TokN _ n)   = "identifier" <+> sq (pretty n)
    pretty (TokMN _ m)  = "module" <+> sq (pretty m)
    pretty (TokTN _ tn) = pretty tn
    pretty (TokSV _ sn) = pretty sn
    pretty (TokB _ b)   = "builtin" <+> sq (pretty b)
    pretty (TokT _ t)   = pretty t
    pretty (TokKw _ k)  = "keyword" <+> sq (pretty k)

runAlexSt :: BSL.ByteString -> Alex a -> Either String (AlexUserState, a)
runAlexSt inp = withAlexSt inp 0 alexInitUserState

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
