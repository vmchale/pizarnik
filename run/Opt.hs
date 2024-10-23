module Main (main) where

import qualified Data.ByteString.Lazy      as BSL
import           Data.Functor              (void)
import           Options.Applicative       (HasCompleter, Mod, Parser, ParserInfo, argument, bashCompleter, command, completer, execParser, fullDesc, header, help, helper,
                                            hsubparser, info, metavar, progDesc, str)
import           P
import           Prettyprinter             (Pretty (pretty), defaultLayoutOptions, hardline, layoutPretty)
import           Prettyprinter.Render.Text (renderIO)
import           System.Exit               (exitFailure)
import           System.IO                 (stderr, stdout)

data Cmd = TC !FilePath | An !FilePath | Fmt !FilePath

pComplete :: HasCompleter f => Mod f a
pComplete = completer . bashCompleter $ "file -X '!*.piz -o plusdirs"

cmd :: Parser Cmd
cmd = hsubparser
    (command "tc" (info tcP (progDesc "Type-check"))
    <> command "an" (info anP (progDesc "Display type annotations"))
    <> command "fmt" (info fmtP (progDesc "Format")))
  where
    tcP = TC<$>src; fmtP=Fmt<$>src; anP=An<$>src

src :: Parser FilePath
src = argument str
    (metavar "FILE"
    <> help "Source file"
    <> pComplete)

wrapper :: ParserInfo Cmd
wrapper = info (helper <*> cmd)
    (fullDesc
    <> progDesc "Pizarnik formatter and type checker"
    <> header "pc - Pizarnik Language")

main = run =<< execParser wrapper

run :: Cmd -> IO ()
run (Fmt fp) = do {contents <- BSL.readFile fp; renderIO stdout =<< fIO (fmt contents)}
run (TC fp)  = do {res <- void <$> tMs ["."] fp; fIO res}

fIO :: Pretty e => Either e a -> IO a
fIO (Right x)  = pure x
fIO (Left err) = renderIO stderr (epopts err) *> exitFailure
  where
    epopts = layoutPretty defaultLayoutOptions . (<>hardline) . pretty
