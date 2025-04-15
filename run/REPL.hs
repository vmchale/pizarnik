module REPL ( repl ) where

import           A
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT)
import qualified Data.IntMap                      as IM
import qualified Data.Text.Lazy                   as TL
import           Data.Text.Lazy.Encoding          (encodeUtf8)
import           Data.Tree                        (Tree (Node))
import           P
import           Pr
import           Prettyprinter                    (Doc, defaultLayoutOptions, hardline, layoutSmart, pretty)
import           Prettyprinter.Render.Text        (renderIO)
import           System.Console.Haskeline         (InputT, Settings (historyFile), defaultSettings, getInputLine, runInputT)
import           System.Directory                 (getHomeDirectory)
import           System.FilePath                  ((</>))
import           System.IO                        (stdout)

repl :: IO ()
repl = runRepl loop

type Repl = InputT (StateT (S, Ctx (TS AlexPosn)) IO)

runRepl :: Repl a -> IO a
runRepl x = do
    h <- (</> ".pizarnik") <$> getHomeDirectory
    flip evalStateT ([], Node IM.empty []) $
        runInputT (defaultSettings { historyFile = Just h }) x

loop :: Repl ()
loop = do
    inp <- getInputLine " "
    case words <$> inp of
        Just (":m":_) -> undefined
        Just e        -> po (stack (dbg (src (unwords e))) <> hardline) *> loop
        Nothing       -> pure ()

stack :: [L] -> Doc ann
stack = p.reverse where
    p []     = "----"
    p (l:ls) = pretty l <#> p ls

po = liftIO . renderIO stdout . layoutSmart defaultLayoutOptions

src = encodeUtf8 . TL.pack
