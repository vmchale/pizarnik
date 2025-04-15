module REPL ( repl ) where

import           A
import           Control.Exception                (Exception, throw)
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import qualified Data.IntMap                      as IM
import qualified Data.Text.Lazy                   as TL
import           Data.Text.Lazy.Encoding          (encodeUtf8)
import           Data.Tree                        (Tree (Node))
import           L
import           Parse                            (pAtoms)
import           Pr
import           Prettyprinter                    (Doc, defaultLayoutOptions, hardline, layoutSmart, pretty)
import           Prettyprinter.Render.Text        (renderIO)
import           S
import           System.Console.Haskeline         (InputT, Settings (historyFile), defaultSettings, getInputLine, runInputT)
import           System.Directory                 (getHomeDirectory)
import           System.FilePath                  ((</>))
import           System.IO                        (stdout)
import           Ty                               (tAS)

repl :: IO ()
repl = runRepl loop

data X = X !AlexUserState S (Ctx (TS AlexPosn))

type Repl = InputT (StateT X IO)

runRepl :: Repl a -> IO a
runRepl x = do
    h <- (</> ".pizarnik") <$> getHomeDirectory
    flip evalStateT (X alexInitUserState [] (Node IM.empty [])) $
        runInputT (defaultSettings { historyFile = Just h }) x

loop :: Repl ()
loop = do
    inp <- getInputLine " "
    case words <$> inp of
        Just (":m":_) -> undefined
        Just e        -> printA (unwords e) *> loop
        Nothing       -> pure ()

printA :: String -> Repl ()
printA src = do
    (X l s c) <- lift get
    let (l'@(i,_,_,_),at) = x$pAtoms l (bytesl src)
        (a,_)=x (tAS i mempty at)
        s' = r (Node IM.empty []) a s
    lift $ put (X l' s' c)
    stackpp s'
  where
    x :: Exception e => Either e a -> a
    x = either throw id

stackpp=po.stack

stack :: [L] -> Doc ann
stack = p.reverse where
    p []     = "----" <> hardline
    p (l:ls) = pretty l <#> p ls

po = liftIO . renderIO stdout . layoutSmart defaultLayoutOptions

bytesl = encodeUtf8 . TL.pack
