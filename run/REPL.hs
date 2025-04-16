{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

module REPL ( repl ) where

import           A
import           Control.Exception                (Exception, throw)
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (runExceptT)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import qualified Data.IntMap                      as IM
import qualified Data.Text.Lazy                   as TL
import           Data.Text.Lazy.Encoding          (encodeUtf8)
import           Data.Tree                        (Tree (Node))
import           L
import           P
import           Parse                            (pAtoms)
import           Pr
import           Prettyprinter                    (Doc, Pretty (pretty), defaultLayoutOptions, hardline, layoutSmart)
import           Prettyprinter.Render.Text        (renderIO)
import           S
import           System.Console.Haskeline         (InputT, Settings (historyFile), defaultSettings, getInputLine, runInputT)
import           System.Directory                 (getHomeDirectory)
import           System.FilePath                  ((</>))
import           System.IO                        (stdout)
import           Ty

repl :: [FilePath] -> IO ()
repl fps = runRepl fps loop

data ReplPos = SP | AP !AlexPosn

instance Pretty ReplPos where
    pretty SP     = "(stack)"
    pretty (AP p) = pretty p

data X = X !AlexUserState S (Ctx (TS AlexPosn))

type Repl = InputT (StateT X IO)

alexSt (u,t,i) = (u,t,i,IM.empty)

runRepl :: [FilePath] -> Repl a -> IO a
runRepl [fp] x = do
    h <- (</> ".pizarnik") <$> getHomeDirectory
    liftIO (runExceptT $ tMs ["."] fp) >>= \case
        Left err -> error (show err)
        Right (st,ctx) -> do
            let t=fmap lm ctx
            flip evalStateT (X (alexSt st) [] t) $
                runInputT (defaultSettings { historyFile = Just h }) x

loop :: Repl ()
loop = do
    inp <- getInputLine " "
    case words <$> inp of
        Just e  -> printA (unwords e) *> loop
        Nothing -> pure ()

printA :: String -> Repl ()
printA src = do
    (X l s c@(Node t _)) <- lift get
    -- TODO: typecheck against lits
    case pAtoms l (bytesl src) of
        Left err -> pE err
        Right (l'@(i,_,_,_),at) -> do
            let tyctx = Ext (fmap AP . aLs<$>t) IM.empty IM.empty
            let (a,_)=x (tAS i tyctx (faseq AP at))
                s' = r (fmap (faseq (fmap AP) <$>) c) a s
            lift $ put (X l' s' c)
            stackpp s'
  where
    x :: Exception e => Either e a -> a
    x = either throw id

stackpp=po.stack

stack :: S -> Doc ann
stack = p.reverse where
    p []     = "----"
    p (l:ls) = pretty l <#> p ls

pE = po.pretty
po = liftIO . renderIO stdout . layoutSmart defaultLayoutOptions . (<>hardline)

bytesl = encodeUtf8 . TL.pack
