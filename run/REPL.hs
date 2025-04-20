{-# LANGUAGE LambdaCase    #-}
{-# LANGUAGE TupleSections #-}

module REPL ( repl ) where

import           A
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (runExceptT)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import qualified Data.IntMap                      as IM
import           Data.List                        (isPrefixOf)
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
import           System.Console.Haskeline         (InputT, Settings (historyFile), completeFilename, defaultSettings, fallbackCompletion, getInputLine, runInputT, setComplete,
                                                   simpleCompletion)
import           System.Directory                 (getHomeDirectory)
import           System.FilePath                  ((</>))
import           System.IO                        (stdout)
import           Ty

repl :: [FilePath] -> IO ()
repl fps = runRepl fps loop

-- TODO: include names in state for completions
data X = X !AlexUserState (S AlexPosn) (Ctx (TS AlexPosn))

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
                runInputT (setComplete (c `fallbackCompletion` completeFilename) (defaultSettings { historyFile = Just h })) x
  where
    c (rp, "") = do {ns <- pure ["dip", "dup", "swap"]; pure (unwords ("" : tail (words rp)), map simpleCompletion (namePrefix ns rp))}

loop :: Repl ()
loop = do
    inp <- getInputLine " "
    case words <$> inp of
        Just e  -> printA (unwords e) *> loop
        Nothing -> pure ()

printA :: String -> Repl ()
printA src = do
    (X l s c@(Node t _)) <- lift get
    -- TODO: typecheck w/ context
    case pAtoms l (bytesl src) of
        Left err -> pE err
        Right ((i,ii,ti,m),at) -> do
            let tyctx = Ext (aLs<$>t) IM.empty IM.empty
            case tAS i tyctx s at of
                Right (a,i') -> do
                    let s' = r c a s
                    lift $ put (X (i',ii,ti,m) s' c)
                    stackpp s'
                Left err -> pE err

stackpp=po.stack

stack :: S a -> Doc ann
stack = p.reverse where
    p []     = "----"
    p (l:ls) = pretty l <#> p ls

pE :: Pretty a => a -> Repl ()
pE = po.pretty
po = liftIO . renderIO stdout . layoutSmart defaultLayoutOptions . (<>hardline)

bytesl = encodeUtf8 . TL.pack

namePrefix :: [String] -> String -> [String]
namePrefix names prevRev = filter (last (words (reverse prevRev)) `isPrefixOf`) names
