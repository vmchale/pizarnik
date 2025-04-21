{-# LANGUAGE LambdaCase #-}

module REPL ( repl ) where

import           A
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (runExceptT)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT, get, put)
import           Data.Bifunctor                   (first)
import qualified Data.IntMap                      as IM
import           Data.List                        (isPrefixOf)
import qualified Data.Text.Lazy                   as TL
import           Data.Text.Lazy.Encoding          (encodeUtf8)
import           Data.Tree                        (Tree (Node))
import           L
import           P
import           Parse                            (pAtoms)
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
data X = X !AlexUserState (S AlexPosn) (Tree (F (TS AlexPosn), Ar))

type Repl = InputT (StateT X IO)

alexSt (u,t,i) = (u,t,i,IM.empty)

names = pure ["dip", "dup", "swap"]

runRepl :: [FilePath] -> Repl a -> IO a
runRepl [fp] x = do
    h <- (</> ".pizarnik") <$> getHomeDirectory
    liftIO (runExceptT $ tMs ["."] fp) >>= \case
        Left err -> error (show err)
        Right (st,ctx) -> do
            let t=fmap (first lm) ctx
            flip evalStateT (X (alexSt st) [] t) $
                runInputT (setComplete (c `fallbackCompletion` completeFilename) (defaultSettings { historyFile = Just h })) x
  where
    c (":", "")    = pure (":", strC ["help", "ty"])
    c ("t:", "")   = pure ("t:", strC ["y"])
    c ("yt:", "")  = pure ("yt:", strC [""])
    c (" yt:", "") = do {ns <- names; pure (" yt:", strC ns)}
    c (rp, "")     = do {ns <- names; pure (unwords ("" : tail (words rp)), strC (namePrefix ns rp))}

strC = map simpleCompletion

loop :: Repl ()
loop = do
    inp <- getInputLine " "
    case words <$> inp of
        Just (":ty":e) -> printT (unwords e) *> loop
        Just e         -> printA (unwords e) *> loop
        Nothing        -> pure ()

printT :: String -> Repl ()
printT src = do
    (X l s (Node (t,ar) _)) <- lift get
    case pAtoms l (bytesl src) of
        Left err -> pE err
        Right ((i,_,_,_),at) -> do
            let tyctx = Ext (aLs<$>t) IM.empty ar
            case tAS i tyctx s at of
                Right (SL a _,_) -> pE a
                Left err         -> pE err

printA :: String -> Repl ()
printA src = do
    (X l s c@(Node (t,ar) _)) <- lift get
    -- TODO: typecheck w/ context
    case pAtoms l (bytesl src) of
        Left err -> pE err
        Right ((i,ii,ti,m),at) -> do
            let tyctx = Ext (aLs<$>t) IM.empty ar
            case tAS i tyctx s at of
                Right (a,i') -> do
                    let s' = r c (aas a) s
                    lift $ put (X (i',ii,ti,m) s' c)
                    stackpp s'
                Left err -> pE err

stackpp=po.stack

pE :: Pretty a => a -> Repl ()
pE = po.pretty
po = liftIO . renderIO stdout . layoutSmart defaultLayoutOptions . (<>hardline)

bytesl = encodeUtf8 . TL.pack

namePrefix :: [String] -> String -> [String]
namePrefix ns prevRev = filter (last (words (reverse prevRev)) `isPrefixOf`) ns
