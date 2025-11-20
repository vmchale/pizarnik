module REPL ( repl ) where

import           A
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (runExceptT)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT, get, gets, put, runStateT)
import           Data.Bifunctor                   (first)
import qualified Data.IntMap                      as IM
import           Data.List                        (isPrefixOf)
import qualified Data.Map                         as M
import           Data.Maybe                       (mapMaybe)
import qualified Data.Text                        as T
import qualified Data.Text.Lazy                   as TL
import           Data.Text.Lazy.Encoding          (encodeUtf8)
import           Data.Tree                        (Tree (Node, rootLabel))
import           L
import           P
import           Parse                            (pAtoms)
import           Pr
import           Prettyprinter                    (Doc, Pretty (pretty), hardline, vsep)
import           S
import           System.Console.Haskeline         (InputT, Settings (historyFile), completeFilename, defaultSettings, fallbackCompletion, getInputLine, runInputT, setComplete,
                                                   simpleCompletion)
import           System.Directory                 (getHomeDirectory)
import           System.Info                      (os)
import           Ty

repl :: [FilePath] -> IO ()
repl fps = runRepl fps loop

-- TODO: include names in state for completions
data X = X !AlexUserState (S AlexPosn) [Tree (F (TS AlexPosn), Ar)]

type Repl = InputT (StateT X IO)

names :: Monad m => StateT X m [String]
names = do
    -- X (_,t,_,_) _ c <- get
    -- pure $ map T.unpack (M.keys t)
    X (_,_,n,_) _ c <- get
    let u=concatMap (IM.keys . snd . rootLabel) c
    pure ("dip":"dup":"swap":mapMaybe (fmap show.(n IM.!?)) u)

lg=lift.gets

sRepl = runExceptT.flip runStateT (0,mempty,mempty,mempty)

runRepl :: [FilePath] -> Repl a -> IO a
runRepl fp x = do
    h <- (</> ".pizarnik") <$> getHomeDirectory
    liftIO (sRepl $ tMs ["."] fp) >>= \case
        Left err -> error (show err)
        Right (ctx,st) -> do
            let t=map (fmap (first lm)) ctx
            flip evalStateT (X st [] t) $
                runInputT (setComplete (c `fallbackCompletion` completeFilename) (defaultSettings { historyFile = Just h })) x
  where
    c (":", "")    = pure (":", strC ["ty"])
    c ("t:", "")   = pure ("t:", strC ["y"])
    c ("yt:", "")  = pure ("yt:", strC [""])
    c (" yt:", "") = do {ns <- names; pure (" yt:", strC ns)}
    c ("", "")     = do {ns <- names; pure ("", strC ns)}
    c (rp, "")     = do {ns <- names; pure (unwords ("" : tail (words rp)), strC (namePrefix ns rp))}

strC = map simpleCompletion

pNs :: Pretty a => M.Map T.Text a -> Doc ann
pNs = vsep.map pB.M.toList

loop :: Repl ()
loop = do
    inp <- getInputLine " "
    case words <$> inp of
        Just (":ty":e) -> printT (unwords e) *> loop
        Just [":alex"] -> (po.pNs =<< lg (\(X (_,n,_,_) _ _) -> n)) *> loop
        Just [":dbg"]  -> (liftIO . uncurry db =<< lg (\(X l _ m) -> (l,m))) *> loop
        Just e         -> printA (unwords e) *> loop
        Nothing        -> pure ()

printT :: String -> Repl ()
printT src = do
    (X l _ c) <- lift get
    case pAtoms l (bytesl src) of
        Left err -> pE err
        Right ((i,_,_,_),at) -> do
            let tyctx = naïve c
            case tAS i tyctx [] at of
                Right ((_, SL a _),_) -> pE a
                Left err              -> pE err
  where
    naïve :: [Tree (F (TS a), Ar)] -> Ext a
    naïve t = Ext (foldMap (\(Node (m,_) _) -> aLs<$>m) t) IM.empty (foldMap (\(Node (_,a) _) -> a) t)

printA :: String -> Repl ()
printA src = do
    (X l s c) <- lift get
    case pAtoms l (bytesl src) of
        Left err -> pE err
        Right ((i,ii,ti,m),at) -> do
            case rc i c s at of
                Right (s',i') -> do
                    lift $ put (X (i',ii,ti,m) s' c)
                    stackpp s'
                Left err -> pE err

stackpp=po.stack

pE :: Pretty a => a -> Repl ()
pE = po.pretty
po = liftIO.rDoc.(<>hardline)

bytesl = encodeUtf8 . TL.pack

namePrefix :: [String] -> String -> [String]
namePrefix ns prevRev = filter (last (words (reverse prevRev)) `isPrefixOf`) ns

(</>) =
    case os of
    "windows" -> \x y -> x ++ "\\" ++ y
    _         -> \x y -> x ++ "/" ++ y
