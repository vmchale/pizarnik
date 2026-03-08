module REPL ( repl ) where

import           A
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (runExceptT)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT, get, gets, put, runState, runStateT)
import qualified Data.IntMap                      as IM
import           Data.List                        (isPrefixOf)
import qualified Data.Map                         as M
import qualified Data.Text                        as T
import qualified Data.Text.Lazy                   as TL
import           Data.Text.Lazy.Encoding          (encodeUtf8)
import           Data.Tree                        (Tree (Node))
import           L
import           Loc
import           P
import           Parse                            (pAtoms)
import           Pr
import           Prettyprinter                    (Doc, Pretty (pretty), flatAlt, group, hardline, hsep, indent, vsep, (<+>))
import           S
import           System.Console.Haskeline         (InputT, Settings (historyFile), completeFilename, defaultSettings, fallbackCompletion, getInputLine, runInputT, setComplete,
                                                   simpleCompletion)
import           System.Directory                 (getHomeDirectory)
import           System.Info                      (os)
import           Ty

repl :: [FilePath] -> IO ()
repl fps = runRepl fps loop

data X = X !AlexUserState (S Loc) (MC (TS Loc) Loc)

type Repl = InputT (StateT X IO)

names :: Monad m => StateT X m [String]
names = do
    X (_,_,n,_) _ (x,_,b) <- get
    let boo (-2) = "True"; boo (-1) = "False"
        boo u = show (n IM.! u)
    pure ("dip":"dup":"strcat":map boo (IM.keys b<>IM.keys x))

ll=lift get;lg=lift.gets

sRepl = runExceptT.flip runStateT (0,mempty,mempty,mempty)

runRepl :: [FilePath] -> Repl a -> IO a
runRepl fp x = do
    h <- (</> ".pizarnik") <$> getHomeDirectory
    liftIO (sRepl $ tMs ["."] fp) >>= \case
        Left err -> error (show err)
        Right (ctx,st) ->
            flip evalStateT (X st [] (naïve ctx)) $
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
        Just (":i":e)  -> try (unwords e) *> loop
        Just [":alex"] -> (po.pNs =<< lg (\(X (_,n,_,_) _ _) -> n)) *> loop
        Just [":dbg"]  -> (liftIO . uncurry db =<< lg (\(X l _ m) -> (l,m))) *> loop
        Just e         -> printA (unwords e) *> loop
        Nothing        -> pure ()

na = faseq no

pTs = vsep.pT []

pT _ []              = []
pT c (Node x xs:xss) =
    case x of
        Right (a,t) -> let c'=c++[a] in tr (pan c' t:pT c' xss)
        Left e      -> tr [pretty e]
  where tr | null xs = id | otherwise = (indent 4 (pTs xs):)

        pan e t = group (hsep (pretty<$>e) <+> ":" <^> group (pretty t))
        s <^> t = flatAlt (t<#>indent 4 t) (s<+>t)

try :: String -> Repl ()
try src = do
    (X l _ (b,c,ar)) <- ll
    case pAtoms l (bytesl src) of
        Left err -> pE err
        Right ((i,_,_,_),at) ->
            let tyctx=Ext (aLs<$>b) c ar
                (steps,_)=runState (tdbg tyctx (na at)) i
            in po$pTs steps

printA, printT :: String -> Repl ()
printT src = do
    (X l _ (b,c,ar)) <- ll
    case pAtoms l (bytesl src) of
        Left err -> pE err
        Right ((i,_,_,_),at) -> do
            let tyctx = Ext (aLs<$>b) c ar
            case tAS i tyctx [] (na at) of
                Right ((_, SL a _),_) -> pE a
                Left err              -> pE err

printA src = do
    (X l s c) <- ll
    case pAtoms l (bytesl src) of
        Left err -> pE err
        Right ((i,ii,ti,m),at) -> do
            case rc i c s (na at) of
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
