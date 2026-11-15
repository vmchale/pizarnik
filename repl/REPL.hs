module REPL ( repl ) where

import           A
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.Class        (lift)
import           Control.Monad.Trans.Except       (runExceptT)
import           Control.Monad.Trans.State.Strict (StateT, evalStateT, get, gets, put, runState, runStateT)
import qualified Data.IntMap                      as IM
import           Data.List                        (isPrefixOf)
import qualified Data.Map                         as M
import           Data.Maybe                       (mapMaybe)
import qualified Data.Text                        as T
import qualified Data.Text.Lazy                   as TL
import           Data.Text.Lazy.Encoding          (encodeUtf8)
import           L
import           Loc
import           P
import           Parse                            (pAtoms)
import           Pr
import           Prettyprinter                    (Doc, Pretty (pretty), hardline, vsep, (<+>))
import           S
import           System.Console.Haskeline         (InputT, Settings (historyFile), completeFilename, defaultSettings, fallbackCompletion, getInputLine, runInputT, setComplete,
                                                   simpleCompletion)
import           System.Directory                 (getHomeDirectory)
import           System.Info                      (os)
import           System.IO                        (Handle)
import           Ty
import           Ty.D

repl :: Handle -> [FilePath] -> IO ()
repl h fps = runRepl fps (loop h)

data X = X !AlexUserState (S Loc) (MC (TS Loc) Loc)

type Repl = InputT (StateT X IO)

names :: Monad m => StateT X m [String]
names = do
    X (_,_,n,_) _ (x,_,b) <- get
    let boo (-2) = Just "True"; boo (-1) = Just "False"
        boo u = fmap show (n IM.!? u)
    pure ("dip":"dup":"strcat":mapMaybe boo (IM.keys b<>IM.keys x))

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
    c (":", "")    = pure (":", strC ["ty","st","i"])
    c ("i:", "")   = pure ("i:", strC [""])
    c (" i:", "")  = do {ns <- names; pure (" i:", strC ns)}
    c ("t:", "")   = pure ("t:", strC ["y"])
    c ("yt:", "")  = pure ("yt:", strC [""])
    c (" yt:", "") = do {ns <- names; pure (" yt:", strC ns)}
    c ("s:", "")   = pure ("s:", strC ["t"])
    c ("ts:", "")  = pure ("ts:", strC [""])
    c ("", "")     = do {ns <- names; pure ("", strC ns)}
    c (rp, "")     = do {ns <- names; pure (unwords ("" : tail (words rp)), strC (namePrefix ns rp))}

    -- :browse subcommand which displays types...

strC = map simpleCompletion

pNs :: Pretty a => M.Map T.Text a -> Doc ann
pNs = vsep.map pB.M.toList

loop :: Handle -> Repl ()
loop h = do
    inp <- getInputLine " "
    case words <$> inp of
        Just (":ty":e) -> printT h (unwords e) *> loop h
        Just (":i":e)  -> try h (unwords e) *> loop h
        Just [":alex"] -> (po h.pNs =<< lg (\(X (_,n,_,_) _ _) -> n)) *> loop h
        Just [":dump"] -> (liftIO . uncurry db =<< lg (\(X l _ m) -> (l,m))) *> loop h
        Just [":st"]   -> do {(X _ s _) <- ll; dbg h s; loop h}
        Just e         -> printA h (unwords e) *> loop h
        Nothing        -> pure ()

na = faseq no

try :: Handle -> String -> Repl ()
try h src = do
    (X l _ (b,c,ar)) <- ll
    case pAtoms l (bytesl src) of
        Left err -> pE h err
        Right ((i,_,_,_),at) ->
            let tyctx=Ext (aLs<$>b) c ar
                (steps,_)=runState (tdbg tyctx (na at)) i
            in po h$pTs steps
-- https://www.compart.com/en/unicode/block/U+2500

printA, printT :: Handle -> String -> Repl ()
printT h src = do
    (X l _ (b,c,ar)) <- ll
    case pAtoms l (bytesl src) of
        Left err -> pE h err
        Right ((i,_,_,_),at) -> do
            let tyctx = Ext (aLs<$>b) c ar
            case runStateT (tAS tyctx [] (na at)) i of
                Right ((_, SL a _),_) -> pE h a
                Left err              -> pE h err

printA h src = do
    (X l s c) <- ll
    case pAtoms l (bytesl src) of
        Left err -> pE h err
        Right ((i,ii,ti,m),at) -> do
            case rc i c s (na at) of
                Right (s',i') -> do
                    lift $ put (X (i',ii,ti,m) s' c)
                    stackpp h s'
                Left err -> pE h err

dbg h = po h.d.reverse where
    d = vsep.map (\a -> pretty a <+> ":" <+> pretty (aL a))

stackpp h=po h.stack

pE :: Pretty a => Handle -> a -> Repl ()
pE h = po h.pretty
po h = liftIO.rh h.(<>hardline)

bytesl = encodeUtf8 . TL.pack

namePrefix :: [String] -> String -> [String]
namePrefix ns prevRev = filter (last (words (reverse prevRev)) `isPrefixOf`) ns

(</>) =
    case os of
    "windows" -> \x y -> x ++ "\\" ++ y
    _         -> \x y -> x ++ "/" ++ y
