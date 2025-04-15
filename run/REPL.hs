module REPL ( loop ) where

import           A
import           Control.Monad.IO.Class           (liftIO)
import           Control.Monad.Trans.State.Strict (StateT)
import qualified Data.Text.Lazy                   as TL
import           Data.Text.Lazy.Encoding          (encodeUtf8)
import           L
import           P
import           Prettyprinter                    (defaultLayoutOptions, layoutSmart)
import           Prettyprinter.Render.Text        (renderIO)
import           System.Console.Haskeline         (InputT, getInputLine)
import           System.IO                        (stdout)

type Repl = InputT (StateT (S, Ctx (TS AlexPosn)) IO)

loop :: Repl ()
loop = do
    inp <- getInputLine " "
    case words <$> inp of
        Just (":m":_) -> undefined
        Just e        -> po$dbg (src (unwords e))

po = liftIO . renderIO stdout . layoutSmart defaultLayoutOptions

src = encodeUtf8 . TL.pack
