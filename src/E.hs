module E ( E (..) ) where

import           L
import           Parse         (ParseE)
import           Prettyprinter (Pretty (pretty))
import           R             (RE)
import           Ty            (TE)

data E = ET FilePath !(TE AlexPosn) | ER FilePath !(RE AlexPosn) | EP FilePath !ParseE

instance Pretty E where
    pretty (ET fp e) = pretty fp <> ":" <> pretty e
    pretty (ER fp e) = pretty fp <> ":" <> pretty e
    pretty (EP fp e) = pretty fp <> ":" <> pretty e
