module Loc ( Loc (..), no ) where

import           L
import           Prettyprinter (Pretty (..))

data Loc = Loc !FilePath !Int !Int | No !Int !Int | CLI

no :: AlexPosn -> Loc
no (AlexPn _ l c) = No l c

instance Pretty Loc where
    pretty (Loc fp l c) = pretty fp <> ":" <> pretty l <> ":" <> pretty c
    pretty (No l c)     = pretty l <> ":" <> pretty c
    pretty CLI          = "(command-line)"
