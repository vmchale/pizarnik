module E (E (..)) where

import           Control.Exception (Exception)
import           Data.Typeable     (Typeable)
import           Nm
import           Parse
import           Pr
import           Prettyprinter     (Pretty (..), (<+>))
import           R
import           Ty

data E a = PE ParseE | TyE (TE a) | RE (RE a) | MDF !MN | MDC !MN | MDT !MN

instance Pretty a => Pretty (E a) where
    pretty (PE e)  = pretty e
    pretty (TyE e) = pretty e
    pretty (RE e)  = pretty e
    pretty (MDF m) = "Module" <+> sq m <+> "imports the same function from different sources."
    pretty (MDC m) = "Module" <+> sq m <+> "imports the same type from different sources."
    pretty (MDT m) = "Module" <+> sq m <+> "imports the same constructor from different sources."

instance Pretty a => Show (E a) where show=show.pretty

instance (Pretty a, Typeable a) => Exception (E a) where
