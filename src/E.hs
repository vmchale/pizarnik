module E (E (..)) where

import           Control.Exception (Exception)
import           Data.Typeable     (Typeable)
import           Nm
import           Parse
import           Pr
import           Prettyprinter     (Pretty (..), (<+>))
import           R
import           Ty

data E a = PE (ParseE a) | TyE (TE a) | RE (RE a) | MDF !(MN a) | MDC !(MN a) | MDT !(MN a) | ES deriving Functor

instance Pretty a => Pretty (E a) where
    pretty (PE e)  = pretty e
    pretty (TyE e) = pretty e
    pretty (RE e)  = pretty e
    pretty (MDF m) = pm m "imports the same function from different sources."
    pretty (MDC m) = pm m "imports the same type from different sources."
    pretty (MDT m) = pm m "imports the same constructor from different sources."
    pretty ES      = "not enough arguments on the stack."

pm m = ((pretty (ann m) <+> "Module" <+> sq m) <+>)

instance Pretty a => Show (E a) where show=show.pretty

instance (Pretty a, Typeable a) => Exception (E a) where
