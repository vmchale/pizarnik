module Ty.D ( pTs ) where

import           A
import           Loc
import           Pr
import           Prettyprinter (Doc, Pretty (pretty), flatAlt, group, hardline, hsep, indent, vsep, (<+>))
import           Ty

pTs = vsep.pT []

pT :: [A Loc] -> [TN (AP Loc)] -> [Doc x]
pT _ []                                 = []
pT c (TN (a, Right t):TN (_, Left e):_) = let c'= c++[a] in [pan [a] t, pan c' e]
pT c (TN (a, Right t):ts)               = let c'=c++[a] in pan c' t:pT c' ts
pT c (TN (a, Left e):_)                 = let c'=c++[a] in [pan c' e]
pT c (TArm (a, Right t) as:ts)          = let c'=c++[a] in cas as ++ nl:pan c' t:pT c' ts
pT c (TArm (a, Left e) as:_)            = let c'=c++[a] in cas as ++ [nl,pan c' e]
pT c (TQ (a, Right t) as:ts)            = let c'=c++[a] in ca as:nl:pan c' t:pT c' ts
pT c (TQ (a, Left e) as:_)              = let c'=c++[a] in [ca as, nl, pan c' e]

pan e t = group (hsep (pretty<$>e) <+> ":" <^> group (pretty t))
s <^> t = flatAlt (s<#>indent 4 t) (s<+>t); ca=(nl<>).indent 4.pTs; cas=map ca; nl=hardline
