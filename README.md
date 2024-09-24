# Pizarnik

Pizarnik is a stack-based, concatenative language with structural sum types and
evocative syntax for pattern-matching.

Aspirational examples:

```
type Bool = `true ⊕ `false;

if : a a `t -- a
   := [ `true⁻¹ drop ]

else : a a `f -- a
     := [ `false⁻¹ nip ]

choice : a a Bool -- a
       := [ { if & else } ]
```
