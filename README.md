# Pizarnik

Pizarnik is a stack-based, concatenative language with extensible cases and
evocative syntax for pattern-matching.

Example:

<!-- % https://homepages.inf.ed.ac.uk/wadler/papers/dual-revolutions/dual-revolutions.pdf gets it backwards? "from A & B one may extract A or B but not both... our take is "one path is taken"... resources not so much -->


```
type B = {`t ⊕ `f};

if : a b `t -- a
   := [ `t⁻¹ drop ]

else : a b `f -- b
     := [ `f⁻¹ nip ]

choice : a a B -- a
       := [ { if & else } ]
```

```
@i prelude/fn

%-

type List a = { `nil ⊕ List(a) a `cons };

type NE a = { List(a) a `cons };

head : NE(a) -- a
     := [ { `cons⁻¹ nip } ]

tail : NE(a) -- a
     := [ { `cons⁻¹ _ } ]

foldr : [ a b -- b ] b List(a) -- b
      := [ { `nil⁻¹ nip & `cons⁻¹ [dup] dip3 [rotl] dip [[rot $] dip swap] dip foldr } ]
```

The same `foldr` works on nonempty lists and lists (unlike Haskell); `head` only works on nonempty lists.
