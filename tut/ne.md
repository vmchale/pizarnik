% 15 Oct. 2025
% Non-Empty Lists
% V. E. McHale

In Pizarnik, we can define functions on lists and they will work on
non-empty lists.

``` pizarnik
type List a = { `nil ⊕ List(a) a `cons };

type NE a = { List(a) a `cons };

foldr : [ a b -- b ] b List(a) -- b
      := [ { `nil⁻¹ nip
           & `cons⁻¹ [dup] dip3 rotl [rot [rot $] dip swap] dip foldr } ]
```

``` pizarnik
type Unit = {`unit};

x : -- NE(Unit)
  := [ `nil `unit `cons ]

z : -- Unit
  := [ [nip] `unit x foldr ]
```

This is allowed because `foldr` accepts a `List(a)`, i.e. ``{`nil ⊕ List(a) a `cons }`` as an argument; we can imagine how a pattern match that handles both the ```nil`` and ``List(a) a `cons`` cases should handle an argument of type ``NE(a) = { List(a) `cons }``.

Non-empty lists enforce the same safety as in Haskell:

``` pizarnik
head : NE(a) -- a
     := [ { `cons⁻¹ nip } ]
```

```pizarnik
y : -- Unit
  := [ x head ]
```

is admissible, but

```pizarnik
w : -- Unit
  := [ `nil head ]
```

will fail:

```
20:8: ‘{`nil}’ is not an acceptable argument, expected ‘{List(a) b `cons}’
```

# Superiority

Doing the above in Haskell (for instance) is more fraught. We can define
`foldr` to apply to both lists and non-empty lists using a typeclass,
but we still need to write the implementation twice. Moreover, the
globality of typeclasses

<!-- extensible cases are superior to typeclasses in the same way row polymorphism is superior to typeclasses -->

<!-- https://blog.ezyang.com/2014/07/type-classes-confluence-coherence-global-uniqueness/ -->
<!-- https://pchiusano.github.io/2018-02-13/typeclasses.html "open"
discovery/containers... -->
<!-- The same `foldr` works on nonempty lists and lists and `head` only works on nonempty lists, enforced by static typing. -->
<!-- no subtyping relation except checking applicability? -->
