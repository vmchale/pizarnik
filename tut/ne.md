% Non-Empty Lists
% 20 Oct. 2025
% V. E. McHale

In Pizarnik, we can define functions on lists and they will work on
non-empty lists.

```{.pizarnik include="../lib/list.piz" startLine=3 endLine=10}
```

```{.pizarnik include="../test/data/permeable.piz" startLine=4 endLine=10}
```

`foldr` accepts a `List(a)`, i.e. ``{ `nil ⊕ List(a) a `cons }`` as an argument; we can imagine how a pattern match that handles both the ```nil`` and ``List(a) a `cons`` cases should handle an argument of type ``NE(a) = { List(a) `cons }``.

Non-empty lists enforce the same safety as in Haskell:

```{.pizarnik include="../lib/list.piz" startLine=11 endLine=12}
```

Had we tried to write `head : List(a) -- a`:

```
5:17: {`nil ⊕ List(a) b `cons} ⊀ {ρ₁ ρ₂ `cons}
```

Moreover, pattern-match exhaustiveness is enforced for non-empty lists, viz.

```{.pizarnik include="../test/data/permeable.piz" startLine=12 endLine=13}
y : -- Unit
  := [ x head ]
```

is admissible, but

```pizarnik
x : -- List(Unit)
  := [ `nil ]

w : -- Unit
  := [ x head ]
```

will fail:

```
23:8: ‘{`nil ⊕
       List( a ) Unit `cons}’ is not an acceptable argument, expected ‘{List( a ) b `cons}’
```

# Polarity and Analogy

Doing the above in Haskell (for instance) is more fickle. We can define
`foldr` to apply to both lists and non-empty lists using a typeclass,
but we still need to write the implementation twice. And typeclass
instance scoping is
[fraught](https://blog.ezyang.com/2014/07/type-classes-confluence-coherence-global-uniqueness/).

Extensible cases [@blume2006] avoid this, in a way dual to row polymorphism—where it works,
it is strictly preferable [@rho].

# References

<!-- https://pchiusano.github.io/2018-02-13/typeclasses.html "open" discovery/containers... -->
