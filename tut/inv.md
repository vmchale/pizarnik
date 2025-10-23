% Pattern-Matching as Inverse
% V. E. McHale
% 20 Oct. 2025

Suppose we have

```pizarnik
type Pair a b = { a b `pair };
```

Then ```pair `` has type

```pizarnik
`pair : a b -- Pair(a,b)
```

Given atoms of types `a`, `b` on the stack, it will leave an atom of type
`Pair(a,b)` in their place. The inverse ```pair⁻¹`` should then take an atom of
type `Pair(a,b)` and leave two atoms of types `a`, `b` on the stack:

```pizarnik
`pair⁻¹ : Pair(a,b) -- a b
```

<!-- Inverse exchanges left and right -->

This is not new [@ehrenberg2009]. However, with pattern match arms as
first-class (typed) atoms, we can implement `&` which juxtaposes two inverse
constructors to form a pattern match clause handling a sum type, viz.

```pizarnik
type Maybe(a) = { a `just ⊕ `nothing };

isJust : Maybe(a) -- Bool
       := [ { `just⁻¹ drop True
            & `nothing⁻¹ False
            }
          ]
```

This is inspired by linear logic's $(G \oplus H)^\bot = G^\bot \& H^\bot$—to
invert a sum type, one supplies an inverse (pattern match clause) for each
summand. This is precisely the De Morgan laws. We have two choices to return a
value of type `Maybe(a)`, and, dually, to accept a value of type `Maybe(a)` as
argument, we must write two pattern-match clauses.

In fact, pattern match exhaustiveness checking falls out for free in this
scheme. Had we written

```pizarnik
isJust : Maybe(a) -- Bool
       := [ { `just⁻¹ drop True } ]
```

we would be confronted with

```
5:20: {a `just ⊕ `nothing} ⊀ {ρ₁ `just}
```

<!-- first-class -->
<!-- constructors are associated with a particular arity but not a particular named type (structural pattern-match exhaustiveness checking) -->

# References
