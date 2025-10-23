% Or-Patterns
% V. E. McHale
% 18 Oct. 2025

<!-- atomicity... allows us to combine unto what is essentially or-patterns -->

Begin by defining `Ord`:

```pizarnik
@i prelude/fn

type Ord = {`lt ⊕ `eq ⊕ `gt};
```

Then we can write:

```pizarnik
gt : Ord -- Bool
    := [ { { `lt⁻¹ & `eq⁻¹ } False & `gt⁻¹ True } ]
```

``{`lt⁻¹ & `eq⁻¹}`` has type ``{`lt ⊕ `eq} --``. The use of `&` to juxtapose pattern match arms is intended to recall $(G \oplus H)^\bot = G^\bot \& H^\bot$ from linear logic.

This makes sense---a `&` ("with") juxtaposes two pattern-match arms (inverse constructors) to form a function accepting a sum type as argument.
<!-- A sum type gives us two choices for how to produce a return value
de Morgan ^ linear logic -->

```pizarnik
lte : { `lt ⊕ `eq } --
    := [ { `lt⁻¹ & `eq⁻¹ } ]

gte : { `eq ⊕ `gt } --
    := [ { `eq⁻¹ & `gt⁻¹ } ]
```

We could have defined `gt` with the above, viz.

```pizarnik
gt : Ord -- Bool
   := [ { lte False & `gt⁻¹ True } ]
```
