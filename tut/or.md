% Or-Patterns
% V. E. McHale
% 18 Oct. 2025

Begin by defining `Ord`:

```{.pizarnik include="../prelude/ord.piz" startLine=3 endLine=3}
```

Then we can write:

```pizarnik
gt : Ord -- Bool
    := [ { { `lt⁻¹ & `eq⁻¹ } False & `gt⁻¹ True } ]
```

``{`lt⁻¹ & `eq⁻¹}`` has type ``{`lt ⊕ `eq} --``. The use of `&` to juxtapose pattern match arms is intended to recall $(G \oplus H)^\bot = G^\bot \& H^\bot$ from linear logic [@munchmaccagnoni2009].

This makes sense---a `&` ("with") juxtaposes two pattern-match arms (inverse constructors) to form a (typed) function accepting a sum type as argument.
<!-- A sum type gives us two choices for how to produce a return value de Morgan ^ linear logic -->
<!-- more about polarity than inverse? -->

```{.pizarnik include="../prelude/ord.piz" startLine=5 endLine=9}
```

We could have defined `gt` with the above, viz.

```pizarnik
gt : Ord -- Bool
   := [ { lte False & `gt⁻¹ True } ]
```

<!-- atomicity... allows us to combine unto what is essentially or-patterns -->
<!-- mention pattern match exhaustiveness checking still works? -->
