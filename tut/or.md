---
title: Or-Patterns
author: V. E. McHale
date: 18 Oct. 2025
bibliography: ty.bib
---

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

Pattern-match exhaustiveness checking in the presence of named or-patterns
is [still a matter of insisting on precise inverses](./inv.html). Had we written

```pizarnik
lte : `lt  --
   := [ `lt⁻¹ ]

gt : Ord -- Bool
   := [ { lte False & `gt⁻¹ True } ]
```

We would be confronted with:

```
prelude/ord.piz:8:6: {`lt ⊕ `eq ⊕ `gt} ⊀ {`lt ⊕ `gt}
```

<!-- better example would be like doing something with bound variable, then stitching those together (with exhaustiveness checking -->

We can define something like or-patterns binding variables, allowing reuse of negative
and positive aspect, viz.

```{.pizarnik include="../test/examples/or.piz" startLine="4"}
```

Inexhaustive patterns are still caught, i.e.

```pizarnik
left : { a `left } -- a
     := [ { `left⁻¹ } ]

maybeLeft : These(a,b) -- Maybe(a)
          := [ { left `just & `right⁻¹ drop `nothing } ]
```

yields

```
test/examples/badOr.piz:9:13: {a `left ⊕ b `right ⊕ a b `both} ⊀ {a `left ⊕ b `right}
```

and

```pizarnik
left : { a `left ⊕ a b `both } -- a
     := [ { `left⁻¹ & `both⁻¹ nip } ]

maybeLeft : These(a,b) -- Maybe(a)
          := [ { left `just } ]
```

yields

```
test/examples/badOr2.piz:9:13: {a `left ⊕ b `right ⊕ a b `both} ⊀ {a `left ⊕ a b `both}
```
