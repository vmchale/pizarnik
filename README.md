# Pizarnik

Pizarnik is a stack-based, concatenative language with extensible cases and
evocative syntax for pattern-matching.

<!-- % https://homepages.inf.ed.ac.uk/wadler/papers/dual-revolutions/dual-revolutions.pdf gets it backwards? "from A & B one may extract A or B but not both... our take is "one path is taken"... resources not so much -->

# First-Class Pattern-Match Arms

Extensible cases are atoms, and typeable.

```pizarnik
type B = {`t ⊕ `f};

if : a b `t -- a
   := [ `t⁻¹ drop ]

else : a b `f -- b
     := [ `f⁻¹ nip ]

choice : a a B -- a
       := [ { if & else } ]
```

# [(Not) Subtypes](https://brianmckenna.org/blog/row_polymorphism_isnt_subtyping)

```pizarnik
@prelude/fn

type List a = { `nil ⊕ List(a) a `cons };

type NE a = { List(a) a `cons };

head : NE(a) -- a
     := [ { `cons⁻¹ nip } ]

foldr : [ a b -- b ] b List(a) -- b
      := [ { `nil⁻¹ nip
           & `cons⁻¹ [dup] dip3 (152)(23) [$] dip2 (23) foldr } ]
```

The same `foldr` works on nonempty lists and lists while `head` only works on nonempty lists. Had we written `head : List(a) -- a`:

```
5:17: {`nil ⊕ List(a) a `cons} ⊀ {List(a) a `cons}
```

# Or-Patterns

`&` (with) gives us the functionality of or-patterns:

```pizarnik
@prelude/fn

type Ord = {`lt ⊕ `eq ⊕ `gt};

gt : Ord -- Bool
   := [ { { `lt⁻¹ & `eq⁻¹ } False & `gt⁻¹ True } ]
```

# Exhaustiveness Checking

Pattern-match exhaustiveness checking falls out for free:

```
x : -- List(Unit)
  := [ `nil ]

w : -- Unit
  := [ x head ]
```

will fail, viz.

```
23:8: ‘{`nil ⊕
       List( Unit ) Unit `cons}’ is not an acceptable argument, expected ‘{List( a ) a `cons}’
```

<!-- related to extensibility + atomicity of each _arm_ rather than tying each clause to the sum type decl... (constructors have arity buuut independent from the other sum typeys -->

# Solving the Expression Problem

[Extensible cases](https://dl.acm.org/doi/10.1145/1159803.1159836) put forward
by Blume, Acar, and Chae solve the expression problem:

<!-- properly solved, expression problem is one of polarity, (sum types that are disjuncts demand disjunctive products?) not analogy -->
<!-- maybe it's not that OO "extends types" it's that extensible cases extend _functions_ (contravariantly) -->

```pizarnik
@prelude/fn

type Either a b = { a `left ⊕ b `right };

mapLeft : [ a -- c ] Either(a,b) -- Either(c,b)
        := [ { `left⁻¹ swap $ `left
             & `right⁻¹ nip `right }
           ]
```

```pizarnik
@prelude/fn
@lib/either

type Both a b = Either(a,b) ∪ { a b `both };

map1 : [a -- b] Both(a,c) -- Both(b,c)
     := [ { mapLeft
          & `both⁻¹ [swap $] dip `both }
        ]
```

# Justification

## Examples

  - [Non-Empty Lists](https://vmchale.github.io/pizarnik/ne.html)
  - [ASTs for Compiler Phases](https://vmchale.github.io/pizarnik/ast.html)
  - [Solving the Expression Problem](https://vmchale.github.io/pizarnik/exp.html)
  - [Error Hierarchies](https://vmchale.github.io/pizarnik/err.html)

## Theory

  - [Pattern-Matching as Inverse](https://vmchale.github.io/pizarnik/inv.html)
  - [Or-Patterns](https://vmchale.github.io/pizarnik/or.html)
  - [Permutations in Stack Programming](https://vmchale.github.io/pizarnik/perm.html)
