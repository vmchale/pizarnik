# Pizarnik

Pizarnik is a stack-based, concatenative language with extensible cases and
evocative syntax for pattern-matching.

<!-- % https://homepages.inf.ed.ac.uk/wadler/papers/dual-revolutions/dual-revolutions.pdf gets it backwards? "from A & B one may extract A or B but not both... our take is "one path is taken"... resources not so much -->

# Pattern-Match Arms as Functions

Extensible cases are atoms, and typeable.

```
type B = {`t ⊕ `f};

if : a b `t -- a
   := [ `t⁻¹ drop ]

else : a b `f -- b
     := [ `f⁻¹ nip ]

choice : a a B -- a
       := [ { if & else } ]
```

# [(Not) Subtypes](https://brianmckenna.org/blog/row_polymorphism_isnt_subtyping)

```
@i prelude/fn

%-

type List a = { `nil ⊕ List(a) a `cons };

type NE a = { List(a) a `cons };

head : NE(a) -- a
     := [ { `cons⁻¹ nip } ]

foldr : [ a b -- b ] b List(a) -- b
      := [ { `nil⁻¹ nip
           & `cons⁻¹ [dup] dip3 rotl [rot [rot $] dip swap] dip foldr } ]
```

The same `foldr` works on nonempty lists and lists and `head` only works on nonempty lists. Had we tried to write `head : List(a) -- a`:

```
5:17: {`nil ⊕ List(a) b `cons} ⊀ {ρ₁ ρ₂ `cons}
```

# Or-Patterns

`&` (with) gives us the functionality of or-patterns:

```
@i prelude/fn

%-

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
       List( a ) Unit `cons}’ is not an acceptable argument, expected ‘{List( a ) b `cons}’
```

<!-- related to extensibility + atomicity of each _arm_ rather than tying each clause to the sum type decl... (constructors have arity buuut independent from the other sum typeys -->

# Solving the Expression Problem

See [Blume, Acar, and Chae](https://dl.acm.org/doi/10.1145/1159803.1159836).

# Doc
  - [Permutations in Stack Programming](https://vmchale.github.io/pizarnik/perm.html)
  - [Non-Empty Lists](https://vmchale.github.io/pizarnik/ne.html)
