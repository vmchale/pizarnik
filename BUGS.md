cabal run pc -- repl lib/maybe.piz prelude/fn.piz
<TAB>
dip       dup       swap      `just     `nothing

only completions for constructors!
(in general identifiers are missing!!)

```
 15 5 gcd
5
----
 10 gcd
not enough arguments on the stack.
```

```
 1 False
1
False
----
 1 False (12)
1
False
False
1
----
 (132)
1:1: ‘Int’ is not an acceptable argument, expected ‘{False}’
```
