```
 :ty (13) dup (24)
'A a b c -- 'A d b c a
```
uh-oh

```
 :ty swap dup swap
'A a b -- 'A b a c
```

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

```
  1 2 3 [swap] dip
2
1
3
----
 drop3
not enough arguments on the stack.
```
