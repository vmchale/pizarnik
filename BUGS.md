  :ty (123) (12)
pc: Uncaught exception ghc-internal:GHC.Internal.Exception.ErrorCall:

(Array.!): undefined array element

While handling (Array.!): undefined array element

 `empty "y" "y" `var `abs `push prettyStack
pc: Uncaught exception ghc-internal:GHC.Internal.Control.Exception.Base.PatternMatchFail:

src/S.hs:(41,1)-(51,35): Non-exhaustive patterns in function ψ

^ should be caught during typechecking...

 "x" `var "x" `lam
{{"x" `var} "x" `lam}
----
 "x" `var "x" `lam printTerm
not enough arguments on the stack.

ugh

 :ty [False [or]] dip foldl
'A {`nil ⊕ List({True ⊕ False}) {True ⊕ False} `cons} -- 'B {False}

uhh

similar problem with

fromList : List(Int) -- Set(Int)
         := [ [ `empty [swap insert] ] dip foldl ]

as ands/foldl...


importing lib/list (into examples/set), where `nil has the SAME arity as in examples/set, leads to problems!
... we DO renames tags, so I assume that the lexer state in REPL then tries to
find `nil with the unique based on lib/list, which is properly invisible...
(also our arity clash check may not be working...)

fromList : List(Int) -- Set(Int)
         := [ [ `nil [ swap insert ] ] dip foldl ]

examples/set.piz:18:29: ‘{`nil ⊕
                         Set( Int ) Int Set( Int ) `branch}’ is not an acceptable argument, expected ‘{`nil}’

(problem of not generalizing types when universals are present... aagh)

test/data/fingertree.piz:6:22: ‘{`o}’ is not an acceptable argument, expected ‘{`e}’

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

this is accepted...

```
h : { `a ⊕ `c ⊕ `t } --
  := [{ `a^ & `c^ & `t^ }]

uhOh : {`t ⊕ `c ⊕ `g} --
     := [h]
```
