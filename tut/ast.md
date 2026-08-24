% One AST, Several Phases
% V. E. McHale
% 23 Aug. 2026

Often in a compiler a pass will transform the AST so that some variant is no
longer present, so that further passes need only handle a
smaller subset of cases.

Consider desugaring; suppose the syntax `[max x^2+max y]` means `λx.λy. max x^2 + max y`; `x` and `y` are implicitly the bound variables.

```{.pizarnik include="../examples/ast.piz" startLine=3 endLine=29}
```

This does check pattern-match exhaustiveness; if we had written

```pizarnik
dedfn : Int Name Name DExpr -- Int AST
      := [ { `resVar⁻¹ { `x⁻¹ drop & `y⁻¹ nip } `var
           & `lam⁻¹ [dedfn] dip `lam
           & `var⁻¹ drop2 `var
           & `dfn⁻¹ [drop2 fresh] dip dedfn
           } ]
```

it would raise the objection

```pizarnik
examples/ast.piz:15:23: {DExpr DExpr `ap ⊕ DExpr Name `lam ⊕ Name `var ⊕
                        DExpr `dfn ⊕ ResVar `resVar} ⊀ {DExpr Name `lam ⊕
                                                       Name `var ⊕ DExpr `dfn ⊕
                                                       ResVar `resVar}
```

And the result is guaranteed to be of type `AST`; if we had written

```pizarnik
dedfn : Int Name Name DExpr -- Int AST
      := [ { `resVar⁻¹ { `x⁻¹ drop & `y⁻¹ nip } `var
           & `lam⁻¹ [dedfn] dip `lam
           & `var⁻¹ drop2 `var
           & `dfn⁻¹ `dfn
           & `ap⁻¹ [dup2] dip2 (243) [dedfn] dip3 (45) dedfn (32) `ap
           } ]
```

it would fail with


```
examples/ast.piz:65:65: occurs check failed: ‘'A’, ‘'A Int ρ₁’
```

We can define e.g. pretty-printers on AST variants without needlessly repeating
ourselves like so:


```{.pizarnik include="../examples/ast.piz" startLine=36 endLine=57}
```

Anything that works on a `DExpr` should work on an `AST`, which is the case:

```pizarnik
 0 "b" `name `var 0 "a" `name `var `ap 0 "a" `name `lam printAST
"λa (a)b"
 0 "b" `name `var 0 "a" `name `var `ap 0 "a" `name `lam printDExpr
"λa (a)b"
```

And supplying a `DExpr` to `printAST` is a type error, viz.

```pizarnik
 `x `resVar `dfn printAbs
1:12: ‘{ (ρ₁ ⊃ {`resVar: (ρ₁ ⊃ {`x})}) `dfn
       }’ is not an acceptable argument, expected
‘{a a `ap ⊕ a (ρ₂ ⊃ {`name: Int Str}) `lam ⊕ (ρ₁ ⊃ {`name: Int Str}) `var}’
"λa (a)b"
 `x `resVar `dfn printDExpr
"[x]"
```
