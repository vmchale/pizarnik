% Solving the Expression Problem
% V. E. McHale
% 14 Nov. 2025

Suppose we have

```{.pizarnik include="../lib/either.piz" startLine=3 endLine=8}
```

Then we can define

```{.pizarnik include="../lib/both.piz" startLine=4 endLine=4}
```

<!-- makes sense that "first-class left" ig -->

We can extend `mapLeft`, viz.

```{.pizarnik include="../lib/both.piz" startLine=10 endLine=14}
```

`mapL` accepts a value of type `Either(a,b)` as argument:

```{.pizarnik include="../test/data/both.piz" startLine=6 endLine=7}
```

Functions defined for `Either(a,b)` do not need to be rewritten and they do not
compromise safety.

```{.pizarnik include="../test/data/both.piz" startLine=12 endLine=13}
```

```
{Bool `left ⊕ Int `right ⊕ Bool Int `both} ⊀ {Bool `left ⊕ Int `right}
```

Pattern matching is different from a function returning values: it is a
disjunctive product. By distinguishing polarity, i.e. disjunctions as arguments
vs. return values, we get first-class patterns. Both the "left" and "right"
aspects are reusable, can be named.

In a similar vein, we can define

```{.pizarnik include="../lib/both.piz" startLine=7 endLine=8}
```

which can be thought of as an or-pattern binding a variable.
