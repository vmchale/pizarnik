% Solving the Expression Problem
% V. E. McHale
% 14 Nov. 2025

Suppose we have

```{.pizarnik include="../lib/either.piz" startLine=3 endLine=8}
```

Then we can define

```{.pizarnik include="../lib/both.piz" startLine=4 endLine=4}
```

We can extend `mapLeft`, viz.

```{.pizarnik include="../lib/both.piz" startLine=10 endLine=14}
```

`mapL` accepts a value of type `Either(a,b)` as argument:

```{.pizarnik include="../test/data/both.piz" startLine=6 endLine=10}
```

Functions defined for `Either(a,b)` do not need to be rewritten and they do not
compromise safety.

```{.pizarnik include="../test/data/both.piz" startLine=12 endLine=13}
```

```
{Bool `left ⊕ Int `right ⊕ Bool Int `both} ⊀ {Bool `left ⊕ Int `right}
```

Pattern matching is different from a function returning values: it is a
disjunctive product. By accounting for polarity, i.e. argument
vs. return value, we get extensible pattern matching. Both the "left" and "right"
aspects are first-class.

To wit, we can define

```{.pizarnik include="../lib/both.piz" startLine=7 endLine=8}
```

which can be thought of as an or-pattern binding a variable.

As Wadler [-@expression] puts it,

> One can think of cases as
> rows and functions as columns in a table. In a functional language,
> the rows are fixed (cases in a datatype declaration) but it is easy to
> add new columns (functions).  In an object-oriented language, the
> columns are fixed (methods in a class declaration) but it is easy to
> add new rows (subclasses).  We want to make it easy to add either rows
> or columns.

Polarity, wherein argument and return value are dual (De Morgan laws for
disjunctive product (pattern match, argument) and disjunctive sum (return value))
frames the expression problem.

# Reference
