---
title: Error Hierarchies
author: V. E. McHale
date: 24 March 2026
---

A [common situation](https://gist.github.com/nkpart/c3bcb48c97c5ded6e277):
suppose various parts of a program can fail in specific, overlapping ways.


```{.pizarnik include="../test/examples/errorHierarchy.piz"}
```

With `tyE` we can raise a `` `scope`` error while typechecking. `handleRewrite`
allows us to (locally) handle a `` `scope`` error without being forced to handle
a `` `unificationFailed`` where it will not occur.

Since `handleTypeError` is inexhaustive, however, we are faced with:

```
test/examples/errorHierarchy.piz:13:19: {`scope ⊕ `unificationFailed} ⊀ (ρ₁ ⊃ {`scope})
```

Thus our scheme is safe; with extensible cases, we do not need to resort to the
lens kludge.

<!-- lenses... gödel counter-witnesses?? hmm -->
