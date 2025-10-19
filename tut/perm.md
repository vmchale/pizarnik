% Permutations in Stack Programming
% V. E. McHale
% 19 Oct. 2025

`dip`, `drop`, `dup`, and `swap` are sufficient to perform any manipulations,
but permutation literals (using cycle notation) may be more agreeable.

Consider:

```pizarnik
rot : a b c -- b c a
    := [ [swap] dip swap ]
```

This is a shuffle word in [Factor](https://docs.factorcode.org/content/article-shuffle-words.html).

```pizarnik
rot : a b c -- b c a
    := [ (123) ]
```

It is hardly worth naming when we have permutation literals! Indeed, `swap` can
be defined like so:

```pizarnik
swap : a b -- b a
     := [ (12) ]
```
