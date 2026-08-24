---
title: Concatenative and Applicative Languages, Negatives
author: V. E. McHale
date: 12 May 2026
---

Though concatenative languages may be clumsier than applicative languages in use, they clarify negatives: in the latter, order matters when applying the function but not when "unwrapping" context, e.g.

$$\lambda a.\lambda b. \frac{a}{b}$$

is different from

$$\lambda b. \lambda a. \frac{a}{b}$$

but how one accesses (now un)bound variables does not depend on the order in
which contexts were unwrapped.

<!-- interestingly, pattern-matching is sequential when one includes e.g. wildcards... https://ats-lang.sourceforge.net/DOCUMENT/INT2PROGINATS/HTML/x2795.html -->
