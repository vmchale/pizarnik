---
title: Concatenative and Applicative Languages, Negatives
author: V. E. McHale
date: 12 May 2026
---

Though concatenative languages may be clumsier than applicative languages in use, they are instructive: in the latter, order matters when applying the function but not when "unwrapping" context, e.g.

$$\lambda a.\lambda b. a-b$$

is different from

$$\lambda b. \lambda a. a-b$$

but access to (now) unbound variables
