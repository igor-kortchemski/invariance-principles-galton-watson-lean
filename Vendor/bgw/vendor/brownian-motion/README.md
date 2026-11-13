# Brownian construction source slice

Apache-2.0 source extracted from
[RemyDegenne/brownian-motion](https://github.com/RemyDegenne/brownian-motion/tree/497e5e2a60450796f75ab920e6c33addae4d644d).
Only the non-Mathlib import closure of `BrownianMotion.Gaussian.BrownianMotion` is included.
Authors and copyright notices are preserved in each file.

The local package configuration omits unrelated tooling dependencies. Compatibility with
our pinned Mathlib is maintained by the adjacent Kolmogorov package and one API adaptation
in `Continuity/KolmogorovChentsov.lean` (a redundant `.aemeasurable` is removed).
The reflection file containing an unfinished theorem is outside this extracted source slice.
