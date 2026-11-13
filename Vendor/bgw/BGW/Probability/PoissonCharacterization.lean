/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.Probability.PoissonCharacterizationCompensation
public import BGW.Probability.PoissonCharacterizationLaw
public import BGW.Probability.PoissonCharacterizationLimit

/-! Characterization of time-simple random point measures with stationary independent increments.

Finite-rate mark sets have finite intensity, disjoint boxes have independent Poisson counts, and
natural-history compensation holds. The joint complex generating function is proved by integrating
a linear remainder estimate over a uniform time grid; intersecting the cells with the boxes handles
arbitrary endpoints without a separate time-refinement argument.

The namespace is `BGW.StableTrees` because this characterization serves the excursion theory of
the stable process.

## References

* O. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Springer, 2002, Chapter 12
  (Poisson and pure jump-type Markov processes; characterization of Poisson processes).
* K. Sato, *Lévy Processes and Infinitely Divisible Distributions*, Cambridge University Press,
  1999, Chapter 1. -/

@[expose] public section

