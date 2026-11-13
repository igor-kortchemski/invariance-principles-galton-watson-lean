/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumStoppedEnergyConvergence

/-!
# Stopped energy estimates for supremum occupations

Finite-grid summation by parts and dominated convergence give the bounded stopped energy
estimate. Doob and Fatou transfer it to the finite auxiliary inverse clock. The terminal
mean and the full positive-filter stopped convergence statements follow from these moments.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
* O. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Springer, 2002, Chapter 7
  (Doob's inequality).
-/

@[expose] public section
