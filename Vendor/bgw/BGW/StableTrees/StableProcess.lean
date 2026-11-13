/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableProcessLaw
public import BGW.StableTrees.StableProcessNoNegativeJumps

/-!
# Stable process existence and functional convergence

The stable process law is the unique law with stable independent increments and zero initial
value. Every qualifying real walk converges to it, and its paths have no negative jumps.

## References

* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999,
  Theorems 13.1 and 13.2.
* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VIII.
* O. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Springer, 2002, Theorem 16.14.
-/

@[expose] public section
