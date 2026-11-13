/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ForestLocalLimitDefs
public import BGW.StableTrees.ForestLocalLimitWeights
public import BGW.StableTrees.ForestLocalLimitLocal
public import BGW.StableTrees.ForestLocalLimitTail
public import BGW.StableTrees.ForestLocalLimitResidue
public import BGW.StableTrees.ForestLocalLimitPrefix

/-!
# Periodic forest local limits and prefix weights

Canonical forest masses, tails and exact-prefix weights, together with periodic
local and tail limits, tree-tail asymptotics, the exact-prefix limit and generic
mass-one convergence tools. The periodic lattice factor is retained in local
limits and cancels in tail sums and exact-prefix weights.

## References

* J.-F. Le Gall, *Random trees and applications*, Probab. Surveys 2 (2005), Section 1.
* N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular Variation*, Cambridge
  University Press, 1987, Section 1.5 (Karamata's theorem).
* V. V. Petrov, *Sums of Independent Random Variables*, Springer, 1975, Chapter VII
  (local limit theorems).
-/

@[expose] public section
