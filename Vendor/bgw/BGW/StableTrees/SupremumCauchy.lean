/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCauchyLimit

/-!
# Resolvent Cauchy and maximal estimates

Compact Doob and occupation Cauchy estimates, a fast approximation sequence, almost sure
locally uniform convergence to its adapted raw limsup, and full-filter compact square-mean
convergence and square integrability of the auxiliary clock at each fixed time.

## Main results

* `occupationDiffMartingale`: the resolvent difference martingale, with its Doob bound
* `integral_sq_compactError_le`: explicit compact square-mean error estimate
* `supOccupation_compact_L2_cauchy`: compact-time Cauchy estimate
* `supAuxEps`: the fast approximation sequence
* `ae_tendsto_supOccupation_supAuxEps_uniform`: almost sure locally uniform convergence
* `supAuxLimit`, `ae_supAuxLimit_spec`: the limit and its almost sure properties
* `integrable_sq_supAuxLimit`: square integrability of the limit at each fixed time
* `supOccupation_compact_L2_tendsto_supAuxLimit`: compact square-mean convergence to the limit

## References

* [J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI]
* [R. M. Blumenthal and R. K. Getoor, *Markov Processes and Potential Theory*, Academic Press,
  1968, Chapter V]
-/

@[expose] public section
