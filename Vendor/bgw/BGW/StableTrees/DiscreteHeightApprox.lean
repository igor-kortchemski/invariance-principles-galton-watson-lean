/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxHeightLimit

/-!
# Discrete height approximation and weak-cycle estimates

Finite-time reversal identifies forest heights and occupations with weak ascending
records and reflected bands. Pre-return duality gives exact mean one at each gap
level and almost surely finite weak epochs. Stopped restart gives iid cycles.

The killed-gap Green diagonal equals the weak ladder renewal function. The ladder
height tail law, its generating transform and the normalized offspring PGF gap give
a scale-uniform second moment, including infinite-variance Gaussian domains.

The maximal inequality and the adjacent-cycle sandwich control the stopped error,
with an explicitly reserved extra cycle. Ladder-height exponential tails remove the
cutoff. Reversal then gives the two-limit discrete occupation estimate.

Window infima are J1-continuous at paths continuous at their endpoints. Dominated
convergence gives occupation continuity outside null boundary levels; these levels
fail for at most countably many bands under the stable law. The exact mesh identity
has only a final-cell error bounded by `1/(n ε)`. Continuous mapping therefore gives
fixed-band joint walk/occupation convergence.

Choosing bands tending to zero outside the exceptional set and applying the
approximation theorem identifies the joint walk/height finite-dimensional limit.
At index two, the sealed height identity gives `X_t - I_t`, with constant one.
-/

@[expose] public section
