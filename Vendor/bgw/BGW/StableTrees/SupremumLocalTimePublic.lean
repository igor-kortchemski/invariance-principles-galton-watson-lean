/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTime
public import BGW.StableTrees.SupremumLocalTimeIdent
public import BGW.StableTrees.SupremumLadderRestart
public import BGW.StableTrees.SupremumLadderTransform
public import BGW.StableTrees.SupremumLocalTimeStopped

/-!
# Public local time at the supremum and ascending ladder processes

For the spectrally positive `θ`-stable process (`1 < θ ≤ 2`), this entry point collects the
local time at the running supremum, constructed as the almost sure limit of the occupation
approximations `ε⁻¹ Leb{s ≤ t : S_s − X_s < ε}` along a deterministic sequence, its inverse, the
ascending ladder time and height processes, their exact Wiener–Hopf transform
`E exp(−q A_z − λ B_z) = exp(−z (q − λ^θ)/(q^{1/θ} − λ))`, the restart identity at ladder times and
stopped `L²` estimates. All modules below are in `BGW.StableTrees` and are reexported here.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV, VI and VII.
* T. Duquesne and J.-F. Le Gall, *Random Trees, Lévy Processes and Spatial Branching Processes*,
  Astérisque 281 (2002), Section 1.1.

## Declarations and their homes

* `supRunning`: `SupremumLocalTime`.
* `supReflected`: `SupremumLocalTime`.
* `supOccupation`: `SupremumLocalTime`.
* `IsSupOccupationSeq`: `SupremumLocalTime`.
* `exists_isSupOccupationSeq`: `SupremumLocalTimeIdentBasic`.
* `supEps`: `SupremumLocalTimeIdentBasic`.
* `isSupOccupationSeq_supEps`: `SupremumLocalTimeIdentBasic`.
* `supLocalTime`: `SupremumLocalTimeIdentBasic`.
* `measurable_supLocalTime_uncurry`: `SupremumLocalTimeIdentBasic`.
* `ae_tendsto_supOccupation`: `SupremumLocalTimeIdentBasic`.
* `ae_tendsto_supOccupation_uniform`: `SupremumLocalTimeIdentUniform`.
* `supOccupation_tendstoInMeasure`: `SupremumLocalTimeIdentPath`.
* `ae_supLocalTime_spec`: `SupremumLocalTimeIdentPath`.
* `supLocalTimeStieltjes`: `SupremumLocalTimeIdentPath`.
* `ae_supLocalTimeStieltjes_support`: `SupremumLocalTimeIdentPath`.
* `ae_supLocalTime_const_of_lt`: `SupremumLocalTimeIdentPath`.
* `stronglyAdapted_supLocalTime`: `SupremumLocalTimeIdentBasic`.
* `measurable_supLocalTime`: `SupremumLocalTimeIdentBasic`.
* `supLocalTimeInverse`: `SupremumLocalTimeIdentInverse`.
* `supLadderTime`: `SupremumLocalTimeIdentInverse`.
* `supLadderHeight`: `SupremumLocalTimeIdentInverse`.
* `measurable_supLadder_uncurry`: `SupremumLocalTimeIdentInverse`.
* `ae_supLadder_spec`: `SupremumLocalTimeIdent`.
* `supLadderExponent`: `SupremumLocalTime`.
* `integral_exp_neg_supLadder`: `SupremumLadderTransformExact`.
* `exists_isStoppingTime_supLocalTimeInverse`: `SupremumLocalTimeIdentInverse`.
* `ae_supRestart_at_ladderTime`: `SupremumLadderRestart`.
* `supOccupation_stopped_L2_bound`: `SupremumLocalTimeStopped`.
* `supOccupation_stopped_L2_tendsto`: `SupremumLocalTimeStopped`.
* `supOccupation_stopped_uniform_tendstoInMeasure`: `SupremumLocalTimeStopped`.
-/

@[expose] public section
