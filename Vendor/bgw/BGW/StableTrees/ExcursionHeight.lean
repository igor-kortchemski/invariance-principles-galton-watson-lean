/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightPositivity
public import BGW.StableTrees.ExcursionHeightNormalization
public import BGW.StableTrees.ExcursionHeightUnitIdentification
public import BGW.StableTrees.ExcursionHeightTwo

/-!
# Continuous height of a stable excursion

This module exports the complete a.e.-age excursion-height interface. Host a.e.-time
agreement, predictable compensation of pre-start occupation and passage endpoint zeros give
simultaneous locality and non-junk. Compensation transfers existence and interior positivity
to the excursion measure. Surviving-age convergence identifies scaling before identification
at each real age. Unit prefix densities transfer raw scaling, and the shape/lifetime product
supplies the terminal trace. The common prefix graphs, unit scaling, normalization and the
variance-two Brownian identification use the same continuous reconstruction throughout.

## Additional public helpers in the endpoint/locality/scaling completion

* `measurable_excursionHeight_real_age`: Joint real-age evaluation of the continuous excursion
  height is measurable.
* `measurable_heightUniv_excursion_real_age`: Joint real-age evaluation of the universal excursion
  height is measurable.
* `ae_heightUniv_eq_excursionHeight_ages`: The universal height agrees with the continuous version
  on surviving age windows.
* `ae_tendsto_excursionHeight_ages`: Universal cutoffs converge to the continuous version on
  surviving age windows.
* `heightApprox_tendstoInMeasure_excursionHeight_ages`: Full-filter identification with the
  continuous height on each finite surviving-age window.
* `passageTime_tendsto_left`: On finite passages, the passage process tends to its finite left
  reading from the left.
* `ae_heightLoc_passageEndpoints_all`: Height vanishes at both passage readings simultaneously at
  all levels.
* `measurable_excursion_heightApprox`: Fixed-age excursion occupation approximations are
  measurable.
* `tendstoInMeasure_continuous_comp_filter`: Continuous real tests preserve convergence in measure
  along a countably generated filter.
* `exists_age_heightApprox_tendstoInMeasure_excursionHeight`: At least one deterministic positive
  age identifies the continuous excursion height.
* `map_excursionScale_survival`: Scaling carries a survival restriction to the scaled restriction,
  with the usual mass factor.
* `heightApprox_tendstoInMeasure_excursionHeight_dilate`: Good ages for full-filter continuous-
  height identification are preserved by dilation.
* `map_shiftAt_firstPassageBelow`: The post-passage centered path has the full local stable law at
  each fixed level.
* `futureInf_neg_of_regularBelowAtZero`: Regularity below zero implies a negative future infimum
  at every positive age.
* `ae_heightLoc_passageTime_fixed`: At every fixed passage level the continuous host height is
  zero almost surely.
* `heightWindowInf`: The infimum of a local path on a compact window.
* `heightWindowInf_le_eval`: A compact window infimum bounds each value in the window.
* `exists_heightWindow_ancestor`: A generalized minimum gives an ancestral contact in a compact
  window.
* `heightLoc_pos_of_ancestor_window`: The rational clock formulas exclude a zero continuous height
  above a positive ancestor.
* `heightWindowInf_cut`: Compact window infima commute with a valid excursion cut.
* `heightLoc_pos_of_window`: A compact minimum above a previous level forces a positive continuous
  height.
* `ae_jumpExcursion_height_pos`: Every host jump mark has strictly positive continuous height at
  every interior age.
* `measurableSet_excursionHeight_pos`: Strict positivity at every interior age is a Borel event of
  the excursion.
* `ae_positive_translate`: Translation by any nonnegative time preserves an a.e. property of
  positive real times.
* `heightApprox_eq_shift_of_past_min`: A centered shift with negative future infimum removes all
  sufficiently shallow old mass.
* `heightUniv_eq_shift_of_past_min`: Universal heights restart after a past minimum whenever the
  fresh infimum is negative.
* `heightLoc_zero_of_raw_restart`: A.e. raw restart and continuity identify the continuous height
  at the restart time.
* `ae_excursionHeight_scale_ages`: Fixed-scale height equality on each finite surviving excursion
  age window.
* `excursionHeight_scale_of_ae`: Almost-everywhere interior scale equality determines the two
  continuous heights everywhere.
* `futureInf_scaleLoc`: Positive stable scaling transports a future infimum on the corresponding
  time window.
* `heightApprox_scaleLoc`: The height occupation approximation obeys exact space-time scaling at
  every cutoff.
* `quasiMeasurePreserving_excursion_age_scale`: Joint age/mark dilation preserves null sets on the
  corresponding surviving age windows.
* `continuous_eq_iff_rat_toNNReal`: Equality of two continuous functions is determined by
  nonnegative rational ages.
* `measurableSet_excursionHeight_scale`: The all-age scaling event is jointly Borel in the scale
  and excursion.
* `ae_heightLoc_two_for_excursion`: **C26 (K17).**  At `θ = 2`, almost surely, the continuous
  height is `X - I` at every time.
* `continuous_eq_dLoc_iff_rat`: A continuous function and a càdlàg path agree everywhere iff they
  agree at rational ages.
* `measurableSet_excursionHeight_eq_path`: The all-age equality of the continuous height with the
  excursion path is Borel.
* `ae_tendsto_rescaled_heightUniv_ages`: Rescaled universal cutoffs converge at almost every
  surviving excursion age.
* `ae_tendsto_heightUniv_unit_of_prefix`: A convergent cutoff sequence with its universal-height
  limit transfers through prefix laws.
* `ae_age_tendsto_rescaled_heightUniv_unit`: At almost every unit age the rescaled cutoff sequence
  has the universal-height limit.
* `ae_heightUniv_scale_unit_ages`: Raw height scaling at almost every unit age, before choosing a
  unit continuous version.
* `isExcursionHeightVersion_scale_of_ae`: Scaling a continuous version gives a version when the
  raw scaling identity holds a.e.
* `exists_isExcursionHeightVersion_of_scale`: A version at a fixed scale pulls back whenever the
  raw heights obey the a.e.-age identity.
* `lifetimeLaw_ne_zero_of_height_index`: The positive lifetime mixing measure is nonzero for a
  valid stable index.
-/

@[expose] public section
