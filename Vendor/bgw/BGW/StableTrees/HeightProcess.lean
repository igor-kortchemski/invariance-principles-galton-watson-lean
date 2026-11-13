/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessBasic
public import BGW.StableTrees.HeightProcessErasure
public import BGW.StableTrees.HeightProcessIdentification
public import BGW.StableTrees.HeightProcessTwo
public import BGW.StableTrees.HeightProcessExploration
public import BGW.StableTrees.HeightProcessRecords
public import BGW.StableTrees.HeightProcessConcentration
public import BGW.StableTrees.HeightProcessSupport
public import BGW.StableTrees.HeightProcessContact
public import BGW.StableTrees.HeightProcessRoot
public import BGW.StableTrees.HeightProcessAncestral
public import BGW.StableTrees.HeightProcessAncestralSupport
public import BGW.StableTrees.HeightProcessRestartMeasure
public import BGW.StableTrees.HeightProcessRestartSource
public import BGW.StableTrees.HeightProcessRestartClock

/-!
# Height process and exploration measures

Public entry point for the height approximation, deterministic reversal, measurability,
erasure algebra, fixed-time occupation limits and the index-two normalization.
The exploration measure has no root atom simultaneously at every horizon.
Ancestral convergence, the Stieltjes bridge and ancestral support tops hold simultaneously.
Exploration restarts at fixed deterministic times by erasure and fresh concatenation.
The raw all-time gap-freeness claim is outside the contract.

## Public proof helpers

* `exists_rat_horizon_of_ancestor`: positive rational ancestor horizon.
* `ae_exploration_strict_or_jump`: source concentration with endpoint jumps.
* `futureInf_eq_before_ancestor`: equality before an ancestral time.
* `explorationStieltjes_restrict_before_ancestor`: equality of earlier source windows.
* `exploration_apply_before_ancestor`: exploration away from its endpoint height.
* `ae_exploration_support_ancestors_fixed`: support bounds for all fixed-horizon ancestors.
* `support_le_of_mass_above_zero`: support points lie below a mass-free tail.
* `topHeight_eq_of_support_bounds`: support bounds determine the top.
* `futureInf_restart_window`: old/fresh infimum decomposition.
* `reversedAt_apply`: pointwise reversal formula.
* `futureInf_bddBelow`: finite lower bound for interval infima.
* `futureInf_le_eval`: infimum bounds interval values.
* `futureInf_self`: terminal infimum value.
* `monotone_futureInf`: monotonicity in the starting time.
* `futureInf_eq_runningInf_shift`: centered running-infimum representation.
* `measurable_futureInf_uncurry`: joint infimum measurability.
* `supRunning_reversedAt_window`: reversed supremum at continuity times.
* `supReflected_reversedAt_window`: reversed reflection at continuity times.
* `ae_exploration_ancestral_times`: Stieltjes ancestral concentration.
* `ae_exploration_height_bounds`: fixed-horizon source height bounds.
* `ae_height_pos_fixed`: positivity at fixed positive times.
* `futureInf_zero_eq_runningInf`: root infimum representation.
* `ae_supLocalTime_pos_shiftAt`: positivity after finite stopping times.
* `supLocalTime_restart_of_contact`: clock restart at supremum contacts.
* `ae_clock_increases_after_passage`: growth after upward passages.
* `heightApprox_eq_supOccupation_reversed`: pathwise occupation reversal.
* `rawFiltration_le_restrict_comap`: prefix information contains the raw filtration.
* `measurable_supOccupation_prefix`: occupation prefix measurability.
* `measurable_supLocalTime_prefix`: clock prefix measurability.
* `ae_reversedAt_of_prefix`: transport of almost sure prefix events.
* `heightApprox_zero`: approximation at zero.
* `height_zero`: height at zero.
* `ae_reversed_clock_prefix`: continuous monotone reversed prefix clock.
* `supRunning_reversedAt_window_left`: supremum formula retaining endpoint jumps.
* `supReflected_reversedAt_eq_zero_of_ancestor`: reversed ancestral contacts.
* `supOccupation_prefix_add_const`: occupation under spatial translation.
* `supOccupation_reversedAt_shift`: occupation under earlier reversal.
* `height_ancestor_clock_identity`: ancestral height as a clock difference.
* `ae_height_ancestor_fixed`: simultaneous identification at a fixed horizon.
* `measurable_supLocalTime_prefix_eval`: joint clock/time prefix measurability.
* `ae_reversed_passage_clock_growth`: passage growth in reversed prefixes.
* `leftLim_supRunning_reversedAt`: reversed supremum left limits.
* `ae_zero_height_ancestor_inf`: fixed-horizon zero-height infimum level.
* `futureInf_split`: infimum decomposition at an intermediate time.
* `exists_rat_ancestor_of_jump`: rational horizons after jumps.
* `futureInf_zero_le_leftLim`: root infimum bounds positive-time left limits.
* `ae_zero_height_ancestor_inf_all`: simultaneous zero-height infimum levels.
* `ae_height_pos_at_jumps`: simultaneous positivity at upward jumps.
* `explorationStieltjes_no_atom_of_leftLim_eq`: absence of continuous endpoint atoms.
* `ae_supLadderHeight_increment_pos`: positive ladder-height increments.
* `ae_strictMono_supLadderHeight`: simultaneous strict ladder growth.
* `ae_supRunning_strict_of_clock_lt`: clock growth forces supremum growth.
* `ae_reversed_clock_strict_countable`: strict growth on countable reversed-prefix times.
* `ae_supLadderHeight_two_level`: index-two identity at a fixed ladder level.
* `ae_supLadderHeight_two`: simultaneous index-two ladder identity.
* `ae_supLocalTime_two`: index-two clock equals the supremum.
* `measurable_supRunning_prefix`: running-supremum prefix measurability.

## Restart proof helpers

The five generic `stieltjes_*` helpers below live in `BGW.Probability.Stieltjes`.

* `map_fresh_height_translation`: time and height pushforward composition.
* `map_eq_eraseMass_of_initial_cdf`: erasure from initial time distribution functions.
* `stieltjes_min_initial_cdf`: cumulative masses of a capped source, including atoms.
* `stieltjes_min_total`: surviving total mass, including complete erasure.
* `map_stieltjes_min_eq_eraseMass`: capped source under a monotone height map.
* `stieltjes_restrict_Ioc_congr`: agreement of source functions on a closed window.
* `stieltjes_min_restrict_le`: domination of the capped source by the original source.
* `map_stieltjes_min_eq_eraseMass_of_ae`: replacement by a source-almost-equal clock.
* `futureInf_shift_window`: infimum translation after a deterministic shift.
* `stieltjes_translate_window`: translation of restricted Stieltjes measures.
* `exploration_source_fresh`: translated fresh source measure.
* `exploration_source_split`: old/fresh source decomposition retaining the old endpoint.
* `topHeight_left_of_ordered_sum`: support top from ordered summands and gap-freeness.
* `exploration_fresh_source_map`: the fresh concatenation summand from height translation.
* `ae_exploration_old_source`: the old summand equals the erased exploration.
* `reversedAt_shift_prefix`: equality of the two fresh reversed windows.
* `supLocalTime_reversedAt_shift_prefix`: equality of their prefix clocks.
* `ae_exploration_source_clock`: source height as a common-clock difference.
* `exploration_source_order_bounds`: old/fresh source heights straddle the offset.
* `ae_topHeight_erased_exploration`: surviving support top equals the clock offset.
* `ae_exploration_fresh_height_translation`: fresh ancestral height translation.

-/

@[expose] public section
