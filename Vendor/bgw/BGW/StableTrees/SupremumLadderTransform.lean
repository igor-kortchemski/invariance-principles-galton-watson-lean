/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformPotential
public import BGW.StableTrees.SupremumLadderTransformExact

/-!
# Boundary potential and ascending ladder Laplace functional

The boundary potential identifies the ladder semigroup rate exactly as `supLadderExponent`,
with normalization one, at all nonnegative parameters. The proof uses cumulative Tonelli,
compact square-mean occupation error and half-rate tail bounds.

## Public helpers

* `lintegral_tail_eq_lintegral_cumulative`: Tonelli for a measure tail.
* `pathStieltjes_lintegral_tail`: cumulative representation for a continuous clock.
* `pathStieltjes_lintegral_decreasing`: representation for a Stieltjes tail weight.
* `map_inverse_eq_pathStieltjes`: inverse pushforward of positive-level volume.
* `aemeasurable_supBoundaryPotential`: boundary measurability through inverse substitution.
* `integrable_exp_neg_supLadder`: integrability of the bounded ladder exponential.
* `supWeightStieltjes`: Stieltjes function of the negative boundary weight.
* `supWeightStieltjes_measure_Ioi`: exact positive-time weight tails.
* `supWeightStieltjes_measure_Ioi_le`: tail domination by the pure time discount.
* `pathStieltjes_lintegral_supWeight`: cumulative representation of the weighted clock.
* `lintegral_clock_le_of_tail_le`: cumulative bound from a bound on weight tails.
* `lintegral_clock_tail_le`: half-rate estimate for the cumulative tail.
* `integrable_clock_and_integral_tail_le`: finite real cumulative integrals and tail bound.
* `abs_integral_clock_sub_le`: compact error plus half-rate tails for two clocks.
* `lintegral_supOccupation_tail`: occupation Stieltjes integrals as time integrals.
* `lintegral_supOccupation_supWeight`: weighted occupation as its ordinary kernel integral.
* `integrable_of_lintegral_eq_ofReal`: finiteness criterion for a nonnegative integral.
* `integral_exp_supOccupation_clock`: real occupation-clock exponential integral.
* `integral_supWeight_eq_cumulative`: finite real weighted cumulative representation.
* `supWeightedOccupation`: the ordinary weighted occupation integral.
* `measurable_supWeightedOccupation`: measurability of weighted occupation.
* `integrableOn_supWeightedKernel`: pathwise weighted-kernel integrability and domination.
* `integrable_supWeightedOccupation`: integrability under the stable path law.
* `ae_integrable_aux_clock_exp`: almost sure finiteness of an auxiliary clock potential.
* `supWeightedOccupation_eq_cumulative`: common cumulative occupation representation.
* `ae_supBoundaryPotential_cumulative`: finite cumulative boundary representative.
* `integrable_supBoundaryPotential_toReal`: integrability of the real boundary potential.
* `ae_abs_supWeightedOccupation_sub_le`: pathwise compact and tail approximation bound.
* `integral_abs_supWeightedOccupation_sub_le`: corresponding mean bound.
* `tendsto_integral_abs_supWeightedOccupation_sub`: full positive-filter convergence in mean.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VI (ladder
  processes) and VII.1.
* A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed., Springer,
  2014, Chapter 6 (Wiener–Hopf factorization).
-/

@[expose] public section
