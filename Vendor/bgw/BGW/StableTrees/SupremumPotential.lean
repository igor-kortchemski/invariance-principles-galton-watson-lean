/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialCorrectionLimit
public import BGW.StableTrees.SupremumPotentialMomentBounds

/-!
# Supremum potential and reflected occupation resolvents

For a spectrally positive stable process of index `θ ∈ (1, 2]` reflected at its running
supremum, this module identifies the law of the supremum at an independent exponential clock
and derives the resulting potentials and resolvent bounds.

## Main results

* `stableScale`, `stableSeries`: the scale function and the `q`-scale series.
* `map_supRunning_expClockLaw`: the density of `S_{e_q}`, the supremum at an exponential clock.
* `supExpTail`, `supPotential`: the tail and the potential, with `Φ h_q(0) = q^{2/θ-1}`.
* `supOccupationResolvent_eq`: the reflected resolvent formula, with its uniform convergence
  (`tendstoUniformlyOn_supOccupationResolvent`).
* `supCorrection` and `abs_supCorrection_le`: the correction term and its bound.
* `condExp_reflectedResolvent_tail`, `resolventMarkov_supReflectedFrom`: the conditional
  resolvent identity and the resolvent Markov property.
* `integral_sq_discountedOccupation_supOccupation_le_two`: second-moment bounds.

The proofs combine the scale series (`SupremumPotentialBasic`), the density and potential
identities (`SupremumPotentialDensity`, `SupremumPotentialIdentity`), the occupation
convolution (`SupremumPotentialConvolution`) and the generic resolvent moment theorem.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VII.
* A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed., Springer,
  2014, Chapter 8 (scale functions).
* A. Kuznetsov, A. E. Kyprianou and V. Rivero, *The theory of scale functions for
  spectrally negative Lévy processes*, in *Lévy Matters II*, Lecture Notes in Math. 2061,
  Springer, 2012.
-/

@[expose] public section
