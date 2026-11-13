/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Scalar.WalkVector
public import BGW.LocallyFinite.ForestWalkLaw

/-!
# The scalar convolution law in Kemperman's forest identity

The existing forest weights and offspring-count product law agree with the
scalar convolution walk. The multiplied identity holds for `ℓ ≥ 1` and every
time `n`; division by `n` is restricted to positive times. No criticality or
lattice assumption is needed.

The scalar form adapts `PoissonDeclumping/Bridge/Kemperman.lean` in
`igor-kortchemski/rare-subtree-patterns`, commit
`fc5ef722392b1af41e8b9d5fc45d5a521b7823dd` (Apache-2.0), using the forest
identity already proved in `BGW.LocallyFinite.ForestWalkLaw`.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace BGW.StableTrees.Scalar

/-- An endpoint `-ℓ` in the convolution walk is the existing count-bridge event. -/
theorem walkLaw_neg_eq_pi_countForestBridges (μ : PMF ℕ) (ℓ n : ℕ) :
    walkLaw μ n {-(ℓ : ℤ)} =
      Measure.pi (fun _ : Fin n => μ.toMeasure) (BGW.countForestBridges ℓ n) := by
  rw [walkLaw_eq_map_offspring_sum,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)]
  congr 1
  ext ω
  change (∑ i : Fin n, ((ω i : ℤ) - 1)) = -(ℓ : ℤ) ↔ ∑ i, ω i + ℓ = n
  have hsum : (∑ i : Fin n, ((ω i : ℤ) - 1)) = ((∑ i, ω i : ℕ) : ℤ) - n := by
    simp [Finset.sum_sub_distrib]
  rw [hsum]
  omega

/-- Kemperman's identity with the scalar convolution law, including time zero. -/
theorem natCast_mul_forestWeight_eq_walkLaw (μ : PMF ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (n : ℕ) :
    (n : ℝ≥0∞) * BGW.forestWeight μ ℓ n =
      (ℓ : ℝ≥0∞) * walkLaw μ n {-(ℓ : ℤ)} := by
  rw [walkLaw_neg_eq_pi_countForestBridges]
  simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using
    BGW.natCast_mul_forestWeight_eq_pi μ.toMeasure hℓ n

/-- Real-valued Kemperman identity; no division by time is performed. -/
theorem natCast_mul_forestWeight_toReal (μ : PMF ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (n : ℕ) :
    (n : ℝ) * (BGW.forestWeight μ ℓ n).toReal =
      ℓ * walkProb μ n (-(ℓ : ℤ)) := by
  have h := congrArg ENNReal.toReal (natCast_mul_forestWeight_eq_walkLaw μ hℓ n)
  rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_natCast] at h
  have hp : walkProb μ n (-(ℓ : ℤ)) = (walkLaw μ n {-(ℓ : ℤ)}).toReal := by
    simp [walkProb, measureReal_def]
  rw [hp]
  exact h

/-- The divided forest formula is restricted to positive times. -/
theorem forestWeight_toReal_eq (μ : PMF ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {n : ℕ} (hn : 1 ≤ n) :
    (BGW.forestWeight μ ℓ n).toReal = ℓ / n * walkProb μ n (-(ℓ : ℤ)) := by
  have h := natCast_mul_forestWeight_toReal μ hℓ n
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp
  linarith

end BGW.StableTrees.Scalar
