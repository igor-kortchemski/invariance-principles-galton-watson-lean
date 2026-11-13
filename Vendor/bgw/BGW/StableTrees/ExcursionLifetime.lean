/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionLifetimeDensity
public import BGW.StableTrees.Scalar.Density
import Mathlib.Analysis.SpecialFunctions.Gamma.Beta

/-! # Lifetime law, normalization and scaling of the excursion measure

For the spectrally positive `θ`-stable process (`1 < θ ≤ 2`) reflected at its infimum, with Itô
excursion measure `N = excursionMeasure θ` and `α = 1/θ`:

* `lintegral_one_sub_exp_lifetime`: `∫ (1 - e^{-qζ}) dN = q^α` (Laplace exponent of the passage
  subordinator);
* `excursionMeasure_lifetime_tail`: `N(ζ > t) = t^{-α} / Γ(1 - α)`;
* `excursionMeasure_lifetime_density`: the lifetime image of `N` has density
  `α / Γ(1 - α) · t^{-1-α}`;
* `stableDensity_zero_eq_inv_theta_gamma`: the stable density at `0` equals `α / Γ(1 - α)`;
* `map_excursionScale_excursionMeasure`: `(S_c)_* N = c^α • N`.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VIII.
* A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed., Springer, 2014,
  Chapters 6 and 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Normalization bridge**: `d_θ(0) = 1 / (θ Γ(1 - 1/θ))` (the coefficient `α/Γ(1-α)`
of the Lévy density equals the stable density at `0`). -/
theorem stableDensity_zero_eq_inv_theta_gamma {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Scalar.stableDensity θ 0 = 1 / (θ * Real.Gamma (1 - 1 / θ)) := by
  have hθ0 : 0 < θ := lt_trans zero_lt_one hθ.1
  have ha : 0 < 1 / θ := one_div_pos.mpr hθ0
  have ha1 : 1 / θ < 1 := (div_lt_one hθ0).mpr hθ.1
  have hs : 0 < Real.sin (Real.pi * (1 / θ)) :=
    Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos ha)
      (by nlinarith [Real.pi_pos])
  have hg := Real.Gamma_mul_Gamma_one_sub (1 / θ)
  have hg' : Real.Gamma (1 / θ) * Real.Gamma (1 - 1 / θ) *
      Real.sin (Real.pi * (1 / θ)) = Real.pi :=
    (eq_div_iff hs.ne').mp hg
  have hb : Real.Gamma (1 - 1 / θ) ≠ 0 :=
    (Real.Gamma_pos_of_pos (sub_pos.mpr ha1)).ne'
  rw [Scalar.stableDensity_zero hθ, Real.Gamma_add_one ha.ne']
  rw [show Real.pi / θ = Real.pi * (1 / θ) by ring]
  apply (eq_div_iff (mul_ne_zero hθ0.ne' hb)).mpr
  field_simp at hg' ⊢
  nlinarith [hg']

end BGW.StableTrees
