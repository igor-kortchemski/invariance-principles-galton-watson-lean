/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionLifetimeTail
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

/-!
# Finite measures on surviving excursion age windows

The product of Lebesgue measure and the excursion measure is restricted to survival.
Its mass is finite because the lifetime tail has exponent `-1 / θ > -1` at zero.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

/-- The surviving excursion age window, with the survival restriction on the product measure. -/
noncomputable def heightExcursionAgeMeasure (θ : ℝ) (S : ℝ≥0) : Measure (ℝ × Excursion) :=
  ((volume.restrict (Ioo (0 : ℝ) (S : ℝ))).prod (excursionMeasure θ)).restrict
    {p | p.1.toNNReal < p.2.lifetime}

/-- Joint measurability of the survival event. -/
theorem measurableSet_heightExcursionAge_survival :
    MeasurableSet {p : ℝ × Excursion | p.1.toNNReal < p.2.lifetime} :=
  measurableSet_lt (measurable_real_toNNReal.comp measurable_fst)
    (measurable_excursion_lifetime.comp measurable_snd)

/-- The lifetime tail is integrable on each bounded interval starting at zero. -/
theorem lintegral_excursion_lifetime_tail_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (S : ℝ≥0) :
    (∫⁻ s in Ioo (0 : ℝ) (S : ℝ),
      excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime}) < ⊤ := by
  by_cases hS : S = 0
  · simp [hS]
  have hSpos : 0 < (S : ℝ) := by
    exact_mod_cast (pos_iff_ne_zero.mpr hS : 0 < S)
  have hθpos : 0 < θ := zero_lt_one.trans hθ.1
  have hp : -1 < -1 / θ := by
    rw [neg_div]
    have h := (div_lt_one hθpos).mpr hθ.1
    linarith
  have hG : 0 < Real.Gamma (1 - 1 / θ) :=
    Real.Gamma_pos_of_pos (sub_pos.mpr ((div_lt_one hθpos).mpr hθ.1))
  have hi : IntegrableOn
      (fun s : ℝ => s ^ (-1 / θ) / Real.Gamma (1 - 1 / θ)) (Ioo 0 S) :=
    ((intervalIntegral.integrableOn_Ioo_rpow_iff hSpos).mpr hp).div_const _
  have hnn : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) S),
      0 ≤ s ^ (-1 / θ) / Real.Gamma (1 - 1 / θ) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    exact div_nonneg (Real.rpow_nonneg hs.1.le _) hG.le
  have he : (∫⁻ s in Ioo (0 : ℝ) (S : ℝ),
      excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime}) =
      ∫⁻ s in Ioo (0 : ℝ) (S : ℝ),
        ENNReal.ofReal (s ^ (-1 / θ) / Real.Gamma (1 - 1 / θ)) := by
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have heq : {e : Excursion | s.toNNReal < e.lifetime} =
        {e : Excursion | s < (e.lifetime : ℝ)} := by
      ext e
      change s.toNNReal < e.lifetime ↔ s < (e.lifetime : ℝ)
      rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hs.1.le]
    rw [heq, excursionMeasure_lifetime_tail hθ s hs.1]
    congr 3
    ring
  rw [he, ← ofReal_integral_eq_lintegral_ofReal hi hnn]
  exact ENNReal.ofReal_lt_top

/-- Survival-restricted product age windows have finite mass. -/
theorem isFiniteMeasure_heightExcursionAgeMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (S : ℝ≥0) : IsFiniteMeasure (heightExcursionAgeMeasure θ S) := by
  have := sigmaFinite_excursionMeasure hθ
  constructor
  rw [heightExcursionAgeMeasure, Measure.restrict_apply_univ,
    Measure.prod_apply measurableSet_heightExcursionAge_survival]
  exact lintegral_excursion_lifetime_tail_lt_top hθ S

end BGW.StableTrees
