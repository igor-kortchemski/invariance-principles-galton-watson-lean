/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesNearStart
public import BGW.StableTrees.HeightBridgesAgeTail

/-!
# Uniform first-moment bound for the initial height occupation

The small-depth estimate cancels the cutoff normalization. The remaining integrated
survival tail vanishes with the initial age window.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Uniform first-moment control of the error from removing an initial age window. -/
theorem exists_lintegral_heightApprox_sub_shift_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t a : ℝ≥0), 0 < t → a + a ≤ t → ∀ ε : ℝ, 0 < ε →
      (∫⁻ e, ENNReal.ofReal
        |heightApprox ε e.path t - heightApprox ε (DLoc.shift a e.path) (t - a)|
          ∂(excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}) ≤
      ENNReal.ofReal (C * ((t : ℝ) / 2) ^ (-1 / θ)) *
        ∫⁻ s in Ioo (0 : ℝ) (a : ℝ),
          excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime} := by
  obtain ⟨C, hC, hbound⟩ := exists_excursion_small_depth_le hθ
  refine ⟨C, hC, fun t a ht haa ε hε => ?_⟩
  let μ := (excursionMeasure θ).restrict {e : Excursion | t < e.lifetime}
  have : IsFiniteMeasure μ := isFiniteMeasure_restrict.mpr
    (excursionMeasure_lifetime_slab_lt_top hθ ht).ne
  have hat : a ≤ t := (le_add_of_nonneg_right (show 0 ≤ a from zero_le)).trans haa
  have htR : 0 < (t : ℝ) := ht
  have hθpos : 0 < θ := zero_lt_one.trans hθ.1
  have hc : ENNReal.ofReal ε⁻¹ * ENNReal.ofReal (C * ε * ((t : ℝ) / 2) ^ (-1 / θ)) =
      ENNReal.ofReal (C * ((t : ℝ) / 2) ^ (-1 / θ)) := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr hε.le)]
    congr 1
    field_simp
  rw [lintegral_heightApprox_sub_shift μ ε hε t a hat]
  calc
    _ = ∫⁻ s in Ioo (0 : ℝ) (a : ℝ), ENNReal.ofReal ε⁻¹ *
        μ {e | e.path.1 s.toNNReal < futureInf e.path t s.toNNReal + ε} := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        restrict_Ioo_eq_restrict_Ico]
    _ ≤ ∫⁻ s in Ioo (0 : ℝ) (a : ℝ),
        ENNReal.ofReal (C * ((t : ℝ) / 2) ^ (-1 / θ)) *
          excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime} := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
      have hspos : 0 < s.toNNReal := Real.toNNReal_pos.mpr hs.1
      have hsa : s.toNNReal < a := by
        exact_mod_cast (show (s.toNNReal : ℝ) < a by
          rw [Real.coe_toNNReal _ hs.1.le]
          exact hs.2)
      have hst : s.toNNReal ≤ t := hsa.le.trans hat
      have hr : 0 < t - s.toNNReal := tsub_pos_iff_lt.mpr (hsa.trans_le hat)
      have hrge : (t : ℝ) / 2 ≤ ((t - s.toNNReal : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_sub hst, Real.coe_toNNReal _ hs.1.le]
        have haR : (a : ℝ) + a ≤ t := haa
        linarith only [haR, hs.2]
      have hpow : ((t - s.toNNReal : ℝ≥0) : ℝ) ^ (-1 / θ) ≤
          ((t : ℝ) / 2) ^ (-1 / θ) :=
        Real.rpow_le_rpow_of_nonpos (half_pos htR) hrge
          (div_nonpos_of_nonpos_of_nonneg (by norm_num : (-1 : ℝ) ≤ 0) hθpos.le)
      have hsmall := hbound s.toNNReal (t - s.toNNReal) ε hspos hr hε
      rw [add_tsub_cancel_of_le hst] at hsmall
      calc
        _ ≤ ENNReal.ofReal ε⁻¹ *
            (excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime} *
              ENNReal.ofReal (C * ε * ((t - s.toNNReal : ℝ≥0) : ℝ) ^ (-1 / θ))) :=
          mul_le_mul' le_rfl hsmall
        _ ≤ ENNReal.ofReal ε⁻¹ *
            (excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime} *
              ENNReal.ofReal (C * ε * ((t : ℝ) / 2) ^ (-1 / θ))) := by
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl
            (ENNReal.ofReal_le_ofReal
              (mul_le_mul_of_nonneg_left hpow (mul_nonneg hC hε.le))))
        _ = _ := by
          calc
            _ = (ENNReal.ofReal ε⁻¹ *
                ENNReal.ofReal (C * ε * ((t : ℝ) / 2) ^ (-1 / θ))) *
                excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime} := by ac_rfl
            _ = _ := congrArg (fun z : ℝ≥0∞ => z *
              excursionMeasure θ {e : Excursion | s.toNNReal < e.lifetime}) hc
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

end BGW.StableTrees
