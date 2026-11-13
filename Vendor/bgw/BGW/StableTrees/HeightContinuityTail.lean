/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightContinuityBasic
import BGW.StableTrees.HeightBridgesCompact
import BGW.StableTrees.StableLocalMarkov
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# Increment tails without height continuity

The ladder-time transform bounds a fresh height. The erasure decomposition bounds the
negative increment separately, yielding a uniform exponential bound on the absolute increment.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The ladder-time transform bounds the tail of the supremum clock. -/
theorem measure_supLocalTime_gt_le_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s : ℝ≥0) (v : ℝ≥0) {q : ℝ} (hq : 0 ≤ q) :
    (stableLocalLaw θ : Measure DLoc) {f | (v : ℝ) < supLocalTime θ f s} ≤
      ENNReal.ofReal (Real.exp (q * s - (v : ℝ) * q ^ (1 - 1 / θ))) := by
  let A (f : DLoc) : ℝ := supLadderTime θ v f
  have hA : Measurable A := measurable_coe_nnreal_real.comp
    ((measurable_supLadder_uncurry θ).1.comp (measurable_const.prodMk measurable_id))
  have hF : Measurable (fun f => ENNReal.ofReal (Real.exp (q * s - q * A f))) :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.sub (measurable_const.mul hA)))
  have hb := meas_le_lintegral₀ (μ := (stableLocalLaw θ : Measure DLoc))
    hF.aemeasurable (s := {f | (v : ℝ) < supLocalTime θ f s}) (by
      intro f hf
      have hinv : supLocalTimeInverse θ f v ≤ (s : WithTop ℝ≥0) :=
        sInf_le ⟨s, rfl, hf⟩
      have hAs : A f ≤ (s : ℝ) := by
        exact_mod_cast WithTop.untopD_le hinv
      rw [ENNReal.one_le_ofReal]
      exact Real.one_le_exp (by nlinarith only [hq, hAs]))
  have hi : Integrable (fun f => Real.exp (-q * A f))
      (stableLocalLaw θ : Measure DLoc) := by
    simpa only [zero_mul, sub_zero] using
      integrable_exp_neg_supLadder hθ hq (le_refl (0 : ℝ)) v
  calc
    _ ≤ ∫⁻ f, ENNReal.ofReal (Real.exp (q * s - q * A f))
        ∂(stableLocalLaw θ : Measure DLoc) := hb
    _ = ENNReal.ofReal (Real.exp (q * s)) *
        ∫⁻ f, ENNReal.ofReal (Real.exp (-q * A f))
          ∂(stableLocalLaw θ : Measure DLoc) := by
      simp_rw [sub_eq_add_neg, Real.exp_add, ENNReal.ofReal_mul (Real.exp_nonneg _),
        neg_mul]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = _ := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => Real.exp_nonneg _),
        (integral_exp_neg_supLadder hθ v hq (le_refl (0 : ℝ))).2.1,
        ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring

/-- Fixed-time reversal gives the same height and supremum-clock laws. -/
theorem map_height_eq_map_supLocalTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {s : ℝ≥0} (hs : 0 < s) :
    (stableLocalLaw θ : Measure DLoc).map (fun f => height θ f s) =
      (stableLocalLaw θ : Measure DLoc).map (fun f => supLocalTime θ f s) := by
  let M (g : D (s : ℝ) ℝ) : ℝ := supLocalTime θ (horizonExtension s g) s
  have hM : Measurable M := (measurable_supLocalTime θ s).comp
    (measurable_horizonExtension s)
  have he (f : DLoc) : M (DLoc.restrict s f) = supLocalTime θ f s :=
    (measurable_supLocalTime_prefix θ s).factorsThrough (restrict_horizonExtension s _)
  have hr : Measurable (fun f : DLoc => DLoc.restrict s (reversedAt s f)) :=
    (DLoc.measurable_restrict s).comp (measurable_reversedAt_uncurry.comp
      (measurable_const.prodMk measurable_id))
  have h := congrArg (fun μ : Measure (D (s : ℝ) ℝ) => μ.map M)
    (map_restrict_reversedAt_stableLocalLaw hθ hs)
  rw [Measure.map_map hM hr, Measure.map_map hM (DLoc.measurable_restrict s)] at h
  simpa only [Function.comp_def, he, height] using h

/-- The fixed-time height has an exponential tail on its stable scale. -/
theorem measure_height_gt_le_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s : ℝ≥0) (hs : 0 < s) (v : ℝ) (hv : 0 ≤ v) :
    (stableLocalLaw θ : Measure DLoc) {f | v < height θ f s} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(v * (s : ℝ) ^ (-(1 - 1 / θ))))) := by
  have hm := measurable_height_fixed θ s
  have hM : Measurable (fun f : DLoc => supLocalTime θ f s) := measurable_supLocalTime θ s
  have he : (stableLocalLaw θ : Measure DLoc) {f | v < height θ f s} =
      (stableLocalLaw θ : Measure DLoc) {f | v < supLocalTime θ f s} := by
    calc
      _ = ((stableLocalLaw θ : Measure DLoc).map (fun f => height θ f s)) (Ioi v) :=
        (Measure.map_apply hm measurableSet_Ioi).symm
      _ = _ := by rw [map_height_eq_map_supLocalTime hθ hs,
        Measure.map_apply hM measurableSet_Ioi]; rfl
  rw [he]
  have hb := measure_supLocalTime_gt_le_exp hθ s v.toNNReal
    (q := (s : ℝ)⁻¹) (inv_nonneg.mpr s.2)
  have hsreal : 0 < (s : ℝ) := hs
  have hc : (↑s)⁻¹ * (s : ℝ) = 1 := inv_mul_cancel₀ hsreal.ne'
  rw [hc] at hb
  simpa only [Real.coe_toNNReal _ hv, ← Real.rpow_neg_eq_inv_rpow,
    sub_eq_add_neg, Real.exp_add] using hb

/-- Absolute height increments have uniform exponential tails, using erasure only. -/
theorem measure_height_increment_gt_le_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t s : ℝ≥0) (hs : 0 < s) (v : ℝ) (hv : 0 ≤ v) :
    (stableLocalLaw θ : Measure DLoc) {f | v < |height θ f (t + s) - height θ f t|} ≤
      ENNReal.ofReal (2 * Real.exp 1 *
        Real.exp (-(v * (s : ℝ) ^ (-(1 - 1 / θ))))) := by
  let P : Measure DLoc := stableLocalLaw θ
  let K (f : DLoc) : ℝ := topHeight (eraseMass
    (ENNReal.ofReal (-(futureInf (DLoc.shift t f) s 0))) (exploration θ f t))
  have hA : P {f | v < height θ (DLoc.shift t f) s} ≤
      ENNReal.ofReal (Real.exp 1 * Real.exp (-(v * (s : ℝ) ^ (-(1 - 1 / θ))))) := by
    have hmheight := measurable_height_fixed θ s
    have hm : MeasurableSet {f : DLoc | v < height θ f s} :=
      measurableSet_lt measurable_const hmheight
    calc
      _ = (P.map (DLoc.shift t)) {f | v < height θ f s} :=
        (Measure.map_apply (DLoc.measurable_shift_fixed t) hm).symm
      _ ≤ _ := by
        rw [map_shift_stableLocalLaw hθ t]
        exact measure_height_gt_le_exp hθ s hs v hv
  have hB := erased_height_tail_le hθ t s hs v hv
  calc
    _ ≤ P ({f | v < height θ (DLoc.shift t f) s} ∪ {f | v < height θ f t - K f}) := by
      apply measure_mono_ae
      filter_upwards [ae_height_erasure_decomposition hθ t s] with f hf
      intro hh
      change v < |height θ f (t + s) - height θ f t| at hh
      change 0 ≤ K f ∧ K f ≤ height θ f t ∧
        height θ f (t + s) = K f + height θ (DLoc.shift t f) s at hf
      rcases lt_abs.mp hh with hh | hh
      · apply Or.inl
        change v < height θ (DLoc.shift t f) s
        linarith only [hh, hf.2.1, hf.2.2]
      · apply Or.inr
        change v < height θ f t - K f
        have hn : 0 ≤ height θ (DLoc.shift t f) s := by
          unfold height supLocalTime
          have hn (k : ℕ) : 0 ≤ supOccupation (supEps θ k)
              (reversedAt s (DLoc.shift t f)) s :=
            mul_nonneg (inv_nonneg.mpr (supEps_pos θ k).le) ENNReal.toReal_nonneg
          rw [limsup_eq_toReal_of_nonneg hn]
          exact ENNReal.toReal_nonneg
        linarith only [hh, hf.2.2, hn]
    _ ≤ P {f | v < height θ (DLoc.shift t f) s} + P {f | v < height θ f t - K f} :=
      measure_union_le _ _
    _ ≤ _ := by
      have hsum := add_le_add hA hB
      calc
        _ ≤ _ := hsum
        _ = _ := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          congr 1
          ring

end BGW.StableTrees
