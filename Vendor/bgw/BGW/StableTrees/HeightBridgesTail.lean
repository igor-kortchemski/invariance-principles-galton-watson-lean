/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesBarrier
public import BGW.StableTrees.HeightBridgesLadderBound

/-!
# Exponential erased-height tail

The ancestral source bounds erasure by a passage-stopped reversed clock. Rational clock
barriers transfer with an independent fresh depth to the stable product law, where the full
ladder transform bounds them. The constant extension of the reversal is never given the
full stable law, and continuity of the height process is not used.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Erased-height tail.**  PROOF REQUIREMENT: use an independent fresh depth and a
stopped/full ladder bound, without height continuity; reversal is constant after `t`, so its
unrestricted ladder height is not an independent full stable process. -/
theorem erased_height_tail_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t r : ℝ≥0) (hr : 0 < r) (v : ℝ) (hv : 0 ≤ v) :
    (stableLocalLaw θ : Measure DLoc)
      {f | v < height θ f t -
        (topHeight (eraseMass
          (ENNReal.ofReal (-(futureInf (DLoc.shift t f) r 0)))
          (exploration θ f t)) : ℝ)} ≤
    ENNReal.ofReal (Real.exp 1 *
      Real.exp (-(v * (r : ℝ) ^ (-(1 - 1 / θ))))) := by
  by_cases ht : t = 0
  · subst t
    have hempty : {f : DLoc | v < height θ f 0 -
        (topHeight (eraseMass
          (ENNReal.ofReal (-(futureInf (DLoc.shift 0 f) r 0)))
          (exploration θ f 0)) : ℝ)} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro f hf
      change v < height θ f 0 -
        (topHeight (eraseMass (ENNReal.ofReal (-(futureInf (DLoc.shift 0 f) r 0)))
          (exploration θ f 0)) : ℝ) at hf
      rw [height_zero] at hf
      have hn := NNReal.coe_nonneg (topHeight (eraseMass
        (ENNReal.ofReal (-(futureInf (DLoc.shift 0 f) r 0))) (exploration θ f 0)))
      linarith only [hv, hf, hn]
    rw [hempty, measure_empty]
    exact zero_le
  have htpos : 0 < t := pos_iff_ne_zero.mpr ht
  let P : Measure DLoc := stableLocalLaw θ
  have hbarrier : (P.prod P) (erasedClockBarrier θ t r v) ≤
      (P.prod P) {p | supLadderHeight θ v.toNNReal p.1 ≤ -runningInfLoc p.2 r} := by
    apply measure_mono_ae
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := P) (ν := P)).ae
      (ae_barrier_supLadderHeight_le hθ t r v.toNNReal)] with p hp
    intro he
    apply hp p.2
    simpa only [Real.coe_toNNReal _ hv] using he
  have hrreal : 0 < (r : ℝ) := hr
  have hpowers : (((r : ℝ)⁻¹) ^ (1 / θ)) ^ (θ - 1) =
      (r : ℝ) ^ (-(1 - 1 / θ)) := by
    have hθne : θ ≠ 0 := ne_of_gt (lt_trans zero_lt_one hθ.1)
    calc
      _ = ((r : ℝ)⁻¹) ^ ((1 / θ) * (θ - 1)) :=
        (Real.rpow_mul (x := (r : ℝ)⁻¹) (inv_nonneg.mpr r.2) _ _).symm
      _ = (r : ℝ) ^ (-((1 / θ) * (θ - 1))) :=
        (Real.rpow_neg_eq_inv_rpow _ _).symm
      _ = _ := by
        congr 1
        field_simp [hθne]
  calc
    _ ≤ P {f | (reversedAt t f, DLoc.shift t f) ∈ erasedClockBarrier θ t r v} :=
      measure_mono_ae (ae_erased_height_exceedance_barrier hθ htpos r v)
    _ = (P.prod P) (erasedClockBarrier θ t r v) :=
      measure_reversed_prefix_fresh_event hθ htpos
        (measurableSet_erasedClockBarrier θ t r v)
        (erasedClockBarrier_prefix_local θ t r v)
    _ ≤ (P.prod P) {p | supLadderHeight θ v.toNNReal p.1 ≤ -runningInfLoc p.2 r} := hbarrier
    _ ≤ ENNReal.ofReal (Real.exp ((r : ℝ)⁻¹ * r -
        (v.toNNReal : ℝ) * (((r : ℝ)⁻¹) ^ (1 / θ)) ^ (θ - 1))) :=
      measure_supLadderHeight_le_independent_depth hθ r v.toNNReal (inv_nonneg.mpr r.2)
    _ = _ := by
      rw [inv_mul_cancel₀ hrreal.ne', Real.coe_toNNReal _ hv, hpowers,
        sub_eq_add_neg, Real.exp_add]

end BGW.StableTrees
