/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesStoppedClock
public import BGW.StableTrees.HeightBridgesPrefixTransfer

/-!
# A measurable stopped-clock barrier event

Rational clock tests describe the barrier before a local-time level. This description
is prefix-local and separates the reversed prefix from the fresh infimum depth.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A rational clock level above `v` is reached before the fresh depth is exceeded. -/
def erasedClockBarrier (θ : ℝ) (t r : ℝ≥0) (v : ℝ) : Set (DLoc × DLoc) :=
  {p | ∃ z : ℚ, v < (z : ℝ) ∧ (z : ℝ) < supLocalTime θ p.1 t ∧
    ∀ q : ℚ, (q : ℝ).toNNReal ≤ t →
      supLocalTime θ p.1 (q : ℝ).toNNReal < (z : ℝ) →
        supRunning p.1 (q : ℝ).toNNReal ≤ -runningInfLoc p.2 r}

/-- The rational stopped-clock barrier is measurable. -/
theorem measurableSet_erasedClockBarrier (θ : ℝ) (t r : ℝ≥0) (v : ℝ) :
    MeasurableSet (erasedClockBarrier θ t r v) := by
  have hI : Measurable (fun p : DLoc × DLoc => -runningInfLoc p.2 r) :=
    ((measurable_runningInfLoc_uncurry.comp
      (measurable_const.prodMk measurable_snd))).neg
  have hM (u : ℝ≥0) : Measurable (fun p : DLoc × DLoc => supLocalTime θ p.1 u) :=
    (measurable_supLocalTime θ u).comp measurable_fst
  have hS (u : ℝ≥0) : Measurable (fun p : DLoc × DLoc => supRunning p.1 u) :=
    (measurable_supRunning u).comp measurable_fst
  have htest (z : ℚ) : MeasurableSet {p : DLoc × DLoc | ∀ q : ℚ,
      (q : ℝ).toNNReal ≤ t → supLocalTime θ p.1 (q : ℝ).toNNReal < (z : ℝ) →
        supRunning p.1 (q : ℝ).toNNReal ≤ -runningInfLoc p.2 r} := by
    have hq (q : ℚ) : MeasurableSet {p : DLoc × DLoc |
        (q : ℝ).toNNReal ≤ t → supLocalTime θ p.1 (q : ℝ).toNNReal < (z : ℝ) →
          supRunning p.1 (q : ℝ).toNNReal ≤ -runningInfLoc p.2 r} :=
      (MeasurableSet.const _).imp
        ((measurableSet_lt (hM _) measurable_const).imp (measurableSet_le (hS _) hI))
    convert MeasurableSet.iInter hq using 1
    ext p
    simp only [mem_iInter, mem_ofPred_eq]
  have hz (z : ℚ) : MeasurableSet {p : DLoc × DLoc |
      v < (z : ℝ) ∧ (z : ℝ) < supLocalTime θ p.1 t ∧ ∀ q : ℚ,
      (q : ℝ).toNNReal ≤ t → supLocalTime θ p.1 (q : ℝ).toNNReal < (z : ℝ) →
        supRunning p.1 (q : ℝ).toNNReal ≤ -runningInfLoc p.2 r} :=
    (MeasurableSet.const _).inter
      ((measurableSet_lt measurable_const (hM t)).inter (htest z))
  simpa only [erasedClockBarrier, Set.ofPred_exists] using MeasurableSet.iUnion hz

/-- The barrier reads its first path only on the compact prefix. -/
theorem erasedClockBarrier_prefix_local (θ : ℝ) (t r : ℝ≥0) (v : ℝ)
    (f g h : DLoc) (he : DLoc.restrict t f = DLoc.restrict t g) :
    ((f, h) ∈ erasedClockBarrier θ t r v ↔ (g, h) ∈ erasedClockBarrier θ t r v) := by
  have hM := supLocalTime_eq_of_restrict_eq θ f g he
  have hS := supRunning_eq_of_restrict_eq f g he
  change (∃ z : ℚ, _ ∧ _ ∧ _) ↔ (∃ z : ℚ, _ ∧ _ ∧ _)
  simp_rw [hM t le_rfl]
  apply exists_congr
  intro z
  apply and_congr_right
  intro _hz
  apply and_congr_right
  intro _hzt
  apply forall_congr'
  intro q
  by_cases hq : (q : ℝ).toNNReal ≤ t
  · rw [hM _ hq, hS _ hq]
  · simp only [hq, false_implies]

/-- Erased-height exceedance implies the rational stopped-clock barrier. -/
theorem ae_erased_height_exceedance_barrier {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) (r : ℝ≥0) (v : ℝ) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      v < height θ f t - (topHeight (eraseMass
        (ENNReal.ofReal (-(futureInf (DLoc.shift t f) r 0))) (exploration θ f t)) : ℝ) →
        (reversedAt t f, DLoc.shift t f) ∈ erasedClockBarrier θ t r v := by
  filter_upwards [ae_erased_height_le_clock_rational hθ ht] with f hf
  intro hv
  let m := -(futureInf (DLoc.shift t f) r 0)
  have hm0 : 0 ≤ m := by
    have hh := futureInf_le_eval (DLoc.shift t f) r 0 0 ⟨by simp, zero_le⟩
    change futureInf (DLoc.shift t f) r 0 ≤ f.1 (t + 0) - f.1 t at hh
    simp only [add_zero, sub_self] at hh
    exact neg_nonneg.mpr hh
  obtain ⟨z, hvz, hzh⟩ := exists_rat_btwn hv
  refine ⟨z, hvz, ?_, ?_⟩
  · exact hzh.trans_le (sub_le_self _ (NNReal.coe_nonneg _))
  · intro q hqt hqz
    by_contra hn
    have hS : m < supRunning (reversedAt t f) (q : ℝ).toNNReal := by
      dsimp only [m]
      rw [futureInf_zero_eq_runningInf]
      exact not_le.mp hn
    have hlt : ENNReal.ofReal m <
        ENNReal.ofReal (supRunning (reversedAt t f) (q : ℝ).toNNReal) :=
      (ENNReal.ofReal_lt_ofReal_iff (hm0.trans_lt hS)).mpr hS
    have hb := hf q hqt (ENNReal.ofReal m) hlt
    exact (not_lt_of_ge hb) (hqz.trans hzh)

/-- Under the full stable law, the stopped-clock barrier implies the ladder-height bound. -/
theorem ae_barrier_supLadderHeight_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t r v : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ g : DLoc,
      (f, g) ∈ erasedClockBarrier θ t r v → supLadderHeight θ v f ≤ -runningInfLoc g r := by
  filter_upwards [ae_supLocalTime_spec hθ, ae_supLadder_spec hθ] with f hM hA
  intro g he
  obtain ⟨z, hvz, hzt, hz⟩ := he
  let a := supLadderTime θ v f
  have hMa : supLocalTime θ f a = v := hA.2.2.2.2.2 v
  have hat : a < t := by
    by_contra hn
    have hh := hM.2.1 (not_lt.mp hn)
    rw [hMa] at hh
    exact (not_lt_of_ge hh) (hvz.trans hzt)
  obtain ⟨q, hq, hqt⟩ := exists_rational_times_above_tendsto hat
  have hc : Tendsto (fun n => supLocalTime θ f (q n : ℝ).toNNReal) atTop (𝓝 (v : ℝ)) := by
    rw [← hMa]
    exact (hM.2.2.1.tendsto a).comp hqt
  obtain ⟨n, hn⟩ := (hc.eventually (eventually_lt_nhds hvz)).exists
  exact (monotone_supRunning f (hq n).1.le).trans (hz (q n) (hq n).2.le hn)

end BGW.StableTrees
