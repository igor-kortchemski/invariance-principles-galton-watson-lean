/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesErasedClock

/-!
# A stopped-clock bound for erased exploration height

A terminal source window with mass greater than the erasure retains some mass. The
ancestral clock bounds its heights from below, and hence bounds the erased height.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Surplus terminal-source mass bounds the erased height by the reversed clock. -/
theorem erased_height_le_clock_of_sup_gt (θ : ℝ) (f : DLoc) {t u : ℝ≥0}
    (hu : u ≤ t) (hf : ∀ s, Function.leftLim f.1 s ≤ f.1 s)
    (hc : Function.leftLim f.1 (t - u) = f.1 (t - u))
    (hmono : Monotone (fun u : Iic t => supLocalTime θ (reversedAt t f) u))
    (hclock : ∀ᵐ x ∂(explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ)),
      0 < x ∧ x ≤ (t : ℝ) ∧ 0 ≤ height θ f x.toNNReal ∧
      height θ f x.toNNReal = supLocalTime θ (reversedAt t f) t -
        supLocalTime θ (reversedAt t f) (t - x.toNNReal))
    (habove : exploration θ f t (Ioi (height θ f t).toNNReal) = 0)
    (m : ℝ≥0∞) (hm : m < ENNReal.ofReal (supRunning (reversedAt t f) u)) :
    height θ f t - (topHeight (eraseMass m (exploration θ f t)) : ℝ) ≤
      supLocalTime θ (reversedAt t f) u := by
  let μ := (explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ))
  let ρ := exploration θ f t
  let A := Ioc ((t - u : ℝ≥0) : ℝ) (t : ℝ)
  have hAsub : A ⊆ Ioc 0 (t : ℝ) := by
    intro x hx
    exact ⟨(t - u).2.trans_lt hx.1, hx.2⟩
  have hmass : μ A = ENNReal.ofReal (supRunning (reversedAt t f) u) := by
    rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr hAsub]
    exact exploration_source_terminal_mass f hu hf hc
  let : IsFiniteMeasure μ := ⟨by
    rw [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  let : IsFiniteMeasure ρ := Measure.isFiniteMeasure_map μ _
  by_contra hn
  have hlt : (topHeight (eraseMass m ρ) : ℝ) <
      height θ f t - supLocalTime θ (reversedAt t f) u := by
    linarith only [not_le.mp hn]
  obtain ⟨h, hkh, hh⟩ := exists_between hlt
  have hh0 : 0 ≤ h := (topHeight (eraseMass m ρ)).2.trans hkh.le
  let H : ℝ≥0 := ⟨h, hh0⟩
  have htail : μ A ≤ ρ (Ioi H) := by
    change μ A ≤ exploration θ f t (Ioi H)
    rw [exploration, Measure.map_apply (measurable_exploration_heightMap θ f) measurableSet_Ioi]
    apply measure_mono_ae
    filter_upwards [hclock] with x hx
    intro hxA
    have hxlo : t - u ≤ x.toNNReal := by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hx.1.le]
      exact hxA.1.le
    have hage : t - x.toNNReal ≤ u := by
      calc
        t - x.toNNReal ≤ t - (t - u) := tsub_le_tsub_left hxlo t
        _ = u := tsub_tsub_cancel_of_le hu
    have hM := hmono (show
      (⟨t - x.toNNReal, show t - x.toNNReal ≤ t from tsub_le_self⟩ : Iic t) ≤
        ⟨u, hu⟩ from hage)
    change supLocalTime θ (reversedAt t f) (t - x.toNNReal) ≤
      supLocalTime θ (reversedAt t f) u at hM
    change H < (height θ f x.toNNReal).toNNReal
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hx.2.2.1, hx.2.2.2]
    exact hh.trans_le (sub_le_sub_left hM _)
  have hpos := eraseMass_Ioi_pos ((hm.trans_le (hmass ▸ htail)))
  have hz := measure_Ioi_eq_zero_of_topHeight_lt (eraseMass_Ioi_eq_zero habove m)
    (show topHeight (eraseMass m ρ) < H from hkh)
  exact (ne_of_gt hpos) hz

/-- On one event all rational reversed ages give the stopped-clock comparison, for every mass. -/
theorem ae_erased_height_le_clock_rational {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q : ℚ,
      (q : ℝ).toNNReal ≤ t → ∀ m : ℝ≥0∞,
      m < ENNReal.ofReal (supRunning (reversedAt t f) (q : ℝ).toNNReal) →
      height θ f t - (topHeight (eraseMass m (exploration θ f t)) : ℝ) ≤
        supLocalTime θ (reversedAt t f) (q : ℝ).toNNReal := by
  have hcont : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q : ℚ,
      ContinuousAt f.1 (t - (q : ℝ).toNNReal) :=
    ae_all_iff.mpr fun q => ae_continuousAt_stableLocalLaw hθ _
  filter_upwards [ae_reversed_clock_prefix hθ ht, ae_exploration_source_clock hθ ht,
    ae_exploration_above_height hθ t, ae_leftLim_le_stableLocalLaw hθ, hcont]
    with f hg hs ha hf hc
  intro q hq m hm
  exact erased_height_le_clock_of_sup_gt θ f hq hf
    ((hc q).continuousWithinAt.leftLim_eq) hg.2.2.1 hs ha m hm

end BGW.StableTrees
