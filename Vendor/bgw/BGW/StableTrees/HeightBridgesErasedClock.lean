/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcess
import Mathlib.MeasureTheory.Measure.Support

/-!
# Erased height and the reversed supremum clock

Surplus mass in a terminal source window remains after erasure. Its ancestral heights
bound the surviving support from below. Only continuity of the reversed supremum clock
is used; continuity of the height process is unnecessary.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Erasure preserves a mass-free upper tail, without a finiteness assumption. -/
theorem eraseMass_Ioi_eq_zero {ρ : Measure ℝ≥0} {R : ℝ≥0}
    (hρ : ρ (Ioi R) = 0) (m : ℝ≥0∞) : eraseMass m ρ (Ioi R) = 0 := by
  by_cases hm : m = 0
  · simpa [hm, eraseMass_zero] using hρ
  have hc : eraseCut m ρ ≤ R := csInf_le' (show ρ (Ioi R) ≤ m by
    rw [hρ]
    exact zero_le)
  have hr : ρ (Ioi R ∩ Iio (eraseCut m ρ)) = 0 :=
    measure_mono_null inter_subset_left hρ
  simp [eraseMass, hm, Measure.add_apply, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Ioi, hr, Measure.dirac_apply', not_lt.mpr hc]

/-- An upper bound for the support top makes every strictly higher tail mass-free. -/
theorem measure_Ioi_eq_zero_of_topHeight_lt {ρ : Measure ℝ≥0} {R h : ℝ≥0}
    (hR : ρ (Ioi R) = 0) (hh : topHeight ρ < h) : ρ (Ioi h) = 0 := by
  by_contra hn
  obtain ⟨x, hxh, hxs⟩ := ρ.nonempty_inter_support_of_pos (pos_iff_ne_zero.mpr hn)
  have hx : ∀ ε : ℝ, 0 < ε → 0 < ρ (Metric.ball x ε) :=
    fun ε hε => (Measure.mem_support_iff_forall x).mp hxs _ (Metric.ball_mem_nhds x hε)
  have hb : BddAbove {x : ℝ≥0 | ∀ ε : ℝ, 0 < ε → 0 < ρ (Metric.ball x ε)} :=
    ⟨R, fun _ hy => support_le_of_mass_above_zero hR hy⟩
  exact (not_lt_of_ge (le_csSup hb hx)) (hh.trans hxh)

/-- A finite measure retains positive upper-tail mass whenever that tail exceeds the erasure. -/
theorem eraseMass_Ioi_pos {ρ : Measure ℝ≥0} [IsFiniteMeasure ρ]
    {m : ℝ≥0∞} {h : ℝ≥0} (hm : m < ρ (Ioi h)) : 0 < eraseMass m ρ (Ioi h) := by
  have hmle : m ≤ ρ univ := hm.le.trans (measure_mono (subset_univ _))
  have hmf : m ≠ ⊤ := ne_top_of_le_ne_top (measure_ne_top ρ _) hmle
  have ht := eraseMass_univ hmle
  have hp : ρ (Iic h) + ρ (Ioi h) = ρ univ := by
    simpa only [compl_Iic] using measure_add_measure_compl (μ := ρ) measurableSet_Iic
  have hpost : IsFiniteMeasure (eraseMass m ρ) := ⟨by
    rw [ht]
    exact lt_of_le_of_lt tsub_le_self (measure_lt_top ρ _)⟩
  let := hpost
  by_contra hn
  have hz : eraseMass m ρ (Ioi h) = 0 := le_antisymm (not_lt.mp hn) zero_le
  have hpart := measure_add_measure_compl (μ := eraseMass m ρ)
    (measurableSet_Iic (a := h))
  simp only [compl_Iic, hz, add_zero, ht, eraseMass_Iic] at hpart
  have hle : ρ univ - m ≤ ρ (Iic h) := hpart ▸ min_le_left _ _
  have hle' := tsub_le_iff_right.mp hle
  have hto := ENNReal.toReal_mono (by finiteness : ρ (Iic h) + m ≠ ⊤) hle'
  have hpt := congrArg ENNReal.toReal hp
  rw [ENNReal.toReal_add (measure_ne_top ρ _) hmf] at hto
  rw [ENNReal.toReal_add (measure_ne_top ρ _) (measure_ne_top ρ _)] at hpt
  have hmt := (ENNReal.toReal_lt_toReal hmf (measure_ne_top ρ _)).mpr hm
  linarith

/-- At a continuity endpoint, the terminal source-window mass is a reversed running supremum. -/
theorem exploration_source_terminal_mass (f : DLoc) {t u : ℝ≥0} (hu : u ≤ t)
    (hf : ∀ s, Function.leftLim f.1 s ≤ f.1 s)
    (hc : Function.leftLim f.1 (t - u) = f.1 (t - u)) :
    (explorationStieltjes f t).measure (Ioc ((t - u : ℝ≥0) : ℝ) (t : ℝ)) =
      ENNReal.ofReal (supRunning (reversedAt t f) u) := by
  have hF (x : ℝ≥0) : explorationStieltjes f t (x : ℝ) = futureInf f t x := by
    simp only [explorationStieltjes, dite_eq_left (explorationStieltjes_spec f t),
      futureInfFun, Real.toNNReal_coe]
  rw [StieltjesFunction.measure_Ioc, hF, hF, futureInf_self]
  have he := supRunning_reversedAt_window f (s := t - u) tsub_le_self hf hc
  rw [tsub_tsub_cancel_of_le hu] at he
  rw [he]

end BGW.StableTrees
