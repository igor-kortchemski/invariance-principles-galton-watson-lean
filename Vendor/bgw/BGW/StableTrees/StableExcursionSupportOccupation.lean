/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableExcursionSupportWindows
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Zero occupation of the reflected stable process

At each fixed positive time the reflection is positive almost surely: otherwise the terminal
time would minimize the compact path, contrary to the regularity and reversal theorem.
Fubini then gives zero Lebesgue occupation of the zero set. This avoids a separate construction
of the drift coefficient of the passage subordinator (J. Bertoin, *Lévy Processes*, Cambridge
University Press, 1996, Chapter VII).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- At any fixed positive time the reflected stable process is almost surely positive. -/
theorem ae_reflected_pos_fixed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), 0 < (reflectedFrom 0 f).1 t := by
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hm := (isStableLevyLaw_stableProcessLaw hθ htR).ae_not_isGenMinimizer_top hθ htR
  rw [← map_restrict_stableLocalLaw hθ ht] at hm
  have hm' := ae_of_ae_map (DLoc.measurable_restrict t).aemeasurable hm
  filter_upwards [hm', ae_eval_zero_stableLocalLaw hθ] with f hn h0
  by_contra hp
  have hz : (reflectedFrom 0 f).1 t = 0 :=
    le_antisymm (le_of_not_gt hp) (reflectedFrom_nonneg 0 f t)
  have hval : f.1 t = runningInfLoc f t := by
    rw [reflectedFrom_zero_apply h0] at hz
    exact sub_eq_zero.mp hz
  apply hn
  let _ : Nonempty (Set.Icc (0 : ℝ) (t : ℝ)) := ⟨⟨0, le_rfl, t.2⟩⟩
  let W := DLoc.restrict t f
  let top : Set.Icc (0 : ℝ) (t : ℝ) := ⟨t, htR.le, le_rfl⟩
  change genVal W top = ⨅ s, W s
  apply le_antisymm
  · apply (min_le_right (Function.leftLim W top) (W top)).trans
    change f.1 t ≤ ⨅ s, W s
    rw [hval]
    apply le_ciInf
    intro s
    exact runningInfLoc_le_eval f t ⟨⟨s, s.2.1⟩, by exact_mod_cast s.2.2⟩
  · exact iInf_le_genVal W top

/-- **The zero set of the reflected process is Lebesgue-null** (a.s.; measured in `ℝ` through the
coercion, since `ℝ≥0` carries no `MeasureSpace` instance). -/
theorem ae_zeroSet_volume_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (volume : Measure ℝ) (((↑) : ℝ≥0 → ℝ) '' {t : ℝ≥0 | (reflectedFrom 0 f).1 t = 0}) = 0 := by
  let P : Measure DLoc := stableLocalLaw θ
  let F : ℝ → DLoc → ℝ := fun t f => (reflectedFrom 0 f).1 (Real.toNNReal t)
  have hF : Measurable (fun p : ℝ × DLoc => F p.1 p.2) := by
    change Measurable (fun p : ℝ × DLoc =>
      (reflectedFrom 0 p.2).1 (Real.toNNReal p.1))
    exact measurable_reflectedFrom_eval.comp (measurable_const.prodMk
      (measurable_snd.prodMk (measurable_real_toNNReal.comp measurable_fst)))
  have hmeas : MeasurableSet {p : ℝ × DLoc | 0 ≤ p.1 → F p.1 p.2 ≠ 0} := by
    simp only [imp_iff_not_or]
    exact (measurableSet_le measurable_const measurable_fst).compl.union
      (measurableSet_eq_fun hF measurable_const).compl
  have htimes : ∀ᵐ t ∂(volume : Measure ℝ), ∀ᵐ f ∂P, 0 ≤ t → F t f ≠ 0 := by
    filter_upwards [(volume : Measure ℝ).ae_ne 0] with t ht
    by_cases hpos : 0 < t
    · have htNN : 0 < Real.toNNReal t := Real.toNNReal_pos.mpr hpos
      exact (ae_reflected_pos_fixed hθ htNN).mono fun _ h _ => ne_of_gt h
    · exact Filter.Eventually.of_forall fun _ h => (ht (le_antisymm (le_of_not_gt hpos) h)).elim
  have hpaths : ∀ᵐ f ∂P, ∀ᵐ t ∂(volume : Measure ℝ), 0 ≤ t → F t f ≠ 0 :=
    (Measure.ae_ae_comm hmeas).mp htimes
  filter_upwards [hpaths] with f hf
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hf] with t ht
  rintro ⟨u, hu, rfl⟩
  apply ht u.2
  change (reflectedFrom 0 f).1 (Real.toNNReal (u : ℝ)) = 0
  simpa only [Real.toNNReal_coe] using (show (reflectedFrom 0 f).1 u = 0 from hu)

end BGW.StableTrees
