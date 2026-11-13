/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.FirstLongMarkBasic
import Mathlib.Data.NNRat.Encodable
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Selecting the first long label

Finite counts on bounded label windows give a least long label. The exponential void
probabilities exclude the event that all such windows are empty.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

variable {θ : ℝ}

/-- The long-mark intensity is strictly positive in the stable range. -/
theorem longRate_pos (hθ : 1 < θ ∧ θ ≤ 2) : 0 < longRate θ := by
  apply one_div_pos.mpr
  exact Real.Gamma_pos_of_pos (sub_pos.mpr ((div_lt_one (by linarith)).mpr hθ.1))

private theorem measurableSet_longMarks :
    MeasurableSet {e : Excursion | (1 : ℝ≥0) < e.lifetime} :=
  measurableSet_lt measurable_const measurable_excursion_lifetime

private theorem longMarks_mass (hθ : 1 < θ ∧ θ ≤ 2) :
    excursionMeasure θ {e : Excursion | (1 : ℝ≥0) < e.lifetime} =
      ENNReal.ofReal (longRate θ) := by
  convert excursionMeasure_longMarks hθ using 2
  ext e
  exact_mod_cast (Iff.rfl : (1 : ℝ≥0) < e.lifetime ↔ (1 : ℝ≥0) < e.lifetime)

/-- The probability that a bounded initial label window has no long mark. -/
theorem measure_no_longMarks (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc)
      {f | excursionPointMeasure f (Ioc 0 t ×ˢ {e : Excursion | 1 < e.lifetime}) = 0} =
      ENNReal.ofReal (Real.exp (-((t : ℝ) * longRate θ))) := by
  obtain ⟨ξ, hξ, heq⟩ := exists_measurable_modification_excursionPointMeasure hθ
  have hlevy := (isTimeSimpleLevy_of_ae_eq_excursionPointMeasure hθ hξ heq).1
  have hrate : IsFiniteRate (stableLocalLaw θ : Measure DLoc) ξ
      {e : Excursion | 1 < e.lifetime} := by
    refine ⟨measurableSet_longMarks, fun u => ?_⟩
    filter_upwards [ae_finite_excursionCount hθ, heq] with f hf hfeq
    rw [hfeq]
    by_cases hu : u = 0
    · subst u
      simp
    · exact (hf u 1 (pos_iff_ne_zero.mpr hu) one_pos).2
  have hr : markRate (stableLocalLaw θ : Measure DLoc) ξ
      {e : Excursion | 1 < e.lifetime} = ENNReal.ofReal (longRate θ) :=
    (excursionMeasure_apply_of_ae_eq hθ hξ heq measurableSet_longMarks).2.symm.trans
      (longMarks_mass hθ)
  calc
    _ = (stableLocalLaw θ : Measure DLoc)
        {f | ξ f (Ioc 0 t ×ˢ {e : Excursion | 1 < e.lifetime}) = 0} := by
      apply measure_congr
      filter_upwards [heq] with f hf
      simp only [hf]
    _ = _ := by
      rw [prob_noMark_window hlevy hrate, hr,
        ENNReal.toReal_ofReal (longRate_pos hθ).le]

private theorem ae_exists_positive_longCount (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∃ n : ℕ,
      excursionPointMeasure f (Ioc 0 (n : ℝ≥0) ×ˢ {e : Excursion | 1 < e.lifetime}) ≠ 0 := by
  let P : Measure DLoc := stableLocalLaw θ
  let S : Set DLoc := {f | ∀ n : ℕ,
    excursionPointMeasure f (Ioc 0 (n : ℝ≥0) ×ˢ {e : Excursion | 1 < e.lifetime}) = 0}
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
      (Real.exp (-((n : ℝ) * longRate θ)))) atTop (𝓝 0) := by
    have h := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.atTop_mul_const (longRate_pos hθ)))
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using h
  have hbound (n : ℕ) : P S ≤ ENNReal.ofReal
      (Real.exp (-((n : ℝ) * longRate θ))) := by
    calc
      _ ≤ (stableLocalLaw θ : Measure DLoc)
          {f | excursionPointMeasure f
            (Ioc 0 (n : ℝ≥0) ×ˢ {e : Excursion | 1 < e.lifetime}) = 0} :=
        measure_mono (show S ⊆ {f | excursionPointMeasure f
          (Ioc 0 (n : ℝ≥0) ×ˢ {e : Excursion | 1 < e.lifetime}) = 0} from
          fun _ hf => hf n)
      _ = _ := by simpa only [NNReal.coe_natCast] using measure_no_longMarks hθ n
  have hz : P S = 0 := le_antisymm (ge_of_tendsto hlim (Eventually.of_forall hbound)) bot_le
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with f hf
  simpa only [S, mem_ofPred_eq, not_forall] using hf

/-- A.s. there is a long label and a least one. -/
theorem ae_exists_longLabel (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∃ L, IsLeast (longLabelSet f) L := by
  filter_upwards [ae_exists_positive_longCount hθ, ae_passageJumpSet_countable hθ,
    ae_finite_excursionCount hθ, ae_jumpExcursion_spec hθ] with f hex hc hfin hspec
  classical
  obtain ⟨n, hn⟩ := hex
  let S : Set ℝ≥0 := {x ∈ passageJumpSet f |
    (x, jumpExcursion x f) ∈ Ioc 0 (n : ℝ≥0) ×ˢ {e : Excursion | 1 < e.lifetime}}
  have hcount : excursionPointMeasure f
      (Ioc 0 (n : ℝ≥0) ×ˢ {e : Excursion | 1 < e.lifetime}) = (S.encard : ℝ≥0∞) :=
    excursionPointMeasure_apply hc (measurable_box measurableSet_longMarks)
  have hne : S.Nonempty := by
    apply Set.nonempty_of_encard_ne_zero
    intro hz
    exact hn (by simp only [hcount, hz, ENat.toENNReal_zero])
  have hn0 : (0 : ℝ≥0) < n := by
    obtain ⟨x, hx⟩ := hne
    exact hx.1.1.trans_le hx.2.1.2
  have hSfin : S.Finite := by
    apply Set.encard_lt_top_iff.mp
    apply ENat.toENNReal_lt_top.mp
    rw [← hcount]
    exact (hfin n 1 hn0 one_pos).2
  obtain ⟨L, hL, hmin⟩ := Set.exists_min_image S id hSfin hne
  have hLlong : L ∈ longLabelSet f :=
    ⟨hL.1, (hspec L hL.1).2.1 ▸ hL.2.2⟩
  refine ⟨L, hLlong, ?_⟩
  intro x hx
  by_cases hxn : x ≤ (n : ℝ≥0)
  · apply hmin x
    refine ⟨hx.1, ⟨hx.1.1, hxn⟩, ?_⟩
    change 1 < (jumpExcursion x f).lifetime
    rw [(hspec x hx.1).2.1]
    exact hx.2
  · exact hL.2.1.2.trans (le_of_not_ge hxn)

/-- The infimum defining the first label equals any least long label. -/
theorem firstLongLabel_eq_of_isLeast {f : DLoc} {L : ℝ≥0}
    (hL : IsLeast (longLabelSet f) L) : firstLongLabel f = L :=
  hL.csInf_eq

/-- Almost surely, the selected label is a long passage jump. -/
theorem ae_firstLongLabel_mem (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), firstLongLabel f ∈ longLabelSet f := by
  filter_upwards [ae_exists_longLabel hθ] with f hf
  obtain ⟨L, hL⟩ := hf
  rw [firstLongLabel_eq_of_isLeast hL]
  exact hL.1

end BGW.StableTrees
