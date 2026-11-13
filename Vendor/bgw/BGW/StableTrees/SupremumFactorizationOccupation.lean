/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarkedExcursionsSupport

/-!
# Splitting occupation integrals over infimum excursions

The zero set has zero Lebesgue measure, so an occupation integral can be split over
passage-jump intervals. The local-time coordinate is constant on each such interval.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- On each passage-jump interval the infimum local time equals the jump label. -/
theorem ae_localTime_on_passage_interval {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      ∀ t : ℝ≥0, passageTimeMinus x f ≤ t → t ≤ passageTime x f →
        localTime f t = (x : ℝ) := by
  filter_upwards [ae_localTime_passageTime hθ] with f hf
  intro x _hx t hgt htd
  have hg := (hf x).2
  have hd := (hf x).1
  have hlo := runningInfLoc_antitone f htd
  have hup := runningInfLoc_antitone f hgt
  dsimp [localTime] at hg hd ⊢
  linarith

/-- Split an occupation integral into the passage-jump intervals, recording the local-time
label as the first coordinate of the excursion point measure. -/
theorem ae_lintegral_split_passage_intervals {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (H : ℝ → ℝ → ℝ → ℝ≥0∞) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∫⁻ t in Ici (0 : ℝ),
        H t (localTime f t.toNNReal) ((reflectedFrom 0 f).1 t.toNNReal)) =
      ∫⁻ p, (∫⁻ t in Ioo (passageTimeMinus p.1 f : ℝ) (passageTime p.1 f : ℝ),
        H t p.1 ((reflectedFrom 0 f).1 t.toNNReal)) ∂excursionPointMeasure f := by
  classical
  filter_upwards [ae_passageJumpSet_countable hθ, ae_jump_intervals_disjoint hθ,
    ae_volume_compl_iUnion_jump_intervals hθ, ae_localTime_on_passage_interval hθ]
    with f hc hd hz hL
  let := hc.to_subtype
  let U : passageJumpSet f → Set ℝ := fun x =>
    Ioo (passageTimeMinus x f : ℝ) (passageTime x f : ℝ)
  have hdisj : Pairwise (Function.onFun Disjoint U) := by
    intro x y hne
    have hxy : (x : ℝ≥0) ≠ y := fun h => hne (Subtype.ext h)
    rcases lt_or_gt_of_ne hxy with hlt | hgt
    · apply Set.disjoint_left.mpr
      intro t ht ht'
      have hsep : (passageTime x f : ℝ) < passageTimeMinus y f := by
        exact_mod_cast hd x x.2 y y.2 hlt
      exact (ht.2.trans hsep).not_gt ht'.1
    · apply Set.disjoint_left.mpr
      intro t ht ht'
      have hsep : (passageTime y f : ℝ) < passageTimeMinus x f := by
        exact_mod_cast hd y y.2 x x.2 hgt
      exact (ht'.2.trans hsep).not_gt ht.1
  have hsets : Ici (0 : ℝ) =ᵐ[volume] ⋃ x, U x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with t ht
    apply propext
    constructor
    · intro ht0
      by_contra hn
      apply ht
      refine ⟨⟨t, ht0⟩, ?_, rfl⟩
      intro hm
      obtain ⟨x, hx, hxt⟩ := Set.mem_iUnion₂.mp hm
      apply hn
      exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, by exact_mod_cast hxt⟩
    · intro hm
      obtain ⟨x, hx⟩ := Set.mem_iUnion.mp hm
      exact (passageTimeMinus x f).coe_nonneg.trans hx.1.le
  rw [setLIntegral_congr hsets, lintegral_iUnion (fun _ => measurableSet_Ioo) hdisj]
  rw [excursionPointMeasure, ite_eq_left hc, lintegral_sum_measure]
  simp_rw [lintegral_dirac]
  apply tsum_congr
  intro x
  apply setLIntegral_congr_fun measurableSet_Ioo
  intro t ht
  have ht0 : 0 ≤ t := (passageTimeMinus x f).coe_nonneg.trans ht.1.le
  have hgt : passageTimeMinus x f ≤ t.toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]
    exact ht.1.le
  have htd : t.toNNReal ≤ passageTime x f := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ ht0]
    exact ht.2.le
  exact congrArg (fun a => H t a ((reflectedFrom 0 f).1 t.toNNReal))
    (hL x x.2 t.toNNReal hgt htd)

end BGW.StableTrees
