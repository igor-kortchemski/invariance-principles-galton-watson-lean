/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionDefs
public import BGW.StableTrees.UnitExcursionLaw
public import BGW.StableTrees.ExcursionMarkovConsequences
public import Mathlib.Probability.Distributions.Exponential

/-!
# Rate and null marks for first long excursions

The lifetime intensity has no atoms. Localizing the mean measure to bounded label windows
transfers this fact simultaneously to every passage jump of a stable path.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

variable {θ : ℝ}

/-- The rate `r_θ = 1/Γ(1-1/θ) = N(ζ > 1) = θ p₀`. -/
noncomputable def longRate (θ : ℝ) : ℝ := 1 / Real.Gamma (1 - 1 / θ)

/-- The exponential law of rate `r_θ` on `ℝ≥0` (the law of the first long label). -/
noncomputable def firstLongLabelLaw (θ : ℝ) : Measure ℝ≥0 :=
  (expMeasure (longRate θ)).map Real.toNNReal

/-- `N(ζ > 1) = r_θ`, from the sealed lifetime tail. -/
theorem excursionMeasure_longMarks (hθ : 1 < θ ∧ θ ≤ 2) :
    excursionMeasure θ {e : Excursion | 1 < (e.lifetime : ℝ)} =
      ENNReal.ofReal (longRate θ) := by
  exact excursionMeasure_lifetime_gt_one hθ

/-- No lifetime is charged by `N` (unified with lifetime `0`, excluded by the carrier). -/
theorem excursionMeasure_lifetime_singleton (hθ : 1 < θ ∧ θ ≤ 2) (u : ℝ≥0) :
    excursionMeasure θ {e : Excursion | e.lifetime = u} = 0 := by
  by_cases hu : u = 0
  · subst hu
    have : {e : Excursion | e.lifetime = 0} = ∅ := by
      ext e
      simp [e.lifetime_pos.ne']
    rw [this, measure_empty]
  · have h := excursionMeasure_lifetime_eq_zero hθ (u : ℝ) (by positivity)
    convert h using 2
    ext e
    simp [NNReal.coe_inj]

/-- A measurable null mark set contains none of the passage-jump marks, almost surely. -/
theorem ae_jumpExcursion_not_mem_of_null (hθ : 1 < θ ∧ θ ≤ 2)
    {A : Set Excursion} (hA : MeasurableSet A) (hnull : excursionMeasure θ A = 0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ x ∈ passageJumpSet f, jumpExcursion x f ∉ A := by
  obtain ⟨ξ, hξ, hξeq⟩ := exists_measurable_modification_excursionPointMeasure hθ
  have hzero (n : ℕ) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ξ f (Ioc 0 (n : ℝ≥0) ×ˢ A) = 0 := by
    apply (lintegral_eq_zero_iff (measurable_count hξ (measurable_box hA))).mp
    rw [lintegral_windowMark_eq hθ hξ hξeq (show (0 : ℝ≥0) ≤ n from bot_le) hA,
      hnull, mul_zero]
  filter_upwards [ae_all_iff.mpr hzero, hξeq,
    ae_excursionPointMeasure_singleton_prod hθ] with f hf hfeq hatom
  intro x hx hmem
  obtain ⟨n, hn⟩ := exists_nat_gt x
  have hle : excursionPointMeasure f ({x} ×ˢ A) ≤
      excursionPointMeasure f (Ioc 0 (n : ℝ≥0) ×ˢ A) := by
    apply measure_mono
    rintro p ⟨hp, hpA⟩
    exact ⟨⟨hp ▸ hx.1, hp ▸ hn.le⟩, hpA⟩
  have hz : excursionPointMeasure f (Ioc 0 (n : ℝ≥0) ×ˢ A) = 0 := by
    rw [← hfeq, hf n]
  rw [hz] at hle
  rw [hatom x A hA, ite_eq_left ⟨hx, hmem⟩] at hle
  exact one_ne_zero (le_antisymm hle bot_le)

/-- A.s. no excursion mark has a prescribed lifetime `a`: the set of excursions of lifetime `a`
is `N`-null, and `N`-null mark sets carry no jump mark (`ae_jumpExcursion_not_mem_of_null`). -/
theorem ae_jump_lifetime_ne (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x ∈ passageJumpSet f,
      passageTime x f - passageTimeMinus x f ≠ a := by
  have hA : MeasurableSet {e : Excursion | e.lifetime = a} :=
    measurableSet_eq_fun measurable_excursion_lifetime measurable_const
  filter_upwards [ae_jumpExcursion_not_mem_of_null hθ hA
    (excursionMeasure_lifetime_singleton hθ a), ae_jumpExcursion_spec hθ] with f hf hs
  intro x hx h
  exact hf x hx ((hs x hx).2.1.trans h)

/-- No fixed jump of the selected mark at a positive cutoff. -/
theorem ae_continuousAt_tailExcursion_path (hθ : 1 < θ ∧ θ ≤ 2) (T : ℝ≥0) (hT : 0 < T) :
    ∀ᵐ e ∂(tailExcursionLaw θ : Measure Excursion), ContinuousAt e.path.1 T := by
  have hjump : ∀ᵐ e ∂(tailExcursionLaw θ : Measure Excursion),
      Function.leftLim e.path.1 T = e.path.1 T := by
    rw [coe_tailExcursionLaw hθ, tailExcursionMeasure, excursionTail]
    exact Measure.ae_smul_measure (ae_restrict_of_ae (N_noFixedJump hθ T hT)) _
  filter_upwards [hjump] with e he
  apply continuousAt_iff_continuous_left'_right'.mpr
  refine ⟨?_, e.path.2.isRightContinuous T⟩
  change Tendsto e.path.1 (𝓝[<] T) (𝓝 (e.path.1 T))
  rw [← he]
  exact e.path.2.tendsto_nhdsLT_leftLim T

end BGW.StableTrees
