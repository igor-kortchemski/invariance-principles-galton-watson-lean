/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarkedExcursions
public import BGW.Probability.PoissonCharacterization

/-! The Itô excursion measure, defined as the mean mark measure on a unit time window.
Its definition is independent of the measurable modification, and lifetime slabs have finite mass.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-! ### The excursion measure `N` -/

/-- **The excursion measure** `N A = ∫⁻ f, μ f ((0,1] × A) ∂P`, `P = stableLocalLaw θ`, as the
`Measure.join` of the law of `f ↦ ((μ f) ↾ (0,1] × univ).map Prod.snd`. -/
noncomputable def excursionMeasure (θ : ℝ) : Measure Excursion :=
  Measure.join ((stableLocalLaw θ : Measure DLoc).map
    (fun f => ((excursionPointMeasure f).restrict (Ioc 0 1 ×ˢ univ)).map Prod.snd))

/-- **Defining formula**: `N A = ∫⁻ f, μ f ((0,1] × A) ∂P`. -/
theorem excursionMeasure_apply {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {A : Set Excursion}
    (hA : MeasurableSet A) :
    excursionMeasure θ A =
      ∫⁻ f, excursionPointMeasure f (Ioc 0 1 ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) := by
  let ν : DLoc → Measure Excursion := fun f =>
    ((excursionPointMeasure f).restrict (Ioc 0 1 ×ˢ univ)).map Prod.snd
  have hν : AEMeasurable ν (stableLocalLaw θ : Measure DLoc) := by
    apply (Measure.measurable_map Prod.snd measurable_snd).comp_aemeasurable
    have hr : Measurable (fun μ : Measure (ℝ≥0 × Excursion) =>
        μ.restrict (Ioc 0 1 ×ˢ univ)) := by
      apply Measure.measurable_of_measurable_coe
      intro B hB
      simp only [Measure.restrict_apply hB]
      exact Measure.measurable_coe (hB.inter (measurableSet_Ioc.prod MeasurableSet.univ))
    exact hr.comp_aemeasurable (aemeasurable_excursionPointMeasure hθ)
  rw [excursionMeasure, Measure.join_apply hA,
    lintegral_map' (Measure.measurable_coe hA).aemeasurable hν]
  apply lintegral_congr
  intro f
  rw [Measure.map_apply measurable_snd hA,
    Measure.restrict_apply (measurable_snd hA)]
  congr 1
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_univ, and_true]
  tauto

/-- **Independence of the modification**: for every measurable modification `ξ`,
`N A = ∫⁻ ξ ((0,1] × A) ∂P`, which is `markRate`. -/
theorem excursionMeasure_apply_of_ae_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    {A : Set Excursion} (hA : MeasurableSet A) :
    excursionMeasure θ A =
        ∫⁻ f, ξ f (Ioc 0 1 ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) ∧
      excursionMeasure θ A = markRate (stableLocalLaw θ : Measure DLoc) ξ A := by
  have heq : excursionMeasure θ A =
      ∫⁻ f, ξ f (Ioc 0 1 ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) := by
    rw [excursionMeasure_apply hθ hA]
    rw [← lintegral_map (Measure.measurable_coe (measurable_box hA)) hξ]
    rw [Measure.map_congr hae,
      lintegral_map' (Measure.measurable_coe (measurable_box hA)).aemeasurable
        (aemeasurable_excursionPointMeasure hθ)]
  exact ⟨heq, heq⟩

/-- **Finite lifetime slabs**: `N {ε < ζ} < ∞` for every `ε > 0`. -/
theorem excursionMeasure_lifetime_slab_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ≥0}
    (hε : 0 < ε) : excursionMeasure θ {e : Excursion | ε < e.lifetime} < ⊤ := by
  obtain ⟨ξ, hξ, hae⟩ := exists_measurable_modification_excursionPointMeasure hθ
  obtain ⟨hlevy, hslab⟩ := isTimeSimpleLevy_of_ae_eq_excursionPointMeasure hθ hξ hae
  rw [(excursionMeasure_apply_of_ae_eq hθ hξ hae (hslab ε hε).1).2]
  exact markRate_lt_top hlevy (hslab ε hε).2

/-- **σ-finiteness** of `N` (exhaustion by `{1/(n+1) < ζ}`; every lifetime is positive). -/
theorem sigmaFinite_excursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    SigmaFinite (excursionMeasure θ) := by
  let S : ℕ → Set Excursion := fun n => {e | 1 / (n + 1 : ℝ≥0) < e.lifetime}
  refine ⟨⟨⟨S, fun _ => trivial, ?_, ?_⟩⟩⟩
  · intro n
    apply excursionMeasure_lifetime_slab_lt_top hθ
    positivity
  · apply eq_univ_of_forall
    intro e
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt e.lifetime_pos
    exact mem_iUnion.mpr ⟨n, hn⟩

end BGW.StableTrees
