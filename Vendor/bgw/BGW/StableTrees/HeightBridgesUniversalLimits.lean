/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridgesUniversal

/-!
# Almost sure identification of the universal limsup

The chosen sequence converges on every required rational slice and almost every age.
Each finite limit equals the literal real limsup defining the universal height.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Under the stable law, `heightUniv` is H02's height at every rational time, a.s. -/
theorem ae_heightUniv_eq_height {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q : ℚ, 0 ≤ q →
      heightUniv θ f (q : ℝ).toNNReal = height θ f (q : ℝ).toNNReal := by
  have hP := (isUniversalHeightSeq_heightEps hθ).2.2.2.1
  apply ae_all_iff.mpr
  intro q
  by_cases hq : 0 ≤ q
  · exact (hP q hq).mono fun _ h _ => h.limsup_eq
  · exact ae_of_all _ fun _ h => False.elim (hq h)

/-- Under `N`, the approximations converge along `heightEps θ` to `heightUniv` at every rational
age before the lifetime. -/
theorem ae_tendsto_heightUniv_excursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(excursionMeasure θ), ∀ q : ℚ, 0 < q → (q : ℝ).toNNReal < e.lifetime →
      Tendsto (fun k => heightApprox (heightEps θ k) e.path (q : ℝ).toNNReal) atTop
        (𝓝 (heightUniv θ e.path (q : ℝ).toNNReal)) := by
  have hN := (isUniversalHeightSeq_heightEps hθ).2.2.2.2.1
  apply ae_all_iff.mpr
  intro q
  by_cases hq : 0 < q
  · have hconv : ∀ᵐ e ∂(excursionMeasure θ).restrict
        {e : Excursion | (q : ℝ).toNNReal < e.lifetime},
        Tendsto (fun k => heightApprox (heightEps θ k) e.path (q : ℝ).toNNReal) atTop
          (𝓝 (heightUniv θ e.path (q : ℝ).toNNReal)) := (hN q hq).mono fun e he => by
      obtain ⟨L, hL⟩ := he
      have heq : heightUniv θ e.path (q : ℝ).toNNReal = L := hL.limsup_eq
      rw [heq]
      exact hL
    have hfull := (ae_restrict_iff'
      (measurableSet_lt measurable_const measurable_excursion_lifetime)).mp hconv
    exact hfull.mono fun _ h _ => h
  · exact ae_of_all _ fun _ h => False.elim (hq h)

/-- Under the unit law, the same at every rational age `q < 1`. -/
theorem ae_tendsto_heightUniv_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), ∀ q : ℚ, 0 < q → q < 1 →
      Tendsto (fun k => heightApprox (heightEps θ k) e.path (q : ℝ).toNNReal) atTop
        (𝓝 (heightUniv θ e.path (q : ℝ).toNNReal)) := by
  have hU := (isUniversalHeightSeq_heightEps hθ).2.2.2.2.2.1
  apply ae_all_iff.mpr
  intro q
  by_cases hq : 0 < q ∧ q < 1
  · filter_upwards [hU q hq.1 hq.2] with e he _ _
    obtain ⟨L, hL⟩ := he
    have heq : heightUniv θ e.path (q : ℝ).toNNReal = L := hL.limsup_eq
    rw [heq]
    exact hL
  · exact ae_of_all _ fun _ h0 h1 => False.elim (hq ⟨h0, h1⟩)

/-- At Lebesgue-a.e. age, `heightUniv` is H02's height under the stable law. -/
theorem ae_age_heightUniv_eq_height {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0) :
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo 0 (S : ℝ))), ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      heightUniv θ f s.toNNReal = height θ f s.toNNReal := by
  have hP := (isUniversalHeightSeq_heightEps hθ).2.2.2.2.2.2.1 S
  exact hP.mono fun _ hs => hs.mono fun _ hf => hf.limsup_eq

/-- At Lebesgue-a.e. age, the approximations converge along `heightEps θ` to `heightUniv` under
`N` on `{s < ζ}`. -/
theorem ae_age_tendsto_heightUniv_excursion {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (S : ℝ≥0) :
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo 0 (S : ℝ))),
      ∀ᵐ e ∂((excursionMeasure θ).restrict {e : Excursion | s.toNNReal < e.lifetime}),
        Tendsto (fun k => heightApprox (heightEps θ k) e.path s.toNNReal) atTop
          (𝓝 (heightUniv θ e.path s.toNNReal)) := by
  have hN := (isUniversalHeightSeq_heightEps hθ).2.2.2.2.2.2.2.1 S
  filter_upwards [hN] with s hs
  filter_upwards [hs] with e he
  obtain ⟨L, hL⟩ := he
  have heq : heightUniv θ e.path s.toNNReal = L := hL.limsup_eq
  rw [heq]
  exact hL

/-- At Lebesgue-a.e. age `s < 1`, the same under the unit law. -/
theorem ae_age_tendsto_heightUniv_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
      ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion),
        Tendsto (fun k => heightApprox (heightEps θ k) e.path s.toNNReal) atTop
          (𝓝 (heightUniv θ e.path s.toNNReal)) := by
  have hU := (isUniversalHeightSeq_heightEps hθ).2.2.2.2.2.2.2.2
  filter_upwards [hU] with s hs
  filter_upwards [hs] with e he
  obtain ⟨L, hL⟩ := he
  have heq : heightUniv θ e.path s.toNNReal = L := hL.limsup_eq
  rw [heq]
  exact hL

end BGW.StableTrees
