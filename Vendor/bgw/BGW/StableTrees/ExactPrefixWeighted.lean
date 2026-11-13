/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import BGW.StableTrees.ForestLocalLimitWeights
import BGW.Probability.SeparableRepresentation

/-!
# Weighted weak convergence on separable metric spaces

Dudley representation transfers the weights to a common probability space. The mass-one
Scheffé theorem then gives convergence of bounded continuous weighted expectations.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

namespace BGW.StableTrees.ExactPrefix

/-- **Generic weighted-convergence helper (also for K15).**  If `P_k ⇒ P₀` on a separable metric
space, `w_k, w₀ ≥ 0` have mean one under `P_k, P₀`, and `w_k (y_k) → w₀ (x)` whenever
`y_k → x` with `x ∈ G` (`P₀ G = 1`) and `y_k ∈ S_k` (`P_k S_k = 1`), then the weighted measures
converge weakly: `∫ F w_k dP_k → ∫ F w₀ dP₀` for every bounded continuous `F`.  (Skorokhod
coupling, a.s. convergence of weights, Scheffé.) -/
theorem tendsto_integral_mul_weight {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [TopologicalSpace.SeparableSpace E] {P : ℕ → ProbabilityMeasure E}
    {P₀ : ProbabilityMeasure E}
    (hP : Tendsto P atTop (𝓝 P₀)) {w : ℕ → E → ℝ} {w₀ : E → ℝ}
    (hw : ∀ k, Measurable (w k)) (hw₀ : Measurable w₀)
    (hnn : ∀ k x, 0 ≤ w k x) (hnn₀ : ∀ x, 0 ≤ w₀ x)
    (h1 : ∀ k, ∫ x, w k x ∂(P k : Measure E) = 1) (h10 : ∫ x, w₀ x ∂(P₀ : Measure E) = 1)
    (S : ℕ → Set E) (hS : ∀ k, (P k : Measure E) (S k)ᶜ = 0)
    (G : Set E) (hG : (P₀ : Measure E) Gᶜ = 0)
    (hconv : ∀ x ∈ G, ∀ y : ℕ → E, (∀ k, y k ∈ S k) → Tendsto y atTop (𝓝 x) →
      Tendsto (fun k => w k (y k)) atTop (𝓝 (w₀ x))) (F : BoundedContinuousFunction E ℝ) :
    Tendsto (fun k => ∫ x, F x * w k x ∂(P k : Measure E)) atTop
      (𝓝 (∫ x, F x * w₀ x ∂(P₀ : Measure E))) := by
  obtain ⟨Ω, mΩ, ν, hν, X, Y, hXm, hYm, hXlaw, hYlaw, hXY⟩ :=
    BGW.Probability.exists_probabilitySpace_tendsto_ae_of_tendsto_metric hP
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure ν := hν
  have hSae : ∀ᵐ ω ∂ν, ∀ k, X k ω ∈ S k := by
    apply ae_all_iff.mpr
    intro k
    have hs : ∀ᵐ x ∂(P k : Measure E), x ∈ S k := by
      rw [ae_iff]
      exact hS k
    rw [← hXlaw k] at hs
    exact ae_of_ae_map (hXm k).aemeasurable hs
  have hGae : ∀ᵐ ω ∂ν, Y ω ∈ G := by
    have hg : ∀ᵐ x ∂(P₀ : Measure E), x ∈ G := by
      rw [ae_iff]
      exact hG
    rw [← hYlaw] at hg
    exact ae_of_ae_map hYm.aemeasurable hg
  have hweight : ∀ᵐ ω ∂ν,
      Tendsto (fun k => w k (X k ω)) atTop (𝓝 (w₀ (Y ω))) := by
    filter_upwards [hSae, hGae, hXY] with ω hs hg hc
    exact hconv (Y ω) hg (fun k => X k ω) hs hc
  have htest : ∀ᵐ ω ∂ν,
      Tendsto (fun k => F (X k ω)) atTop (𝓝 (F (Y ω))) := by
    filter_upwards [hXY] with ω hc
    exact (F.continuous.tendsto _).comp hc
  have hmass (k : ℕ) : ∫ ω, w k (X k ω) ∂ν = 1 := by
    rw [← integral_map (hXm k).aemeasurable (hw k).aestronglyMeasurable, hXlaw, h1]
  have hmass₀ : ∫ ω, w₀ (Y ω) ∂ν = 1 := by
    rw [← integral_map hYm.aemeasurable hw₀.aestronglyMeasurable, hYlaw, h10]
  have ht := tendsto_integral_mul_of_massOne
    (fun k => (hw k).comp (hXm k)) (hw₀.comp hYm)
    (fun k ω => hnn k (X k ω)) (fun ω => hnn₀ (Y ω)) hmass hmass₀
    (tendstoInMeasure_of_tendsto_ae
      (fun k => ((hw k).comp (hXm k)).aestronglyMeasurable) hweight)
    (fun k => F.continuous.measurable.comp (hXm k)) (F.continuous.measurable.comp hYm)
    (fun k ω => by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using F.norm_coe_le_norm (X k ω))
    (fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply] using F.norm_coe_le_norm (Y ω))
    (tendstoInMeasure_of_tendsto_ae
      (fun k => (F.continuous.measurable.comp (hXm k)).aestronglyMeasurable) htest)
  have hsource (k : ℕ) : (∫ ω, F (X k ω) * w k (X k ω) ∂ν) =
      ∫ x, F x * w k x ∂(P k : Measure E) := by
    rw [← hXlaw k, integral_map (hXm k).aemeasurable]
    exact (F.continuous.measurable.mul (hw k)).aestronglyMeasurable
  have htarget : (∫ ω, F (Y ω) * w₀ (Y ω) ∂ν) =
      ∫ x, F x * w₀ x ∂(P₀ : Measure E) := by
    rw [← hYlaw, integral_map hYm.aemeasurable]
    exact (F.continuous.measurable.mul hw₀).aestronglyMeasurable
  simpa only [Function.comp_apply, hsource, htarget] using ht

end BGW.StableTrees.ExactPrefix
