/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Topology.UnitInterval
public import Mathlib.Topology.MetricSpace.Polish

import BGW.Probability.SkorokhodRepresentationEncoding
import BGW.Probability.SkorokhodRepresentationReal
import BGW.Probability.SkorokhodRepresentationTransport
import BGW.Probability.WeakConvergence

/-!
# Skorokhod representation on Polish spaces

Weakly convergent probability laws on a Polish space have measurable versions on the unit
interval that converge almost surely. The proof encodes the space in the real line using
small continuity cells and the Cantor set, applies real quantile coupling, then transports
the resulting joint law to the unit interval.

Reference: Billingsley, *Convergence of Probability Measures*, second edition (1999),
Theorem 6.7. The real encoding replaces the nested subinterval construction in that proof.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace BGW.Probability

/-- Skorokhod's representation theorem: weakly convergent laws on a Polish space are the laws of
random variables on `([0,1], Lebesgue)` converging almost surely
(Billingsley 1999, Theorem 6.7; C14). -/
theorem exists_tendsto_ae_of_tendsto {S : Type*} [TopologicalSpace S] [PolishSpace S]
    [MeasurableSpace S] [BorelSpace S]
    {P : ℕ → ProbabilityMeasure S} {Q : ProbabilityMeasure S} (h : Tendsto P atTop (𝓝 Q)) :
    ∃ (X : ℕ → unitInterval → S) (Y : unitInterval → S),
      (∀ n, Measurable (X n)) ∧ Measurable Y ∧
      (∀ n, Measure.map (X n) (volume : Measure unitInterval) = (P n : Measure S)) ∧
      Measure.map Y (volume : Measure unitInterval) = (Q : Measure S) ∧
      ∀ᵐ ω ∂(volume : Measure unitInterval), Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
  let := TopologicalSpace.upgradeIsCompletelyMetrizable S
  let : Nonempty S := Q.nonempty
  obtain ⟨g, hg, hcont, hreflect⟩ := exists_ae_continuous_real_encoding (Q : Measure S)
  have hlim : Tendsto (fun n => (P n).map g) atTop (𝓝 (Q.map g)) :=
    tendsto_map_of_ae_continuousAt h (fun _ => hg.measurable.aemeasurable) hcont
  obtain ⟨U, V, hU, hV, hVlaw, hconv⟩ :=
    RealCoupling.exists_measurable_coupling_of_tendsto hlim
  let μ := RealCoupling.unitProbability
  have hlaw (ν : ProbabilityMeasure S) {Z : ℝ → ℝ} (hZ : Measurable Z)
      (hZlaw : μ.map Z = (ν.map g : Measure ℝ)) :
      μ.map (hg.invFun ∘ Z) = (ν : Measure S) := by
    rw [← Measure.map_map hg.measurable_invFun hZ, hZlaw]
    change ((ν : Measure S).map g).map hg.invFun = (ν : Measure S)
    rw [Measure.map_map hg.measurable_invFun hg.measurable,
      hg.leftInverse_invFun.id, Measure.map_id]
  have hrange (ν : ProbabilityMeasure S) {Z : ℝ → ℝ} (hZ : Measurable Z)
      (hZlaw : μ.map Z = (ν.map g : Measure ℝ)) :
      ∀ᵐ ω ∂μ, Z ω ∈ Set.range g := by
    apply ae_of_ae_map hZ.aemeasurable
    rw [hZlaw]
    exact ae_map_mem_range hg.measurableSet_range hg.measurable.aemeasurable
  let X : ℕ → ℝ → S := fun n => hg.invFun ∘ U n
  let Y : ℝ → S := hg.invFun ∘ V
  have hXm (n : ℕ) : Measurable (X n) := hg.measurable_invFun.comp (hU n).1
  have hYm : Measurable Y := hg.measurable_invFun.comp hV
  have hXlaw (n : ℕ) : μ.map (X n) = (P n : Measure S) := hlaw (P n) (hU n).1 (hU n).2
  have hYlaw : μ.map Y = (Q : Measure S) := hlaw Q hV hVlaw
  have hconvS : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω)) := by
    have hUr : ∀ᵐ ω ∂μ, ∀ n, U n ω ∈ Set.range g :=
      ae_all_iff.mpr fun n => hrange (P n) (hU n).1 (hU n).2
    filter_upwards [hconv, hUr, hrange Q hV hVlaw] with ω hω hUω hVω
    have hXeq (n : ℕ) : g (X n ω) = U n ω := by
      obtain ⟨x, hx⟩ := hUω n
      change g (hg.invFun (U n ω)) = U n ω
      rw [← hx, hg.leftInverse_invFun x]
    have hYeq : g (Y ω) = V ω := by
      obtain ⟨x, hx⟩ := hVω
      change g (hg.invFun (V ω)) = V ω
      rw [← hx, hg.leftInverse_invFun x]
    apply hreflect
    simpa only [hXeq, hYeq] using hω
  obtain ⟨X', Y', hXm', hYm', hXlaw', hYlaw', hconv'⟩ :=
    exists_tendsto_ae_unitInterval_of_commonSpace μ hXm hYm hconvS
  exact ⟨X', Y', hXm', hYm', fun n => (hXlaw' n).trans (hXlaw n),
    hYlaw'.trans hYlaw, hconv'⟩

end BGW.Probability
