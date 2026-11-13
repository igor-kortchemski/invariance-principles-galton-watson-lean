/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import Mathlib.Probability.Kernel.Representation

/-!
# Transport of almost sure representations to the unit interval

An almost surely convergent sequence of Polish-valued random variables on any probability
space can be realized on the unit interval, with the same joint law. Thus the choice of the
unit interval as the source of a Skorokhod representation is independent of the construction
of its coupling.
-/

@[expose] public section

open Filter MeasureTheory
open scoped Topology

namespace BGW.Probability

/-- Transfer an almost surely convergent common-space representation to Lebesgue measure on
the unit interval. No standard Borel assumption on the original probability space is needed. -/
theorem exists_tendsto_ae_unitInterval_of_commonSpace {S Ω : Type*}
    [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} {Y : Ω → S} (hX : ∀ n, Measurable (X n)) (hY : Measurable Y)
    (hconv : ∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (Y ω))) :
    ∃ (X' : ℕ → unitInterval → S) (Y' : unitInterval → S),
      (∀ n, Measurable (X' n)) ∧ Measurable Y' ∧
      (∀ n, Measure.map (X' n) (volume : Measure unitInterval) = Measure.map (X n) μ) ∧
      Measure.map Y' (volume : Measure unitInterval) = Measure.map Y μ ∧
      ∀ᵐ ω ∂(volume : Measure unitInterval), Tendsto (fun n => X' n ω) atTop (𝓝 (Y' ω)) := by
  let : Nonempty Ω := nonempty_of_isProbabilityMeasure μ
  let : Nonempty S := ⟨Y (Classical.choice ‹Nonempty Ω›)⟩
  let F : Ω → S × (ℕ → S) := fun ω => (Y ω, fun n => X n ω)
  have hF : Measurable F := hY.prodMk (Measurable.of_eval hX)
  obtain ⟨f, hf, hmap⟩ := (μ.map F).exists_measurable_map_eq
  have hYmap : Measure.map (fun ω => (f ω).1) volume = μ.map Y := by
    rw [← Function.comp_def, ← Measure.map_map measurable_fst hf, hmap,
      Measure.map_map measurable_fst hF]
    rfl
  have hXmap (n : ℕ) : Measure.map (fun ω => (f ω).2 n) volume = μ.map (X n) := by
    have heval : Measurable (fun z : S × (ℕ → S) => z.2 n) :=
      (measurable_pi_apply n).comp measurable_snd
    rw [show (fun ω => (f ω).2 n) = (fun z : S × (ℕ → S) => z.2 n) ∘ f from rfl,
      ← Measure.map_map heval hf, hmap, Measure.map_map heval hF]
    rfl
  have hconvMap : ∀ᵐ z ∂μ.map F, Tendsto z.2 atTop (𝓝 z.1) := by
    apply (ae_map_iff hF.aemeasurable ?_).mpr hconv
    exact measurableSet_tendsto_fun
      (fun n => (measurable_pi_apply n).comp measurable_snd) measurable_fst
  have hconv' : ∀ᵐ ω ∂volume, Tendsto (f ω).2 atTop (𝓝 (f ω).1) := by
    apply ae_of_ae_map (μ := volume)
      (p := fun z : S × (ℕ → S) => Tendsto z.2 atTop (𝓝 z.1)) hf.aemeasurable
    rwa [hmap]
  exact ⟨fun n ω => (f ω).2 n, fun ω => (f ω).1,
    fun n => (measurable_pi_apply n).comp (measurable_snd.comp hf),
    measurable_fst.comp hf, hXmap, hYmap, hconv'⟩

end BGW.Probability
