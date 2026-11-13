/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessModulus
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Uniform modulus control over all height laws

For each fixed index, continuity gives a small modulus in probability. Combining
these bounds over finitely many initial indices with the eventual regeneration
estimate gives one scale valid uniformly over every scaling index.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.HeightTightness

private theorem exists_pos_height_modulus_probability_small (μ : PMF ℕ)
    (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ (offspringSeqLaw μ).toMeasure.real
      {ω | η < heightOscillation B n T δ ω} ≤ ε := by
  let P := (offspringSeqLaw μ).toMeasure
  let E (m : ℕ) : Set (ℕ → ℕ) := {ω | η < heightOscillation B n T (1 / (m + 1 : ℝ)) ω}
  have hm (m : ℕ) : MeasurableSet (E m) :=
    measurableSet_lt measurable_const (measurable_heightOscillation B n T _)
  have hscale : Tendsto (fun m : ℕ => (1 : ℝ) / (m + 1 : ℝ)) atTop (𝓝 0) := by
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hev : ∀ ω : ℕ → ℕ, ∀ᶠ m : ℕ in atTop, ω ∉ E m := by
    intro ω
    let f := forestHeightPath B n T ω
    obtain ⟨ρ, hρ, hclose⟩ := Metric.uniformContinuous_iff.mp
      (CompactSpace.uniformContinuous_of_continuous f.continuous) (η / 2) (by positivity)
    filter_upwards [hscale.eventually (gt_mem_nhds hρ)] with m hmρ
    have hb : heightOscillation B n T (1 / (m + 1 : ℝ)) ω ≤ η / 2 := by
      apply heightOscillation_le B n T.coe_nonneg (by positivity) ω
      intro s t hst
      have hh := hclose (a := s) (b := t) (by
        change |(s : ℝ) - t| < ρ
        exact hst.trans_lt hmρ)
      change |B n / n * forestHeightLin ω (n * s) -
        B n / n * forestHeightLin ω (n * t)| < η / 2 at hh
      exact hh.le
    intro hh
    have : η < heightOscillation B n T (1 / (m + 1 : ℝ)) ω := hh
    linarith
  have hprob : Tendsto (fun m : ℕ => P.real (E m)) atTop (𝓝 0) :=
    tendsto_measureReal_zero_of_eventually_notMem P hm (Eventually.of_forall hev)
  obtain ⟨m, hmε⟩ := (hprob.eventually (gt_mem_nhds hε)).exists
  exact ⟨1 / (m + 1 : ℝ), by positivity, hmε.le⟩

/-- The asymptotic height modulus extends uniformly to all scaling indices, including the
finitely many initial path laws. -/
theorem exists_pos_uniform_height_modulus_probability_small {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T)
    {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ n : ℕ, (offspringSeqLaw μ).toMeasure.real
      {ω | η < heightOscillation B n T δ ω} ≤ ε := by
  obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_pos_eventually_forestHeight_modulus_small h hT hη hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hsmall
  choose d hd hp using fun i : Fin (N + 1) =>
    exists_pos_height_modulus_probability_small μ B i T hη hε
  have hne : (Finset.univ : Finset (Fin (N + 1))).Nonempty := ⟨⟨0, by omega⟩, by simp⟩
  let dmin := Finset.univ.inf' hne d
  have hmin : 0 < dmin := by
    obtain ⟨i, _, he⟩ := Finset.exists_mem_eq_inf' hne d
    change 0 < Finset.univ.inf' hne d
    rw [he]
    exact hd i
  let δ := min δ₀ dmin
  refine ⟨δ, lt_min hδ₀ hmin, ?_⟩
  intro n
  by_cases hn : N ≤ n
  · apply le_trans (measureReal_mono ?_) (hN n hn)
    intro ω hω
    exact hω.trans_le (heightOscillation_mono B n T.coe_nonneg hδ₀.le (min_le_left _ _) ω)
  · let i : Fin (N + 1) := ⟨n, by omega⟩
    have hle : δ ≤ d i := (min_le_right _ _).trans (Finset.inf'_le d (Finset.mem_univ i))
    apply le_trans (measureReal_mono ?_) (hp i)
    intro ω hω
    exact hω.trans_le (heightOscillation_mono B n T.coe_nonneg (hd i).le hle ω)

end BGW.StableTrees.HeightTightness
