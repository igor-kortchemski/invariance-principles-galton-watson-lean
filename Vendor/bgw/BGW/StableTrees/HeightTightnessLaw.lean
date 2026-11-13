/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessUniformModulus
public import BGW.StableTrees.HeightTightnessCompact
public import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Tightness of all interpolated forest-height laws

Uniform modulus estimates over every scaling index and a summable allocation of
exceptional probabilities give one compact path set. The paths start at zero,
and Arzelà-Ascoli supplies compactness. The zero horizon is handled directly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.HeightTightness

/-- The laws of the normalized height paths on `[0,T]` are tight. -/
theorem isTightMeasureSet_forestHeightLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (T : ℝ≥0) :
    IsTightMeasureSet (Set.range fun n : ℕ =>
      ((offspringSeqLaw μ).map (forestHeightPath B n T) :
        Measure C(Set.Icc (0 : ℝ) (T : ℝ), ℝ))) := by
  by_cases hT : T = 0
  · subst T
    let C₀ := C(Set.Icc (0 : ℝ) ((0 : ℝ≥0) : ℝ), ℝ)
    have hf (n : ℕ) : forestHeightPath B n 0 = fun _ : ℕ → ℕ => (0 : C₀) := by
      funext ω
      ext t
      have ht : (t : ℝ) = 0 := le_antisymm t.property.2 t.property.1
      change B n / n * forestHeightLin ω (n * (t : ℝ)) = 0
      simp [ht, forestHeightLin, forestHeight]
    have he : (fun n : ℕ => ((offspringSeqLaw μ).map (forestHeightPath B n 0) : Measure C₀)) =
        fun _ : ℕ => ((offspringSeqLaw μ).map (fun _ : ℕ → ℕ => (0 : C₀)) : Measure C₀) := by
      funext n
      rw [hf n]
    rw [he, Set.range_const]
    exact isTightMeasureSet_singleton
  have hTpos : 0 < T := pos_iff_ne_zero.mpr hT
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨e, _, he, heε⟩ := ENNReal.lt_iff_exists_real_btwn.mp hε
  have hepos : 0 < e := ENNReal.ofReal_pos.mp he
  let b (j : ℕ) : ℝ := (e / 2) * (1 / 2) ^ j
  have hbpos (j : ℕ) : 0 < b j := by dsimp [b]; positivity
  choose δ hδ hp using fun j : ℕ => exists_pos_uniform_height_modulus_probability_small h
    hTpos (η := 1 / (j + 1 : ℝ)) (by positivity) (hbpos j)
  obtain ⟨K, hK, hKmem⟩ := exists_isCompact_of_height_moduli T δ hδ
  refine ⟨K, hK, ?_⟩
  rintro ν ⟨n, rfl⟩
  change (((offspringSeqLaw μ).map (forestHeightPath B n T)) :
    Measure C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) Kᶜ ≤ ε
  have hmPath : Measurable (forestHeightPath B n T) := by
    simpa only [forestPairPath, Function.comp_def] using (measurable_forestPairPath B n T).snd
  rw [ProbabilityMeasure.toMeasure_map, Measure.map_apply
    (f := forestHeightPath B n T) hmPath hK.measurableSet.compl]
  let E (j : ℕ) : Set (ℕ → ℕ) := {ω | 1 / (j + 1 : ℝ) < heightOscillation B n T (δ j) ω}
  have hsub : (forestHeightPath B n T) ⁻¹' Kᶜ ⊆ ⋃ j, E j := by
    intro ω hω
    by_contra hh
    have hgood (j : ℕ) (s t : Set.Icc (0 : ℝ) (T : ℝ)) (hd : |(s : ℝ) - t| ≤ δ j) :
        |forestHeightPath B n T ω s - forestHeightPath B n T ω t| ≤ 1 / (j + 1 : ℝ) := by
      have hm : heightOscillation B n T (δ j) ω ≤ 1 / (j + 1 : ℝ) :=
        le_of_not_gt (fun hbad => hh (Set.mem_iUnion.mpr ⟨j, hbad⟩))
      exact (heightDifference_le_heightOscillation B n T.coe_nonneg ω s t hd).trans hm
    have hz : forestHeightPath B n T ω ⟨0, le_rfl, T.coe_nonneg⟩ = 0 := by
      simp [forestHeightPath, forestHeightLin, forestHeight]
    exact hω (hKmem _ hz hgood)
  have hprob (j : ℕ) : (offspringSeqLaw μ).toMeasure (E j) ≤ ENNReal.ofReal (b j) := by
    rw [← ofReal_measureReal]
    exact ENNReal.ofReal_le_ofReal (hp j n)
  have hs : Summable b :=
    (summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left (e / 2)
  have hsum : ∑' j, b j = e := by
    dsimp only [b]
    rw [tsum_mul_left, tsum_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)]
    norm_num
  calc
    _ ≤ (offspringSeqLaw μ).toMeasure (⋃ j, E j) := measure_mono hsub
    _ ≤ ∑' j, (offspringSeqLaw μ).toMeasure (E j) := measure_iUnion_le _
    _ ≤ ∑' j, ENNReal.ofReal (b j) := ENNReal.tsum_le_tsum hprob
    _ = ENNReal.ofReal e := by
      rw [← ENNReal.ofReal_tsum_of_nonneg (fun j => (hbpos j).le) hs, hsum]
    _ ≤ ε := heε.le

end BGW.StableTrees.HeightTightness
