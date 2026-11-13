/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessAncestralSupport
import BGW.Probability.Stieltjes

/-!
# Initial source truncation and erasure

Initial time truncation is characterized by distribution functions, without choosing a
crossing time.
Capping a Stieltjes function therefore erases the top mass of its pushed-forward source,
including a partial boundary atom and the case where the entire source is erased.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
namespace BGW.StableTrees
open BGW.Probability

/-- A measurable time change and a height translation commute with the fresh pushforward. -/
theorem map_fresh_height_translation {μ : Measure ℝ} {τ : ℝ → ℝ} (hτ : Measurable τ)
    {φ ψ : ℝ → ℝ≥0} (hφ : Measurable φ) (hψ : Measurable ψ) (K : ℝ≥0)
    (he : ∀ᵐ x ∂μ, φ (τ x) = ψ x + K) :
    (μ.map τ).map φ = (μ.map ψ).map (fun h => h + K) := by
  have hK : Measurable (fun h : ℝ≥0 => h + K) := measurable_id.add_const K
  rw [Measure.map_map hφ hτ, Measure.map_map hK hψ]
  exact Measure.map_congr he



private theorem initial_cdf_Iio {ν ν' : Measure ℝ} {k : ℝ≥0∞}
    (hcdf : ∀ a : ℝ, ν' (Iic a) = min (ν (Iic a)) k) (a : ℝ) :
    ν' (Iio a) = min (ν (Iio a)) k := by
  let D := {q : ℚ // (q : ℝ) < a}
  have hdir : Directed (· ⊆ ·) (fun q : D => Iic (q.1 : ℝ)) := by
    intro p q
    refine ⟨⟨max p.1 q.1, by simpa only [Rat.cast_max] using max_lt p.2 q.2⟩, ?_, ?_⟩
    · exact Iic_subset_Iic.mpr (by exact_mod_cast le_max_left p.1 q.1)
    · exact Iic_subset_Iic.mpr (by exact_mod_cast le_max_right p.1 q.1)
  have hun : (⋃ q : D, Iic (q.1 : ℝ)) = Iio a := by
    ext x
    constructor
    · intro hx
      obtain ⟨q, hq⟩ := mem_iUnion.mp hx
      exact hq.trans_lt q.2
    · intro hx
      obtain ⟨q, hxq, hqa⟩ := exists_rat_btwn (show x < a from hx)
      exact mem_iUnion.mpr ⟨⟨q, hqa⟩, hxq.le⟩
  rw [← hun, hdir.measure_iUnion, hdir.measure_iUnion]
  simp_rw [hcdf]
  exact (iSup_inf_eq _ _).symm

/-- A monotone height map preserves initial-segment distribution-function truncation. -/
theorem map_eq_eraseMass_of_initial_cdf {ν ν' : Measure ℝ}
    [IsFiniteMeasure ν] [IsFiniteMeasure ν'] {φ : ℝ → ℝ≥0}
    (hφ : Measurable φ) (hmono : Monotone φ) (m : ℝ≥0∞)
    (htot : ν' univ = ν univ - m)
    (hcdf : ∀ a : ℝ, ν' (Iic a) = min (ν (Iic a)) (ν univ - m)) :
    ν'.map φ = eraseMass m (ν.map φ) := by
  apply Measure.ext_of_Iic
  intro h
  rw [eraseMass_Iic, Measure.map_apply hφ measurableSet_Iic,
    Measure.map_apply hφ measurableSet_Iic, Measure.map_apply hφ MeasurableSet.univ,
    preimage_univ]
  let B := φ ⁻¹' Iic h
  change ν' B = min (ν B) (ν univ - m)
  by_cases hb : B.Nonempty
  · by_cases hba : BddAbove B
    · let c := sSup B
      have hsub : B ⊆ Iic c := fun _ hx => le_csSup hba hx
      have hcontains : Iio c ⊆ B := by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := (lt_csSup_iff hba hb).mp hx
        exact (hmono hxy.le).trans hy
      by_cases hc : c ∈ B
      · have heq : B = Iic c := by
          apply subset_antisymm hsub
          intro x hx
          rcases (show x ≤ c from hx).lt_or_eq with hlt | rfl
          · exact hcontains hlt
          · exact hc
        rw [heq, hcdf]
      · have heq : B = Iio c := by
          apply subset_antisymm _ hcontains
          intro x hx
          exact lt_of_le_of_ne (show x ≤ c from hsub hx) (fun he => hc (he ▸ hx))
        rw [heq, initial_cdf_Iio hcdf]
    · have heq : B = univ := by
        apply eq_univ_of_forall
        intro x
        obtain ⟨y, hy, hxy⟩ := not_bddAbove_iff.mp hba x
        exact (hmono hxy.le).trans hy
      rw [heq, htot, min_eq_right tsub_le_self]
  · rw [not_nonempty_iff_eq_empty.mp hb, measure_empty, measure_empty, zero_min]




/-- A monotone height map turns a capped Stieltjes source into top-mass erasure. -/
theorem map_stieltjes_min_eq_eraseMass {F G : StieltjesFunction ℝ} {T c : ℝ}
    (hT : 0 ≤ T) (hc : c ≤ F T)
    (he : ∀ x ∈ Icc 0 T, G x = min (F x) c)
    {φ : ℝ → ℝ≥0} (hφ : Measurable φ) (hmono : Monotone φ) :
    (G.measure.restrict (Ioc 0 T)).map φ =
      eraseMass (ENNReal.ofReal (F T - c)) ((F.measure.restrict (Ioc 0 T)).map φ) := by
  let : IsFiniteMeasure (F.measure.restrict (Ioc 0 T)) := ⟨by
    rw [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  let : IsFiniteMeasure (G.measure.restrict (Ioc 0 T)) := ⟨by
    rw [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  exact map_eq_eraseMass_of_initial_cdf hφ hmono _
    (stieltjes_min_total hT hc he) (stieltjes_min_initial_cdf hT hc he)

/-- A measurable height map agreeing with a monotone clock on the original source also erases. -/
theorem map_stieltjes_min_eq_eraseMass_of_ae {F G : StieltjesFunction ℝ} {T c : ℝ}
    (hT : 0 ≤ T) (hc : c ≤ F T)
    (he : ∀ x ∈ Icc 0 T, G x = min (F x) c)
    {φ ψ : ℝ → ℝ≥0} (hψ : Measurable ψ) (hmono : Monotone ψ)
    (heq : ∀ᵐ x ∂F.measure.restrict (Ioc 0 T), φ x = ψ x) :
    (G.measure.restrict (Ioc 0 T)).map φ =
      eraseMass (ENNReal.ofReal (F T - c)) ((F.measure.restrict (Ioc 0 T)).map φ) := by
  have hle := stieltjes_min_restrict_le hT he
  have heq' : ∀ᵐ x ∂G.measure.restrict (Ioc 0 T), φ x = ψ x := heq.filter_mono (ae_mono hle)
  rw [Measure.map_congr heq', Measure.map_congr heq]
  exact map_stieltjes_min_eq_eraseMass hT hc he hψ hmono

end BGW.StableTrees
