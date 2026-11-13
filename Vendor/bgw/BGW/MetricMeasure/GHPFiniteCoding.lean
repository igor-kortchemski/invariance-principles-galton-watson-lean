/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.GromovHausdorffProkhorov
public import BGW.MetricMeasure.FiniteProkhorov

/-!
# Countable data for finite measured metric spaces

A labelled finite carrier is encoded by rounded pairwise distances and rounded
atomic masses. Equal codes give a measure comparison and a bijection of small
distortion, hence a bound for the exact GHP distance. Zero-mass points are
included in both arrays.

Adapted from `Freezing2/Geometry/GHPFiniteCoding.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped BigOperators

universe u

namespace BGW.MetricMeasure

variable {X Y : Type u} [MetricSpace X] [MeasurableSpace X]
  [MetricSpace Y] [MeasurableSpace Y]

/-- Distance and weight arrays of a finite labelled measured space. -/
noncomputable def finiteMeasuredCode {n : ℕ} (μ : Measure X) (e : X ≃ Fin n) (ε : ℝ) :
    (Fin n → Fin n → ℤ) × (Fin n → ℤ) :=
  (fun i j ↦ ⌊dist (e.symm i) (e.symm j) / ε⌋,
    fun i ↦ ⌊μ.real {e.symm i} / (ε / (n : ℝ))⌋)

/-- Coinciding finite codes control the exact summed GHP infimum. -/
theorem ghpDistance_le_of_finiteMeasuredCode_eq
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] [BorelSpace X] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n : ℕ} (e : X ≃ Fin n) (f : Y ≃ Fin n) {ε : ℝ} (hε : 0 < ε)
    (hcode : finiteMeasuredCode μ e ε = finiteMeasuredCode ν f ε) :
    ghpDistance μ ν ≤ 3 * ε := by
  classical
  let φ : X ≃ Y := e.trans f.symm
  have hφ : Measurable φ := measurable_of_countable _
  have hn : (0 : ℝ) < n := by
    have hcard : Fintype.card X = n := by simpa using Fintype.card_congr e
    rw [← hcard]
    exact_mod_cast Fintype.card_pos
  have hdist (x x' : X) : |dist x x' - dist (φ x) (φ x')| ≤ ε := by
    apply abs_sub_le_of_floor_div_eq hε
    have h := congrFun (congrFun (congrArg Prod.fst hcode) (e x)) (e x')
    simpa only [finiteMeasuredCode, Equiv.symm_apply_apply, φ, Equiv.trans_apply] using h
  have hmass (y : Y) : (μ.map φ).real {y} = μ.real {φ.symm y} := by
    have hpre : φ ⁻¹' {y} = {φ.symm y} := by
      ext x
      exact φ.eq_symm_apply.symm
    simp only [measureReal_def, Measure.map_apply hφ (measurableSet_singleton y), hpre]
  have hatom (y : Y) : |(μ.map φ).real {y} - ν.real {y}| ≤ ε / (n : ℝ) := by
    rw [hmass]
    apply abs_sub_le_of_floor_div_eq (div_pos hε hn)
    have h := congrFun (congrArg Prod.snd hcode) (f y)
    simpa only [finiteMeasuredCode, Equiv.symm_apply_apply, φ, Equiv.symm_trans_apply,
      Equiv.symm_symm] using h
  have hP : levyProkhorovDist (μ.map φ) ν ≤ ε := by
    have hcard : Fintype.card Y = n := by simpa using Fintype.card_congr f
    calc
      _ ≤ ∑ y, |(μ.map φ).real {y} - ν.real {y}| :=
        levyProkhorovDist_le_sum_atoms _ _
      _ ≤ ∑ _y : Y, ε / (n : ℝ) := Finset.sum_le_sum (fun y _ ↦ hatom y)
      _ = ε := by simp only [Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul]; field_simp
  have h := ghpDistance_le_of_approx μ ν φ hφ hε
    (fun x x' ↦ (hdist x x').trans (by linarith))
    (r := 0) (fun y ↦ ⟨φ.symm y, by simp⟩) hP
  linarith

/-- The same comparison for dependent codes whose first entry records the
number of points. Equality of the cardinality entries is derived from the
code equality, so the caller need not identify the two index types first. -/
theorem ghpDistance_le_of_sigma_finiteMeasuredCode_eq
    [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] [BorelSpace X] [BorelSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {n m : ℕ} (e : X ≃ Fin n) (f : Y ≃ Fin m) {ε : ℝ} (hε : 0 < ε)
    (hcode : (⟨n, finiteMeasuredCode μ e ε⟩ :
        Σ k : ℕ, (Fin k → Fin k → ℤ) × (Fin k → ℤ)) =
      ⟨m, finiteMeasuredCode ν f ε⟩) :
    ghpDistance μ ν ≤ 3 * ε := by
  obtain ⟨hn, hc⟩ := Sigma.mk.inj_iff.mp hcode
  subst m
  exact ghpDistance_le_of_finiteMeasuredCode_eq μ ν e f hε (eq_of_heq hc)

end BGW.MetricMeasure

