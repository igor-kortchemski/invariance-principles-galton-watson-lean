/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Measurable
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Indicator

/-!
# Fixed discontinuities of laws on the Skorokhod space

A point-finite measurable family has only countably many members of positive measure.
Apply this to jumps larger than a fixed threshold, then take a countable union.
-/

@[expose] public section

namespace BGW.Skorokhod

open Set Filter Topology MeasureTheory

open scoped ENNReal

/-- A point-finite measurable family has countably many members of positive finite measure. -/
theorem countable_measure_ne_zero_of_point_finite {Ω I : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (A : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hfin : ∀ x, {i | x ∈ A i}.Finite) :
    {i | μ (A i) ≠ 0}.Countable := by
  classical
  have hfinite {ε : ℝ} (hε : 0 < ε) : {i | ε < μ.real (A i)}.Finite := by
    by_contra hinf
    let e := Set.Infinite.natEmbedding _ hinf
    let u : ℕ → I := fun n => (e n).val
    have hu : Function.Injective u := Subtype.val_injective.comp e.injective
    have hlim : Tendsto (fun n => μ (A (u n))) atTop (𝓝 0) := by
      have h := tendsto_measure_of_tendsto_indicator_of_isFiniteMeasure
        (A := (∅ : Set Ω)) atTop μ (fun n => hA (u n)) ?_
      · simpa only [measure_empty] using h
      · intro x
        have hf : {n | x ∈ A (u n)}.Finite := (hfin x).preimage hu.injOn
        have he := hf.eventually_cofinite_notMem
        rw [Nat.cofinite_eq_atTop] at he
        filter_upwards [he] with n hn
        simp only [mem_empty_iff_false, iff_false]
        exact hn
    have hreal : Tendsto (fun n => μ.real (A (u n))) atTop (𝓝 0) := by
      simpa only [Measure.real, ENNReal.toReal_zero, Function.comp_def] using
        (ENNReal.continuousAt_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).tendsto.comp hlim
    have hle : ε ≤ 0 := ge_of_tendsto' hreal (fun n => (e n).property.le)
    exact (not_le_of_gt hε) hle
  apply (countable_iUnion fun n : ℕ =>
    (hfinite (show 0 < 1 / (n + 1 : ℝ) by positivity)).countable).mono
  intro i hi
  have hpos : 0 < μ.real (A i) :=
    ENNReal.toReal_pos hi (measure_ne_top μ (A i))
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hpos
  exact mem_iUnion.mpr ⟨n, hn⟩

variable {T : ℝ} {E : Type*}

/-- A law on `D` has at most countably many fixed discontinuity times (C12(3)). -/
theorem countable_setOf_measure_jump_ne_zero [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] (P : ProbabilityMeasure (D T E)) :
    {t : Set.Icc (0 : ℝ) T |
      (P : Measure (D T E)) {f | Function.leftLim f t ≠ f t} ≠ 0}.Countable := by
  classical
  let A : ℕ → Set.Icc (0 : ℝ) T → Set (D T E) := fun n t =>
    {f | 1 / (n + 1 : ℝ) < dist (Function.leftLim f t) (f t)}
  have hA (n : ℕ) (t : Set.Icc (0 : ℝ) T) : MeasurableSet (A n t) :=
    measurableSet_lt measurable_const
      ((measurable_leftLim_eval t).dist (measurable_eval t))
  have hc (n : ℕ) : {t | (P : Measure (D T E)) (A n t) ≠ 0}.Countable :=
    countable_measure_ne_zero_of_point_finite (P : Measure (D T E)) (A n) (hA n)
      (fun f => finite_setOf_jump_gt f (by positivity))
  apply (countable_iUnion hc).mono
  intro t ht
  have heq : {f : D T E | Function.leftLim f t ≠ f t} = ⋃ n, A n t := by
    ext f
    simp only [mem_ofPred_eq, mem_iUnion]
    constructor
    · intro hf
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (dist_pos.mpr hf)
      exact ⟨n, hn⟩
    · rintro ⟨n, hn⟩
      exact dist_pos.mp ((show 0 < 1 / (n + 1 : ℝ) by positivity).trans hn)
  change (P : Measure (D T E)) {f | Function.leftLim f t ≠ f t} ≠ 0 at ht
  rw [heq] at ht
  have hex : ∃ n, (P : Measure (D T E)) (A n t) ≠ 0 := by
    by_contra! hzero
    exact ht (measure_iUnion_null hzero)
  obtain ⟨n, hn⟩ := hex
  exact mem_iUnion.mpr ⟨n, hn⟩

end BGW.Skorokhod
