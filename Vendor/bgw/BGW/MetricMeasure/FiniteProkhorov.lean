/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.MetricMeasure.ProkhorovBounds
public import Mathlib.Algebra.Order.Floor.Ring

/-!
# Finite atom bounds for Prokhorov distance

The difference on any event is bounded by the sum of the absolute differences
of its atomic masses. This gives a Prokhorov bound without a lower bound on
nonzero masses or on distances between points. Quantizing each atom at a
scale divided by the number of points yields countable approximation data.

Adapted from `Freezing2/Probability/FiniteProkhorov.lean` in
`igor-kortchemski/uniform-attachment-freezing-scaling-limits`, commit
`8bace72d36cdf7d250414f3d98acfaa415de23d9` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory Metric Set
open scoped BigOperators ENNReal

namespace BGW.MetricMeasure

variable {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]

/-- Atomic mass discrepancies bound the discrepancy on every event. -/
theorem abs_measureReal_sub_le_sum_atoms (μ ν : Measure X)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (B : Set X) :
    |μ.real B - ν.real B| ≤ ∑ x, |μ.real {x} - ν.real {x}| := by
  classical
  let s : Finset X := (Set.toFinite B).toFinset
  have hs : (s : Set X) = B := (Set.toFinite B).coe_toFinset
  calc
    |μ.real B - ν.real B| = |∑ x ∈ s, (μ.real {x} - ν.real {x})| := by
      rw [Finset.sum_sub_distrib, sum_measureReal_singleton, sum_measureReal_singleton, hs]
    _ ≤ ∑ x ∈ s, |μ.real {x} - ν.real {x}| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ x, |μ.real {x} - ν.real {x}| :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun _ _ _ ↦ abs_nonneg _)

/-- On a finite metric space, the genuine Prokhorov distance is at most the
sum of absolute atomic mass discrepancies. No full-support premise is used. -/
theorem levyProkhorovDist_le_sum_atoms [MetricSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    levyProkhorovDist μ ν ≤ ∑ x, |μ.real {x} - ν.real {x}| := by
  classical
  have hδ : 0 ≤ ∑ x, |μ.real {x} - ν.real {x}| :=
    Finset.sum_nonneg (fun _ _ ↦ abs_nonneg _)
  apply levyProkhorovDist_le_of_forall_le μ ν hδ
  intro ε B hε _
  have hε0 : 0 < ε := hδ.trans_lt hε
  apply (ENNReal.toReal_le_toReal (measure_ne_top μ B)
    (ENNReal.add_ne_top.mpr ⟨measure_ne_top ν _, ENNReal.ofReal_ne_top⟩)).mp
  rw [ENNReal.toReal_add (measure_ne_top ν _) ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hε0.le]
  change μ.real B ≤ ν.real (thickening ε B) + ε
  have hB := (abs_le.mp (abs_measureReal_sub_le_sum_atoms μ ν B)).2
  calc
    μ.real B ≤ ν.real B + ∑ x, |μ.real {x} - ν.real {x}| := by linarith
    _ ≤ ν.real (thickening ε B) + ε :=
      add_le_add (measureReal_mono (self_subset_thickening hε0 B)) hε.le

/-- Equality of integer parts at scale `η` bounds the unscaled discrepancy. -/
theorem abs_sub_le_of_floor_div_eq {a b η : ℝ} (hη : 0 < η)
    (h : ⌊a / η⌋ = ⌊b / η⌋) : |a - b| ≤ η := by
  have hi := Int.abs_sub_lt_one_of_floor_eq_floor h
  rw [← sub_div, abs_div, abs_of_pos hη] at hi
  simpa only [one_mul] using ((div_lt_iff₀ hη).mp hi).le

/-- Equal rounded atomic masses give an error proportional to the number of
points. All atoms, including zero-mass atoms, are part of the code. -/
theorem levyProkhorovDist_le_card_mul_of_floor_atoms_eq [MetricSpace X] [BorelSpace X]
    (μ ν : Measure X) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {η : ℝ} (hη : 0 < η)
    (hcode : ∀ x, ⌊μ.real {x} / η⌋ = ⌊ν.real {x} / η⌋) :
    levyProkhorovDist μ ν ≤ (Fintype.card X : ℝ) * η := by
  calc
    _ ≤ ∑ x, |μ.real {x} - ν.real {x}| := levyProkhorovDist_le_sum_atoms μ ν
    _ ≤ ∑ _x : X, η := Finset.sum_le_sum (fun x _ ↦
      abs_sub_le_of_floor_div_eq hη (hcode x))
    _ = (Fintype.card X : ℝ) * η := by simp

/-- The finite weight code uses a mesh of `ε / card X`, so equal codes are
within `ε` independently of the number of finite points. -/
noncomputable def finiteWeightCode (μ : Measure X) (ε : ℝ) : X → ℤ :=
  fun x ↦ ⌊μ.real {x} / (ε / (Fintype.card X : ℝ))⌋

theorem levyProkhorovDist_le_of_finiteWeightCode_eq [Nonempty X]
    [MetricSpace X] [BorelSpace X] (μ ν : Measure X)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (hε : 0 < ε) (hcode : finiteWeightCode μ ε = finiteWeightCode ν ε) :
    levyProkhorovDist μ ν ≤ ε := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have h := levyProkhorovDist_le_card_mul_of_floor_atoms_eq μ ν (div_pos hε hc)
    (fun x ↦ congrFun hcode x)
  have he : (Fintype.card X : ℝ) * (ε / (Fintype.card X : ℝ)) = ε := by
    field_simp
  rwa [he] at h

end BGW.MetricMeasure

