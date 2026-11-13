/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Probability.ProductMeasure
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# First-success masses for product sequences

The event of `r` failures followed by a success in a prescribed set is a finite
box. Summing its masses gives the normalized restriction to the success set.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The first visit to `Q` is at `r`, and the visited point also belongs to `A`. -/
def firstSuccess (Q A : Set Ω) (r : ℕ) : Set (ℕ → Ω) :=
  {ω | ω r ∈ Q ∩ A ∧ ∀ i < r, ω i ∉ Q}

omit [MeasurableSpace Ω] in
private theorem firstSuccess_eq_pi (Q A : Set Ω) (r : ℕ) :
    firstSuccess Q A r = (↑(Finset.range (r + 1)) : Set ℕ).pi
      (fun i => if i = r then Q ∩ A else Qᶜ) := by
  ext ω
  change (ω r ∈ Q ∩ A ∧ ∀ i < r, ω i ∉ Q) ↔
    ∀ i ∈ (↑(Finset.range (r + 1)) : Set ℕ), ω i ∈ if i = r then Q ∩ A else Qᶜ
  constructor
  · rintro ⟨hr, hpre⟩ i hi
    have hil : i ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    by_cases he : i = r
    · simpa only [he, ite_true] using hr
    · rw [ite_eq_right he]
      exact hpre i (by omega)
  · intro h
    refine ⟨?_, fun i hi => ?_⟩
    · simpa only [ite_true] using h r (by simp)
    · have he : i ≠ r := by omega
      have hh := h i (by simp; omega)
      rwa [ite_eq_right he] at hh

/-- First-success events are measurable. -/
theorem measurableSet_firstSuccess {Q A : Set Ω} (hQ : MeasurableSet Q)
    (hA : MeasurableSet A) (r : ℕ) : MeasurableSet (firstSuccess Q A r) := by
  rw [firstSuccess_eq_pi]
  apply MeasurableSet.pi (Finset.countable_toSet _)
  intro i _
  split_ifs
  · exact hQ.inter hA
  · exact hQ.compl

/-- A first-success event has the expected finite product mass. -/
theorem infinitePi_firstSuccess_atom (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {Q A : Set Ω} (hQ : MeasurableSet Q) (hA : MeasurableSet A) (r : ℕ) :
    (Measure.infinitePi (fun _ : ℕ => ρ)) (firstSuccess Q A r) =
      (ρ Qᶜ) ^ r * ρ (Q ∩ A) := by
  rw [firstSuccess_eq_pi, Measure.infinitePi_pi]
  · rw [Finset.prod_range_succ]
    have hp : (∏ i ∈ Finset.range r, ρ (if i = r then Q ∩ A else Qᶜ)) = (ρ Qᶜ) ^ r := by
      calc
        _ = ∏ _i ∈ Finset.range r, ρ Qᶜ := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [ite_eq_right (ne_of_lt (Finset.mem_range.mp hi))]
        _ = _ := by simp
    rw [hp, ite_eq_left rfl]
  · intro i _
    split_ifs
    · exact hQ.inter hA
    · exact hQ.compl

omit [MeasurableSpace Ω] in
private theorem firstSuccess_disjoint (Q A : Set Ω) :
    Pairwise (fun r s => Disjoint (firstSuccess Q A r) (firstSuccess Q A s)) := by
  intro r s hrs
  apply Set.disjoint_left.mpr
  intro ω hr hs
  rcases lt_or_gt_of_ne hrs with h | h
  · exact hs.2 r h hr.1.1
  · exact hr.2 s h hs.1.1

/-- Summing first-success masses gives the conditional mass in the success set. -/
theorem infinitePi_firstSuccess_mass (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {Q A : Set Ω} (hQ : MeasurableSet Q) (hA : MeasurableSet A) :
    (Measure.infinitePi (fun _ : ℕ => ρ)) (⋃ r, firstSuccess Q A r) =
      (ρ Q)⁻¹ * ρ (Q ∩ A) := by
  rw [measure_iUnion (firstSuccess_disjoint Q A) (measurableSet_firstSuccess hQ hA)]
  simp_rw [infinitePi_firstSuccess_atom ρ hQ hA]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric, prob_compl_eq_one_sub hQ,
    ENNReal.sub_sub_cancel ENNReal.one_ne_top (prob_le_one : ρ Q ≤ 1)]

/-- A positive-mass success set is visited almost surely by an iid sequence. -/
theorem infinitePi_ae_exists_success (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    {Q : Set Ω} (hQ : MeasurableSet Q) (hq : ρ Q ≠ 0) :
    ∀ᵐ ω ∂Measure.infinitePi (fun _ : ℕ => ρ), ∃ r, ω r ∈ Q := by
  have hm : (Measure.infinitePi (fun _ : ℕ => ρ)) (⋃ r, firstSuccess Q univ r) = 1 := by
    rw [infinitePi_firstSuccess_mass ρ hQ MeasurableSet.univ, inter_univ,
      ENNReal.inv_mul_cancel hq (measure_ne_top _ _)]
  have ha := (mem_ae_iff_prob_eq_one
    (MeasurableSet.iUnion (measurableSet_firstSuccess hQ MeasurableSet.univ))).mpr hm
  filter_upwards [ha] with ω hω
  obtain ⟨r, hr⟩ := mem_iUnion.mp hω
  exact ⟨r, hr.1.1⟩

end BGW.StableTrees.DiscreteForest
