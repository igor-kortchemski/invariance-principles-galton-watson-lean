/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxCycleMean

/-!
# The killed-gap Green kernel

The gap walk started at `x > 0` is killed when the original increment walk first
reaches `x`. Prepending `x` zero offspring values embeds it in a first weak cycle.
Duality then gives a finite Green kernel without any offspring second moment.
The bound here is geometric in `x`; it is not the scale-uniform renewal estimate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- A killed-gap walk started at `x` survives through time `k` and is then at `y`. -/
def killedGapEvent (x y k : ℕ) : Set (ℕ → ℕ) :=
  {ω | walk ω k = (x : ℤ) - (y : ℤ) ∧ ∀ u ≤ k, walk ω u < (x : ℤ)}

/-- The Green kernel of the gap walk killed on entering the nonpositive half-line. -/
noncomputable def killedGapGreen (μ : PMF ℕ) (x y : ℕ) : ℝ≥0∞ :=
  ∑' k : ℕ, (offspringSeqLaw μ).toMeasure (killedGapEvent x y k)

/-- Each finite killed-gap transition event is measurable. -/
theorem measurableSet_killedGapEvent (x y k : ℕ) : MeasurableSet (killedGapEvent x y k) := by
  have hm : MeasurableSet {ω : ℕ → ℕ | ∀ u ≤ k, walk ω u < (x : ℤ)} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter fun u => MeasurableSet.iInter fun _ =>
      measurableSet_lt (measurable_walk u) measurable_const
  exact (measurableSet_eq_fun (measurable_walk k) measurable_const).inter hm

private def zeroPrefix (n : ℕ) : Set (ℕ → ℕ) := {ω | ∀ i < n, ω i = 0}

private theorem walk_zeroPrefix {ω : ℕ → ℕ} {n : ℕ} (hω : ω ∈ zeroPrefix n)
    {u : ℕ} (hu : u ≤ n) : walk ω u = -(u : ℤ) := by
  unfold walk
  have he : ∀ i ∈ Finset.range u, ω i = 0 := by
    intro i hi
    exact hω i (by have := Finset.mem_range.mp hi; omega)
  calc
    _ = ∑ _i ∈ Finset.range u, (-1 : ℤ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [he i hi]
      simp
    _ = -(u : ℤ) := by simp

private theorem zeroPrefix_mass (μ : PMF ℕ) (n : ℕ) :
    (offspringSeqLaw μ).toMeasure (zeroPrefix n) = (μ 0) ^ n := by
  have he : zeroPrefix n = (fun ω (i : Fin n) => ω i) ⁻¹' {fun _ : Fin n => 0} := by
    ext ω
    change (∀ i < n, ω i = 0) ↔ (fun i : Fin n => ω i) = (fun _ => 0)
    constructor
    · intro h
      funext i
      exact h i i.isLt
    · intro h i hi
      exact congrFun h ⟨i, hi⟩
  rw [he, ← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    map_offspringSeqLaw_initial, Measure.pi_singleton]
  simp [PMF.toMeasure_apply_singleton]

private theorem preStopped_zeroPrefix (n : ℕ) :
    PreStopped (fun _ : ℕ → ℕ => (n : ℕ∞)) (zeroPrefix n) := by
  intro m ω ξ hm he
  have hnm : n = m := ENat.natCast_inj.mp hm
  subst m
  refine ⟨rfl, ?_⟩
  constructor
  · intro h i hi
    rw [← he i hi]
    exact h i hi
  · intro h i hi
    rw [he i hi]
    exact h i hi

private theorem zeroPrefix_shift_mass (μ : PMF ℕ) (n : ℕ) {A : Set (ℕ → ℕ)}
    (hA : MeasurableSet A) :
    (offspringSeqLaw μ).toMeasure (zeroPrefix n ∩ shiftSeq n ⁻¹' A) =
      (μ 0) ^ n * (offspringSeqLaw μ).toMeasure A := by
  have hN : IsSeqStoppingTime (fun _ : ℕ → ℕ => (n : ℕ∞)) :=
    fun _ _ _ hm _ => ⟨hm, Iff.rfl⟩
  have hfin : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, (n : ℕ∞) ≠ ⊤ := by simp
  have h := stoppedRestart μ (fun _ => (n : ℕ∞)) hN hfin (preStopped_zeroPrefix n) hA
  have he : {ω : ℕ → ℕ | ∃ m : ℕ, (n : ℕ∞) = m ∧ shiftSeq m ω ∈ A} =
      shiftSeq n ⁻¹' A := by
    ext ω
    constructor
    · rintro ⟨m, hm, hA⟩
      have he : n = m := ENat.natCast_inj.mp hm
      subst m
      exact hA
    · intro hA
      exact ⟨n, rfl, hA⟩
  rw [he, zeroPrefix_mass] at h
  exact h

private theorem zeroPrefix_killed_subset (x y k : ℕ) :
    zeroPrefix x ∩ shiftSeq x ⁻¹' killedGapEvent x y k ⊆ negativeLevelEvent y (x + k) := by
  intro ω hω
  obtain ⟨hz, hk⟩ := hω
  have hwx : walk ω x = -(x : ℤ) := walk_zeroPrefix hz le_rfl
  have hwalk (u : ℕ) : walk ω (x + u) = walk (shiftSeq x ω) u + walk ω x := by
    rw [walk_shiftSeq]
    ring
  refine ⟨?_, fun u hu huk => ?_⟩
  · rw [hwalk, hk.1, hwx]
    ring
  · by_cases hux : u ≤ x
    · rw [walk_zeroPrefix hz hux]
      omega
    · have htail := hk.2 (u - x) (by omega)
      have he : x + (u - x) = u := by omega
      rw [← he, hwalk, hwx]
      omega

/-- A geometric entrance bound controls every killed-gap transition series.
It proves finiteness, but does not replace the sharper weak-ladder renewal bound. -/
theorem killedGapGreen_weighted_le_one (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (x y : ℕ) :
    (μ 0) ^ x * killedGapGreen μ x y ≤ 1 := by
  rw [killedGapGreen, ← ENNReal.tsum_mul_left]
  calc
    _ = ∑' k : ℕ, (offspringSeqLaw μ).toMeasure
        (zeroPrefix x ∩ shiftSeq x ⁻¹' killedGapEvent x y k) := by
      apply tsum_congr
      intro k
      exact (zeroPrefix_shift_mass μ x (measurableSet_killedGapEvent x y k)).symm
    _ ≤ ∑' k : ℕ, (offspringSeqLaw μ).toMeasure (negativeLevelEvent y (x + k)) :=
      ENNReal.tsum_le_tsum fun k => measure_mono (zeroPrefix_killed_subset x y k)
    _ ≤ ∑' n : ℕ, (offspringSeqLaw μ).toMeasure (negativeLevelEvent y n) :=
      ENNReal.tsum_comp_le_tsum_of_injective (f := fun k : ℕ => x + k)
        (fun _ _ h => Nat.add_left_cancel h)
        (fun n => (offspringSeqLaw μ).toMeasure (negativeLevelEvent y n))
    _ = 1 := tsum_negativeLevelEvent_mass μ hc hne y

/-- Every killed-gap Green entry is finite, with infinite offspring variance allowed. -/
theorem killedGapGreen_lt_top (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (x y : ℕ) : killedGapGreen μ x y < ∞ := by
  have h := killedGapGreen_weighted_le_one μ hc hne x y
  by_contra hnot
  have he : killedGapGreen μ x y = ∞ := top_unique (not_lt.mp hnot)
  have hpow : (μ 0) ^ x ≠ 0 := pow_ne_zero x (hc.apply_zero_ne_zero hne)
  simp [he, hpow] at h

end BGW.StableTrees.DiscreteHeightApprox
