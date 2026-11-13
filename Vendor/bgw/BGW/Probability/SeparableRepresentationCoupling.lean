/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Probability.ConditionalProbability
public import Mathlib.MeasureTheory.Constructions.UnitInterval
public import Mathlib.Probability.Kernel.IonescuTulcea.Traj
public import Mathlib.Probability.ProductMeasure

/-!
# Conditional couplings for the separable representation theorem

A countable measurable partition of `S` gives, for two probability measures `μ` and `ν`, a
conditional coupling driven by a shared uniform variable `u`. Given the current point `y`, in the
cell `A i`, the coupled point stays in the cell (drawn from `μ` conditioned on `A i`) when `u` is
below the stay probability of that cell, and is otherwise drawn from the residual law. The
probability of landing in different cells is bounded by the cell-mass defect `cellDefect`.
Iterating these kernels over a sequence of partitions gives a trajectory construction over the base
`S × unitInterval`, with the uniform variable shared across all times.

See Dudley, "Distances of probability measures and random variables" (1968), and *Real
Analysis and Probability* (2002), Theorem 11.7.2.
-/

@[expose] public section

open Filter MeasureTheory Set TopologicalSpace ProbabilityTheory Preorder
open scoped Topology ProbabilityTheory ENNReal Classical unitInterval

namespace BGW.Probability

/-- The index of the unique cell of a countable measurable partition containing a point. -/
noncomputable def partitionIndex {S : Type*} (A : ℕ → Set S)
    (hA : ⋃ i, A i = univ) (x : S) : ℕ :=
  Nat.find (mem_iUnion.mp (hA.symm ▸ mem_univ x))

/-- A point lies in the cell indexed by its `partitionIndex`. -/
lemma partitionIndex_mem {S : Type*} {A : ℕ → Set S} {hA : ⋃ i, A i = univ} (x : S) :
    x ∈ A (partitionIndex A hA x) := by
  unfold partitionIndex
  exact Nat.find_spec (mem_iUnion.mp (hA.symm ▸ mem_univ x))

private lemma partitionIndex_eq_iff_mem {S : Type*} {A : ℕ → Set S} {hA : ⋃ i, A i = univ}
    (hdisj : Pairwise (Function.onFun Disjoint A)) (x : S) (i : ℕ) :
    partitionIndex A hA x = i ↔ x ∈ A i := by
  constructor
  · rintro rfl
    exact partitionIndex_mem x
  · intro hi
    by_contra hne
    have hmem := partitionIndex_mem (A := A) (hA := hA) x
    exact (disjoint_left.mp (hdisj hne)) hmem hi

private lemma measurable_partitionIndex {S : Type*} [MeasurableSpace S] {A : ℕ → Set S}
    {hA : ⋃ i, A i = univ} (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) : Measurable (partitionIndex A hA) := by
  apply measurable_to_countable'
  intro i
  have heq : partitionIndex A hA ⁻¹' {i} = A i := by
    ext x
    simp only [mem_preimage, mem_singleton_iff, partitionIndex_eq_iff_mem hdisj]
  rw [heq]
  exact hmeas i

private noncomputable def commonMass {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) (A : ℕ → Set S) (i : ℕ) : ℝ≥0∞ := min (μ (A i)) (ν (A i))

private noncomputable def leftDefect {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) (A : ℕ → Set S) (i : ℕ) : ℝ≥0∞ :=
  μ (A i) - commonMass μ ν A i

private noncomputable def rightDefect {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) (A : ℕ → Set S) (i : ℕ) : ℝ≥0∞ :=
  ν (A i) - commonMass μ ν A i

private noncomputable def residualRaw {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) (A : ℕ → Set S) : Measure S :=
  Measure.sum fun i => leftDefect μ ν A i • μ[|A i]

/-- The one-sided cell-mass defect `cellDefect` used to control different-cell probability. -/
noncomputable def cellDefect {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) (A : ℕ → Set S) : ℝ≥0∞ :=
  ∑' i, (ν (A i) - min (μ (A i)) (ν (A i)))

private noncomputable def residualLaw {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) (A : ℕ → Set S) : Measure S :=
  if cellDefect μ ν A = 0 then μ else (cellDefect μ ν A)⁻¹ • residualRaw μ ν A

private lemma tsum_cell_mass {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {A : ℕ → Set S}
    (hmeas : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : ⋃ i, A i = univ) : ∑' i, μ (A i) = 1 := by
  rw [← measure_iUnion hdisj hmeas, hcover, measure_univ]

private lemma tsum_common_ne_top {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ]
    {A : ℕ → Set S} (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ) :
    ∑' i, commonMass μ ν A i ≠ ∞ := by
  have hμ : ∑' i, μ (A i) ≠ ∞ := by
    rw [tsum_cell_mass μ hmeas hdisj hcover]
    exact ENNReal.one_ne_top
  exact ne_top_of_le_ne_top hμ (ENNReal.tsum_le_tsum fun i => min_le_left _ _)

private lemma tsum_leftDefect {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ]
    {A : ℕ → Set S}
    (hmeas : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : ⋃ i, A i = univ) :
    ∑' i, leftDefect μ ν A i = 1 - ∑' i, commonMass μ ν A i := by
  simpa only [leftDefect, tsum_cell_mass μ hmeas hdisj hcover] using
    ENNReal.tsum_sub (f := fun i => μ (A i)) (g := fun i => commonMass μ ν A i)
      (tsum_common_ne_top μ ν hmeas hdisj hcover) (fun i => min_le_left _ _)

private lemma tsum_rightDefect {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : ℕ → Set S}
    (hmeas : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : ⋃ i, A i = univ) :
    ∑' i, rightDefect μ ν A i = 1 - ∑' i, commonMass μ ν A i := by
  simpa only [rightDefect, tsum_cell_mass ν hmeas hdisj hcover] using
    ENNReal.tsum_sub (f := fun i => ν (A i)) (g := fun i => commonMass μ ν A i)
      (tsum_common_ne_top μ ν hmeas hdisj hcover) (fun i => min_le_right _ _)

private lemma tsum_leftDefect_eq_defect {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : ℕ → Set S} (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ) :
    ∑' i, leftDefect μ ν A i = cellDefect μ ν A := by
  rw [tsum_leftDefect μ ν hmeas hdisj hcover]
  simpa only [cellDefect, rightDefect, commonMass] using
    (tsum_rightDefect μ ν hmeas hdisj hcover).symm

private lemma cellDefect_ne_top {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : ℕ → Set S}
    (hmeas : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : ⋃ i, A i = univ) : cellDefect μ ν A ≠ ∞ := by
  rw [show cellDefect μ ν A = 1 - ∑' i, commonMass μ ν A i from by
    simpa only [cellDefect, rightDefect, commonMass] using
      tsum_rightDefect μ ν hmeas hdisj hcover]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

private lemma cond_apply_univ {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (B : Set S) :
    μ[|B] univ = if μ B = 0 then 0 else 1 := by
  by_cases hB : μ B = 0
  · simp [hB, ProbabilityTheory.cond_eq_zero_of_meas_eq_zero]
  · let := ProbabilityTheory.cond_isProbabilityMeasure hB
    simp [hB]

private lemma mass_smul_cond {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (B : Set S) : μ B • μ[|B] = μ.restrict B := by
  by_cases hB : μ B = 0
  · rw [hB, zero_smul]
    exact (Measure.restrict_eq_zero.mpr hB).symm
  · rw [ProbabilityTheory.cond, smul_smul,
      ENNReal.mul_inv_cancel hB (measure_ne_top μ B), one_smul]

private lemma sum_mass_cond {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] {A : ℕ → Set S}
    (hmeas : ∀ i, MeasurableSet (A i)) (hdisj : Pairwise (Function.onFun Disjoint A))
    (hcover : ⋃ i, A i = univ) :
    (Measure.sum fun i => μ (A i) • μ[|A i]) = μ := by
  simp_rw [mass_smul_cond]
  rw [← Measure.restrict_iUnion hdisj hmeas, hcover, Measure.restrict_univ]

private lemma residualRaw_univ {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] (A : ℕ → Set S) :
    residualRaw μ ν A univ = ∑' i, leftDefect μ ν A i := by
  rw [residualRaw, Measure.sum_apply _ MeasurableSet.univ]
  apply tsum_congr
  intro i
  rw [Measure.smul_apply, smul_eq_mul, cond_apply_univ]
  by_cases hi : μ (A i) = 0
  · have hc : commonMass μ ν A i = 0 := by
      apply le_antisymm _ bot_le
      exact (min_le_left _ _).trans hi.le
    simp [hi, hc, leftDefect]
  · simp [hi]

private lemma residualLaw_isProbability {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : ℕ → Set S} (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ) :
    IsProbabilityMeasure (residualLaw μ ν A) := by
  constructor
  by_cases hD : cellDefect μ ν A = 0
  · simp [residualLaw, hD]
  · simp only [residualLaw, hD, ↓reduceIte]
    rw [Measure.smul_apply, smul_eq_mul, residualRaw_univ,
      tsum_leftDefect_eq_defect μ ν hmeas hdisj hcover]
    exact ENNReal.inv_mul_cancel hD (cellDefect_ne_top μ ν hmeas hdisj hcover)

private lemma defect_smul_residualLaw {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : ℕ → Set S} (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ) :
    cellDefect μ ν A • residualLaw μ ν A = residualRaw μ ν A := by
  by_cases hD : cellDefect μ ν A = 0
  · have hleft : ∑' i, leftDefect μ ν A i = 0 := by
      rw [tsum_leftDefect_eq_defect μ ν hmeas hdisj hcover, hD]
    have hi : ∀ i, leftDefect μ ν A i = 0 := ENNReal.tsum_eq_zero.mp hleft
    simp [residualLaw, residualRaw, hD, hi]
  · simp only [residualLaw, hD, ↓reduceIte]
    rw [smul_smul, ENNReal.mul_inv_cancel hD (cellDefect_ne_top μ ν hmeas hdisj hcover), one_smul]

private noncomputable def commonWeight {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) (A : ℕ → Set S) (i : ℕ) : ℝ≥0∞ :=
  commonMass μ ν A i * (ν (A i))⁻¹

private noncomputable def failureWeight {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) (A : ℕ → Set S) (i : ℕ) : ℝ≥0∞ :=
  if ν (A i) = 0 then 1 else rightDefect μ ν A i * (ν (A i))⁻¹

private lemma mul_commonWeight {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] (A : ℕ → Set S) (i : ℕ) :
    ν (A i) * commonWeight μ ν A i = commonMass μ ν A i := by
  by_cases hi : ν (A i) = 0
  · have hc : commonMass μ ν A i = 0 := by
      apply le_antisymm _ bot_le
      exact (min_le_right _ _).trans hi.le
    simp [hi, hc, commonWeight]
  · rw [commonWeight, mul_left_comm, ENNReal.mul_inv_cancel hi (measure_ne_top _ _), mul_one]

private lemma mul_failureWeight {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] (A : ℕ → Set S) (i : ℕ) :
    ν (A i) * failureWeight μ ν A i = rightDefect μ ν A i := by
  by_cases hi : ν (A i) = 0
  · have hc : commonMass μ ν A i = 0 := by
      apply le_antisymm _ bot_le
      exact (min_le_right _ _).trans hi.le
    simp [hi, hc, failureWeight, rightDefect]
  · simp only [failureWeight, hi, ↓reduceIte]
    rw [mul_left_comm, ENNReal.mul_inv_cancel hi (measure_ne_top _ _), mul_one]

private lemma commonWeight_add_failureWeight {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] (A : ℕ → Set S) (i : ℕ) :
    commonWeight μ ν A i + failureWeight μ ν A i = 1 := by
  by_cases hi : ν (A i) = 0
  · have hc : commonMass μ ν A i = 0 := by
      apply le_antisymm _ bot_le
      exact (min_le_right _ _).trans hi.le
    simp [hi, hc, commonWeight, failureWeight]
  · simp only [failureWeight, hi, ↓reduceIte]
    rw [commonWeight, rightDefect, commonMass, ← add_mul,
      add_tsub_cancel_of_le (min_le_right _ _), ENNReal.mul_inv_cancel hi (measure_ne_top _ _)]

private lemma cond_mismatch_null {S : Type*} [MeasurableSpace S]
    (μ : Measure S) {A : ℕ → Set S}
    (hmeas : ∀ i, MeasurableSet (A i)) {hdisj : Pairwise (Function.onFun Disjoint A)}
    {hcover : ⋃ i, A i = univ} (i : ℕ) :
    μ[|A i] {x | partitionIndex A hcover x ≠ i} = 0 := by
  apply ae_iff.mp
  filter_upwards [ae_cond_mem (hmeas i)] with x hx
  simpa only [mem_ofPred_eq, ne_eq, not_not] using
    (partitionIndex_eq_iff_mem hdisj x i).mpr hx

private noncomputable def augmentedOriginal {B S : Type*} (n : ℕ)
    (x : (i : Finset.Iic n) → B × S) : B := (x ⟨0, by simp⟩).1

private lemma measurable_augmentedOriginal {B S : Type*} [MeasurableSpace B]
    [MeasurableSpace S] (n : ℕ) :
    Measurable (augmentedOriginal (B := B) (S := S) n) :=
  measurable_fst.comp (measurable_pi_apply (⟨0, by simp⟩ : ↥(Finset.Iic n)))

private noncomputable def augmentedPair {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) (n : ℕ) : Kernel B (B × S) := Kernel.id ×ₖ K n

private instance augmentedPair_isMarkov {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    IsMarkovKernel (augmentedPair K n) := by
  rw [augmentedPair]
  infer_instance

private noncomputable def augmentedStep {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) (n : ℕ) : Kernel ((i : Finset.Iic n) → B × S) (B × S) :=
  (augmentedPair K (n + 1)).comap (augmentedOriginal n) (measurable_augmentedOriginal n)

private instance augmentedStep_isMarkov {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    IsMarkovKernel (augmentedStep K n) := by
  rw [augmentedStep]
  infer_instance

private noncomputable def augmentedInitial {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) : Kernel B ((i : Finset.Iic 0) → B × S) :=
  (augmentedPair K 0).map
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => B × S)).symm

private noncomputable def augmentedTrajectory {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] : Kernel B (ℕ → B × S) :=
  Kernel.traj (augmentedStep K) 0 ∘ₖ augmentedInitial K

private instance augmentedInitial_isMarkov {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] :
    IsMarkovKernel (augmentedInitial K) := by
  rw [augmentedInitial]
  exact Kernel.IsMarkovKernel.map _
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => B × S)).symm.measurable

private instance augmentedTrajectory_isMarkov {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] :
    IsMarkovKernel (augmentedTrajectory K) := by
  rw [augmentedTrajectory]
  infer_instance

private noncomputable def trajectoryKernel {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] : Kernel B (ℕ → S) :=
  (augmentedTrajectory K).map (fun z n => (z n).2)

private instance trajectoryKernel_isMarkov {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] :
    IsMarkovKernel (trajectoryKernel K) := by
  rw [trajectoryKernel]
  exact Kernel.IsMarkovKernel.map _ (by fun_prop)

private lemma comp_comap_augmentedInitial {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] (L : Kernel B S) :
    (L.comap (augmentedOriginal 0) (measurable_augmentedOriginal 0)) ∘ₖ
      augmentedInitial K = L := by
  rw [augmentedInitial, Kernel.comp_map _ _
    (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => B × S)).symm.measurable]
  rw [← Kernel.comap_comp_right]
  have he : augmentedOriginal 0 ∘
      (MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => B × S)).symm = Prod.fst := by
    funext x
    rfl
  simp only [he]
  rw [← Kernel.comp_map _ _ measurable_fst, augmentedPair, ← Kernel.fst_eq,
    Kernel.fst_prod, Kernel.comp_id]

private lemma partialTraj_map_original {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    (Kernel.partialTraj (X := fun _ : ℕ => B × S) (augmentedStep K) 0 n).map
      (augmentedOriginal n) =
      Kernel.deterministic (augmentedOriginal 0) (measurable_augmentedOriginal 0) := by
  have he : augmentedOriginal n = augmentedOriginal 0 ∘
      frestrictLe₂ (π := fun _ : ℕ => B × S) (Nat.zero_le n) := by
    funext x
    rfl
  rw [he, Kernel.map_comp_right _
    (measurable_frestrictLe₂ (X := fun _ : ℕ => B × S) (Nat.zero_le n))
    (measurable_augmentedOriginal 0), Kernel.partialTraj_map_frestrictLe₂,
    Kernel.partialTraj_self, Kernel.id_map]

private lemma augmentedTrajectory_map_zero {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] :
    (augmentedTrajectory K).map (fun z : ℕ → B × S => (z 0).2) = K 0 := by
  let e := MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 => B × S)
  have he : (fun z : ℕ → B × S => (z 0).2) =
      (Prod.snd ∘ e) ∘ (frestrictLe 0) := by
    funext z
    rfl
  rw [augmentedTrajectory, Kernel.map_comp, he]
  rw [Kernel.map_comp_right _ (measurable_frestrictLe 0)
    (measurable_snd.comp e.measurable), Kernel.traj_map_frestrictLe, Kernel.partialTraj_self]
  rw [Kernel.id_map (measurable_snd.comp e.measurable), augmentedInitial]
  rw [Kernel.deterministic_comp_eq_map (measurable_snd.comp e.measurable)]
  rw [← Kernel.map_comp_right _ e.symm.measurable (measurable_snd.comp e.measurable)]
  have hes : (Prod.snd ∘ e) ∘ e.symm = (Prod.snd : B × S → S) := by
    funext x
    simp
  rw [hes]
  rw [augmentedPair, ← Kernel.snd_eq, Kernel.snd_prod]

private lemma augmentedTrajectory_map_succ {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    (augmentedTrajectory K).map (fun z : ℕ → B × S => (z (n + 1)).2) = K (n + 1) := by
  let evalFin : ((i : Finset.Iic (n + 1)) → B × S) → B × S :=
    fun z => z ⟨n + 1, by simp⟩
  have he : (fun z : ℕ → B × S => (z (n + 1)).2) =
      (Prod.snd ∘ evalFin) ∘ frestrictLe (n + 1) := by
    funext z
    rfl
  have heval : Measurable evalFin := by
    exact measurable_pi_apply (⟨n + 1, by simp⟩ : ↥(Finset.Iic (n + 1)))
  rw [augmentedTrajectory, Kernel.map_comp, he]
  rw [Kernel.map_comp_right _ (measurable_frestrictLe (n + 1))
    (measurable_snd.comp heval), Kernel.traj_map_frestrictLe]
  have hp : (Kernel.partialTraj (X := fun _ : ℕ => B × S) (augmentedStep K) 0
      (n + 1)).map evalFin =
      (augmentedStep K n) ∘ₖ
        (Kernel.partialTraj (X := fun _ : ℕ => B × S) (augmentedStep K) 0 n) := by
    rw [← Kernel.partialTraj_comp_partialTraj (X := fun _ : ℕ => B × S)
      (κ := augmentedStep K)
      (Nat.zero_le n) (Nat.le_succ n), Kernel.map_comp]
    congr 1
    unfold evalFin
    exact Kernel.map_partialTraj_succ_self (X := fun _ : ℕ => B × S)
      (κ := augmentedStep K) n
  rw [Kernel.map_comp_right _ heval (measurable_snd : Measurable (Prod.snd : B × S → S)), hp]
  have hs : (augmentedStep K n).map Prod.snd =
      (K (n + 1)).comap (augmentedOriginal n) (measurable_augmentedOriginal n) := by
    rw [augmentedStep, ← Kernel.comap_map_comm _ (measurable_augmentedOriginal n)
      (measurable_snd : Measurable (Prod.snd : B × S → S)), augmentedPair, ← Kernel.snd_eq,
      Kernel.snd_prod]
  rw [Kernel.map_comp, hs, ← Kernel.comp_map, partialTraj_map_original,
    Kernel.comp_deterministic_eq_comap, comp_comap_augmentedInitial]

private lemma trajectoryKernel_map_eval_kernel {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    (trajectoryKernel K).map (fun z : ℕ → S => z n) = K n := by
  have hproj : Measurable (fun z : ℕ → B × S => fun n => (z n).2) := by fun_prop
  cases n with
  | zero =>
      rw [trajectoryKernel, ← Kernel.map_comp_right _ hproj (measurable_pi_apply 0)]
      exact augmentedTrajectory_map_zero K
  | succ n =>
      rw [trajectoryKernel, ← Kernel.map_comp_right _ hproj (measurable_pi_apply (n + 1))]
      exact augmentedTrajectory_map_succ K n

private noncomputable def trajectoryCoupling {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (ν : Measure B) (K : ℕ → Kernel B S) [∀ n, IsMarkovKernel (K n)] :
    Measure (B × (ℕ → S)) :=
  ν ⊗ₘ trajectoryKernel K

private instance trajectoryCoupling_isProbability {B S : Type*} [MeasurableSpace B]
    [MeasurableSpace S]
    (ν : Measure B) [IsProbabilityMeasure ν] (K : ℕ → Kernel B S)
    [∀ n, IsMarkovKernel (K n)] : IsProbabilityMeasure (trajectoryCoupling ν K) := by
  rw [trajectoryCoupling]
  infer_instance

private lemma trajectoryCoupling_map_pair {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (ν : Measure B) [IsProbabilityMeasure ν] (K : ℕ → Kernel B S)
    [∀ n, IsMarkovKernel (K n)] (n : ℕ) :
    Measure.map (fun z : B × (ℕ → S) => (z.1, z.2 n)) (trajectoryCoupling ν K) =
      ν ⊗ₘ (K n) := by
  have hfun : (fun z : B × (ℕ → S) => (z.1, z.2 n)) =
      Prod.map id (fun z : ℕ → S => z n) := rfl
  rw [hfun, trajectoryCoupling, ← Measure.compProd_map (μ := ν) (κ := trajectoryKernel K)
    (f := fun z : ℕ → S => z n) (measurable_pi_apply n)]
  have hEval : (trajectoryKernel K).map (fun z : ℕ → S => z n) = K n :=
    trajectoryKernel_map_eval_kernel K n
  rw [hEval]

private lemma trajectoryCoupling_map_fst {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (ν : Measure B) [IsProbabilityMeasure ν] (K : ℕ → Kernel B S)
    [∀ n, IsMarkovKernel (K n)] :
    Measure.map Prod.fst (trajectoryCoupling ν K) = ν := by
  exact Measure.fst_compProd ν (trajectoryKernel K)

private lemma trajectoryCoupling_map_eval {B S : Type*} [MeasurableSpace B] [MeasurableSpace S]
    (ν : Measure B) [IsProbabilityMeasure ν] (K : ℕ → Kernel B S)
    [∀ n, IsMarkovKernel (K n)] {μ : ℕ → Measure S}
    (hlaw : ∀ n, (K n ∘ₘ ν) = μ n) (n : ℕ) :
    Measure.map (fun z : B × (ℕ → S) => z.2 n) (trajectoryCoupling ν K) = μ n := by
  calc
    Measure.map (fun z : B × (ℕ → S) => z.2 n) (trajectoryCoupling ν K) =
        Measure.map Prod.snd (ν ⊗ₘ K n) := by
      rw [← trajectoryCoupling_map_pair ν K n, Measure.map_map measurable_snd (by fun_prop)]
      rfl
    _ = K n ∘ₘ ν := Measure.snd_compProd ν (K n)
    _ = μ n := hlaw n

private lemma commonWeight_le_one {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] (A : ℕ → Set S) (i : ℕ) :
    commonWeight μ ν A i ≤ 1 := by
  rw [← commonWeight_add_failureWeight μ ν A i]
  exact le_add_right le_rfl

private lemma commonWeight_ne_top' {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] (A : ℕ → Set S) (i : ℕ) :
    commonWeight μ ν A i ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (commonWeight_le_one μ ν A i)

/-- The probability of using the conditional law on a cell, represented in the unit interval. -/
noncomputable def cellStayProbability {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] (A : ℕ → Set S) (i : ℕ) : I :=
  ⟨(min (μ (A i)) (ν (A i)) * (ν (A i))⁻¹).toReal, ENNReal.toReal_nonneg,
    (ENNReal.toReal_le_toReal (by
      apply ne_top_of_le_ne_top ENNReal.one_ne_top
      by_cases hi : ν (A i) = 0
      · simp [hi]
      · calc
          min (μ (A i)) (ν (A i)) * (ν (A i))⁻¹ ≤ ν (A i) * (ν (A i))⁻¹ :=
            (by gcongr; exact min_le_right _ _)
          _ = 1 := ENNReal.mul_inv_cancel hi (measure_ne_top _ _)) ENNReal.one_ne_top).mpr (by
      by_cases hi : ν (A i) = 0
      · simp [hi]
      · calc
          min (μ (A i)) (ν (A i)) * (ν (A i))⁻¹ ≤ ν (A i) * (ν (A i))⁻¹ :=
            (by gcongr; exact min_le_right _ _)
          _ = 1 := ENNReal.mul_inv_cancel hi (measure_ne_top _ _))⟩

private noncomputable def uniformBranch {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] (A : ℕ → Set S) (i : ℕ) (u : I) :
    Measure S :=
  if u < cellStayProbability μ ν A i then μ[|A i] else residualLaw μ ν A

private noncomputable def uniformCouplingKernel {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] (A : ℕ → Set S)
    (hmeas : ∀ i, MeasurableSet (A i)) : Kernel (S × I) S where
  toFun z := Measure.sum fun i => if z.1 ∈ A i then uniformBranch μ ν A i z.2 else 0
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro B hB
    simp only [Measure.sum_apply _ hB]
    apply Measurable.tsum
    intro i
    have heq : (fun z : S × I => (if z.1 ∈ A i then uniformBranch μ ν A i z.2 else 0) B) =
        (fun z => if z.1 ∈ A i then uniformBranch μ ν A i z.2 B else 0) := by
      funext z
      by_cases hz : z.1 ∈ A i <;> simp [hz]
    rw [heq]
    apply Measurable.ite (measurable_fst (hmeas i))
    · have heq' : (fun z : S × I => uniformBranch μ ν A i z.2 B) = (fun z =>
          if z.2 < cellStayProbability μ ν A i then μ[|A i] B else residualLaw μ ν A B) := by
        funext z
        by_cases hz : z.2 < cellStayProbability μ ν A i <;> simp [uniformBranch, hz]
      rw [heq']
      exact Measurable.ite (measurableSet_lt
        (measurable_snd : Measurable (Prod.snd : S × I → I)) measurable_const)
        measurable_const measurable_const
    · exact measurable_const

private lemma uniformCouplingKernel_apply_of_mem {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] {A : ℕ → Set S}
    (hmeas : ∀ i, MeasurableSet (A i))
    {hdisj : Pairwise (Function.onFun Disjoint A)} {_hcover : ⋃ i, A i = univ}
    {y : S} {i : ℕ} (hy : y ∈ A i) (u : I) :
    uniformCouplingKernel μ ν A hmeas (y, u) = uniformBranch μ ν A i u := by
  change (Measure.sum fun j => if y ∈ A j then uniformBranch μ ν A j u else 0) = _
  ext B hB
  simp only [Measure.sum_apply _ hB]
  rw [tsum_eq_single i]
  · simp [hy]
  · intro j hji
    have hyj : y ∉ A j := fun hyj => (disjoint_left.mp (hdisj hji)) hyj hy
    simp [hyj]

private lemma uniformCouplingKernel_isMarkov {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : ℕ → Set S} (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ) :
    IsMarkovKernel (uniformCouplingKernel μ ν A hmeas) := by
  constructor
  intro z
  obtain ⟨i, hi⟩ : ∃ i, z.1 ∈ A i := by
    have : z.1 ∈ ⋃ i, A i := hcover.symm ▸ mem_univ z.1
    exact mem_iUnion.mp this
  rw [uniformCouplingKernel_apply_of_mem μ ν hmeas (hdisj := hdisj) (_hcover := hcover) hi]
  by_cases hμ : μ (A i) = 0
  · have hw : cellStayProbability μ ν A i = 0 := by
      apply Subtype.ext
      simp [cellStayProbability, hμ]
    rw [uniformBranch, hw]
    simp only [not_lt_zero, ↓reduceIte]
    exact residualLaw_isProbability μ ν hmeas hdisj hcover
  · by_cases hu : z.2 < cellStayProbability μ ν A i
    · rw [uniformBranch]
      simp only [hu, ↓reduceIte]
      exact ProbabilityTheory.cond_isProbabilityMeasure hμ
    · rw [uniformBranch]
      simp only [hu, ↓reduceIte]
      exact residualLaw_isProbability μ ν hmeas hdisj hcover

private lemma volume_stayProbability {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] (A : ℕ → Set S) (i : ℕ) :
    volume (Iio (cellStayProbability μ ν A i)) = commonWeight μ ν A i := by
  rw [unitInterval.volume_Iio]
  change ENNReal.ofReal (commonWeight μ ν A i).toReal = commonWeight μ ν A i
  exact ENNReal.ofReal_toReal (commonWeight_ne_top' μ ν A i)

private lemma volume_leaveProbability {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν] (A : ℕ → Set S) (i : ℕ) :
    volume (Ici (cellStayProbability μ ν A i)) = failureWeight μ ν A i := by
  have hf : failureWeight μ ν A i = 1 - commonWeight μ ν A i :=
    (ENNReal.eq_sub_of_add_eq (commonWeight_ne_top' μ ν A i)
      (by simpa only [add_comm] using commonWeight_add_failureWeight μ ν A i))
  rw [hf, unitInterval.volume_Ici]
  change ENNReal.ofReal (1 - (commonWeight μ ν A i).toReal) = 1 - commonWeight μ ν A i
  rw [← ENNReal.toReal_one, ← ENNReal.toReal_sub_of_le (commonWeight_le_one μ ν A i)
    ENNReal.one_ne_top, ENNReal.ofReal_toReal]
  exact ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self

private lemma lintegral_uniformBranch {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure ν]
    {A : ℕ → Set S} (_hmeas : ∀ i, MeasurableSet (A i))
    (_hdisj : Pairwise (Function.onFun Disjoint A)) (_hcover : ⋃ i, A i = univ)
    (i : ℕ) (B : Set S) :
    ∫⁻ u, uniformBranch μ ν A i u B = commonWeight μ ν A i * μ[|A i] B +
      failureWeight μ ν A i * residualLaw μ ν A B := by
  have heq : (fun u => uniformBranch μ ν A i u B) = fun u =>
      (Iio (cellStayProbability μ ν A i)).indicator (fun _ => μ[|A i] B) u +
      (Ici (cellStayProbability μ ν A i)).indicator (fun _ => residualLaw μ ν A B) u := by
    funext u
    by_cases hu : u < cellStayProbability μ ν A i
    · simp [uniformBranch, hu]
    · have hu' : cellStayProbability μ ν A i ≤ u := le_of_not_gt hu
      simp [uniformBranch, hu, hu']
  rw [heq, lintegral_add_left]
  · rw [lintegral_indicator measurableSet_Iio, lintegral_indicator measurableSet_Ici,
      setLIntegral_const, setLIntegral_const, volume_stayProbability, volume_leaveProbability]
    rw [mul_comm (μ[|A i] B) (commonWeight μ ν A i),
      mul_comm ((residualLaw μ ν A) B) (failureWeight μ ν A i)]
  · exact Measurable.indicator measurable_const measurableSet_Iio

private lemma bind_uniformCouplingKernel {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : ℕ → Set S} (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ) :
    uniformCouplingKernel μ ν A hmeas ∘ₘ ν.prod volume = μ := by
  ext B hB
  have hdecomp : ν = Measure.sum fun i => ν.restrict (A i) := by
    rw [← Measure.restrict_iUnion hdisj hmeas, hcover, Measure.restrict_univ]
  rw [Measure.bind_apply hB (Kernel.aemeasurable _), lintegral_prod _
    (Kernel.measurable_coe _ hB).aemeasurable]
  nth_rewrite 1 [hdecomp]
  rw [lintegral_sum_measure]
  have hterm (i : ℕ) :
      ∫⁻ y, (∫⁻ u : I, uniformCouplingKernel μ ν A hmeas (y, u) B) ∂ν.restrict (A i) =
        commonMass μ ν A i * μ[|A i] B + rightDefect μ ν A i * residualLaw μ ν A B := by
    calc
      _ = ∫⁻ _y, commonWeight μ ν A i * μ[|A i] B +
          failureWeight μ ν A i * residualLaw μ ν A B ∂ν.restrict (A i) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem (hmeas i)] with y hy
        simp_rw [uniformCouplingKernel_apply_of_mem μ ν hmeas
          (hdisj := hdisj) (_hcover := hcover) hy]
        exact lintegral_uniformBranch μ ν hmeas hdisj hcover i B
      _ = (commonWeight μ ν A i * μ[|A i] B +
          failureWeight μ ν A i * residualLaw μ ν A B) * ν (A i) := by
        rw [setLIntegral_const]
      _ = _ := by
        rw [add_mul, mul_comm (commonWeight μ ν A i * μ[|A i] B),
          mul_comm (failureWeight μ ν A i * residualLaw μ ν A B), ← mul_assoc, ← mul_assoc,
          mul_commonWeight, mul_failureWeight]
  rw [tsum_congr hterm, ENNReal.tsum_add]
  calc
    _ = (∑' i, commonMass μ ν A i * μ[|A i] B) +
        cellDefect μ ν A * residualLaw μ ν A B := by rw [ENNReal.tsum_mul_right]; rfl
    _ = (∑' i, commonMass μ ν A i * μ[|A i] B) + residualRaw μ ν A B := by
      have hD := congrArg (fun ρ : Measure S => ρ B)
        (defect_smul_residualLaw μ ν hmeas hdisj hcover)
      simp only [Measure.smul_apply, smul_eq_mul] at hD
      rw [hD]
    _ = ∑' i, (commonMass μ ν A i * μ[|A i] B +
        leftDefect μ ν A i * μ[|A i] B) := by
      simp only [residualRaw, Measure.sum_apply _ hB, Measure.smul_apply, smul_eq_mul,
        ENNReal.tsum_add]
    _ = ∑' i, μ (A i) * μ[|A i] B := by
      apply tsum_congr
      intro i
      rw [← add_mul, commonMass, leftDefect, commonMass,
        add_tsub_cancel_of_le (min_le_left _ _)]
    _ = μ B := by
      have h := congrArg (fun ρ : Measure S => ρ B) (sum_mass_cond μ hmeas hdisj hcover)
      simpa only [Measure.sum_apply _ hB, Measure.smul_apply, smul_eq_mul] using h

private lemma compProd_uniform_mismatch_null {S : Type*} [MeasurableSpace S]
    (μ ν : Measure S) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {A : ℕ → Set S} (hmeas : ∀ i, MeasurableSet (A i))
    (hdisj : Pairwise (Function.onFun Disjoint A)) (hcover : ⋃ i, A i = univ) (i : ℕ) :
    ((ν.prod volume) ⊗ₘ uniformCouplingKernel μ ν A hmeas)
      {z | z.1.1 ∈ A i ∧ z.1.2 < cellStayProbability μ ν A i ∧
        partitionIndex A hcover z.1.1 ≠ partitionIndex A hcover z.2} = 0 := by
  have hidx : Measurable (partitionIndex A hcover) := measurable_partitionIndex hmeas hdisj
  have hE : MeasurableSet {z : (S × I) × S | z.1.1 ∈ A i ∧
      z.1.2 < cellStayProbability μ ν A i ∧
      partitionIndex A hcover z.1.1 ≠ partitionIndex A hcover z.2} := by
    apply MeasurableSet.inter
    · exact (hmeas i).preimage measurable_fst.fst
    · exact (measurableSet_lt
        (measurable_snd.comp measurable_fst :
          Measurable (fun z : (S × I) × S => z.1.2)) measurable_const).inter
        ((measurableSet_eq_fun (hidx.comp measurable_fst.fst)
          (hidx.comp measurable_snd)).compl)
  let _ := uniformCouplingKernel_isMarkov μ ν hmeas hdisj hcover
  rw [Measure.compProd_apply hE]
  rw [lintegral_prod _ (Kernel.measurable_kernel_prodMk_left hE).aemeasurable]
  have hpoint (y : S) (u : I) : uniformCouplingKernel μ ν A hmeas (y, u)
      (Prod.mk (y, u) ⁻¹' {z : (S × I) × S | z.1.1 ∈ A i ∧
        z.1.2 < cellStayProbability μ ν A i ∧
        partitionIndex A hcover z.1.1 ≠ partitionIndex A hcover z.2}) = 0 := by
    by_cases hy : y ∈ A i
    · by_cases hu : u < cellStayProbability μ ν A i
      · have hiy : partitionIndex A hcover y = i :=
          (partitionIndex_eq_iff_mem hdisj y i).mpr hy
        have hset : Prod.mk (y, u) ⁻¹' {z : (S × I) × S | z.1.1 ∈ A i ∧
            z.1.2 < cellStayProbability μ ν A i ∧
            partitionIndex A hcover z.1.1 ≠ partitionIndex A hcover z.2} =
            {x | partitionIndex A hcover x ≠ i} := by
          ext x
          simp [hy, hu, hiy, ne_comm]
        rw [hset, uniformCouplingKernel_apply_of_mem μ ν hmeas
          (hdisj := hdisj) (_hcover := hcover) hy]
        simp [uniformBranch, hu, cond_mismatch_null μ hmeas (hdisj := hdisj) i]
      · have hset : Prod.mk (y, u) ⁻¹' {z : (S × I) × S | z.1.1 ∈ A i ∧
            z.1.2 < cellStayProbability μ ν A i ∧
            partitionIndex A hcover z.1.1 ≠ partitionIndex A hcover z.2} = ∅ := by
          ext x
          simp [hy, hu]
        rw [hset]
        exact measure_empty
    · have hset : Prod.mk (y, u) ⁻¹' {z : (S × I) × S | z.1.1 ∈ A i ∧
          z.1.2 < cellStayProbability μ ν A i ∧
          partitionIndex A hcover z.1.1 ≠ partitionIndex A hcover z.2} = ∅ := by
        ext x
        simp [hy]
      rw [hset]
      exact measure_empty
  simp_rw [hpoint]
  simp

/-- Couplings driven by one uniform variable on every cell. In addition to exact marginals, the
common-branch mismatch events are null, which lets a later diagonal argument share the uniform
variable across all times. -/
theorem exists_uniform_coupling_of_partitions {S : Type*} [MeasurableSpace S]
    (μ : ℕ → Measure S) (ν : Measure S) [∀ n, IsProbabilityMeasure (μ n)]
    [IsProbabilityMeasure ν] (A : ℕ → ℕ → Set S) (hmeas : ∀ n i, MeasurableSet (A n i))
    (hdisj : ∀ n, Pairwise (Function.onFun Disjoint (A n)))
    (hcover : ∀ n, ⋃ i, A n i = univ) :
    ∃ ρ : Measure ((S × I) × (ℕ → S)), IsProbabilityMeasure ρ ∧
      (∀ n, Measure.map (fun z : (S × I) × (ℕ → S) => z.2 n) ρ = μ n) ∧
      Measure.map Prod.fst ρ = ν.prod volume ∧ ∀ n i,
      ρ {z | z.1.1 ∈ A n i ∧ z.1.2 < cellStayProbability (μ n) ν (A n) i ∧
        partitionIndex (A n) (hcover n) z.1.1 ≠
          partitionIndex (A n) (hcover n) (z.2 n)} = 0 := by
  let K : ℕ → Kernel (S × I) S := fun n => uniformCouplingKernel (μ n) ν (A n) (hmeas n)
  let (n : ℕ) : IsMarkovKernel (K n) :=
    uniformCouplingKernel_isMarkov (μ n) ν (hmeas n) (hdisj n) (hcover n)
  refine ⟨trajectoryCoupling (ν.prod volume) K, inferInstance,
    trajectoryCoupling_map_eval (ν.prod volume) K
      (fun n => bind_uniformCouplingKernel (μ n) ν (hmeas n) (hdisj n) (hcover n)),
    trajectoryCoupling_map_fst (ν.prod volume) K, ?_⟩
  intro n i
  let T : (S × I) × (ℕ → S) → (S × I) × S := fun z => (z.1, z.2 n)
  let E : Set ((S × I) × S) := {z | z.1.1 ∈ A n i ∧
    z.1.2 < cellStayProbability (μ n) ν (A n) i ∧
    partitionIndex (A n) (hcover n) z.1.1 ≠ partitionIndex (A n) (hcover n) z.2}
  have hidx : Measurable (partitionIndex (A n) (hcover n)) :=
    measurable_partitionIndex (hmeas n) (hdisj n)
  have hT : Measurable T := by fun_prop
  have hE : MeasurableSet E := by
    apply MeasurableSet.inter
    · exact (hmeas n i).preimage measurable_fst.fst
    · exact (measurableSet_lt (measurable_snd.comp measurable_fst :
        Measurable (fun z : (S × I) × S => z.1.2)) measurable_const).inter
        ((measurableSet_eq_fun (hidx.comp measurable_fst.fst)
          (hidx.comp measurable_snd)).compl)
  rw [show {z : (S × I) × (ℕ → S) | z.1.1 ∈ A n i ∧
      z.1.2 < cellStayProbability (μ n) ν (A n) i ∧
      partitionIndex (A n) (hcover n) z.1.1 ≠
        partitionIndex (A n) (hcover n) (z.2 n)} = T ⁻¹' E from rfl]
  rw [← Measure.map_apply hT hE, trajectoryCoupling_map_pair (ν.prod volume) K n]
  exact compProd_uniform_mismatch_null (μ n) ν (hmeas n) (hdisj n) (hcover n) i

end BGW.Probability
