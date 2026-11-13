/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContourMirror
public import BGW.StableTrees.TailPair
public import BGW.StableTrees.DiscreteForest
public import BGW.ContinuumTrees.ContourAdapters

/-!
# Contour paths and mirror symmetry on the locally finite carrier

Finite trees carry their interpolated contour, and infinite trees carry the zero path.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

private theorem interpolation_cell (a : ℕ → ℝ) (n : ℕ) {t : ℝ}
    (ht : t ∈ Icc (n : ℝ) (n + 1)) :
    (fun t : ℝ => (1 - (t - ⌊t⌋₊)) * a ⌊t⌋₊ + (t - ⌊t⌋₊) * a (⌊t⌋₊ + 1)) t =
      (1 - (t - n)) * (a n) + (t - n) * (a (n + 1)) := by
  by_cases he : t = n + 1
  · subst t
    have hf : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by
      rw [← Nat.cast_add_one, Nat.floor_natCast]
    simp [hf]
  · have hf : ⌊t⌋₊ = n := (Nat.floor_eq_iff (le_trans (Nat.cast_nonneg n) ht.1)).2
      ⟨ht.1, lt_of_le_of_ne ht.2 he⟩
    simp only [hf]

private theorem continuousOn_interpolation_cell (a : ℕ → ℝ) (n : ℕ) :
    ContinuousOn (fun t : ℝ =>
      (1 - (t - ⌊t⌋₊)) * a ⌊t⌋₊ + (t - ⌊t⌋₊) * a (⌊t⌋₊ + 1))
      (Icc (n : ℝ) (n + 1)) := by
  apply ContinuousOn.congr (f := fun t : ℝ =>
    (1 - (t - n)) * (a n) + (t - n) * (a (n + 1)))
      (by fun_prop)
  intro t ht
  exact interpolation_cell a n ht

private theorem continuousOn_interpolation_Iic (a : ℕ → ℝ) (n : ℕ) :
    ContinuousOn (fun t : ℝ =>
      (1 - (t - ⌊t⌋₊)) * a ⌊t⌋₊ + (t - ⌊t⌋₊) * a (⌊t⌋₊ + 1)) (Iic (n : ℝ)) := by
  induction n with
  | zero =>
    apply ContinuousOn.congr (f := fun t : ℝ =>
      (1 - t) * (a 0) + t * (a 1)) (by fun_prop)
    intro t ht
    have ht0 : t ≤ 0 := by simpa using ht
    have hf : ⌊t⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    simp [hf]
  | succ n ih =>
    have hu : Iic (n : ℝ) ∪ Icc (n : ℝ) (n + 1) = Iic ((n + 1 : ℕ) : ℝ) := by
      ext t
      simp only [mem_union, mem_Iic, mem_Icc, Nat.cast_add, Nat.cast_one]
      constructor
      · rintro (h | h) <;> linarith [h]
      · intro h
        rcases le_total t (n : ℝ) with hn | hn
        · exact Or.inl hn
        · exact Or.inr ⟨hn, h⟩
    rw [← hu]
    exact ih.union_of_isClosed (continuousOn_interpolation_cell a n) isClosed_Iic isClosed_Icc

/-- The interpolated height is continuous. -/
private theorem continuous_interpolation (a : ℕ → ℝ) :
    Continuous (fun t : ℝ =>
      (1 - (t - ⌊t⌋₊)) * a ⌊t⌋₊ + (t - ⌊t⌋₊) * a (⌊t⌋₊ + 1)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have ht : t < ((⌊t⌋₊ + 1 : ℕ) : ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one t
  exact (continuousOn_interpolation_Iic a (⌊t⌋₊ + 1)).continuousAt (Iic_mem_nhds ht)


/-- The finite-tree contour interpolation is continuous on the real line. -/
theorem continuous_contourLin (t : PlaneTree) : Continuous t.contourLin :=
  continuous_interpolation (fun i => (t.contourAt i : ℝ))

/-- The locally finite carrier has only countably many finite trees. -/
theorem countable_finiteVertices :
    Set.Countable {τ : BGW.LocallyFinite.Tree | BGW.LocallyFinite.FiniteVertices τ} := by
  rw [← BGW.LocallyFinite.range_toLocallyFinite]
  exact Set.countable_range _

/-- Mirror on the locally finite carrier: the mirror of the decoded finite tree, and the
identity on infinite trees. -/
noncomputable def treeMirror (τ : BGW.LocallyFinite.Tree) : BGW.LocallyFinite.Tree :=
  if h : BGW.LocallyFinite.FiniteVertices τ then
    (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).mirror.toLocallyFinite
  else τ

/-- Mirroring on the locally finite carrier is measurable. -/
theorem measurable_treeMirror : Measurable treeMirror := by
  apply measurable_of_measurable_on_compl_countable _ countable_finiteVertices
  change Measurable (fun τ : {τ : BGW.LocallyFinite.Tree |
    ¬ BGW.LocallyFinite.FiniteVertices τ} => treeMirror τ)
  have he : (fun τ : {τ : BGW.LocallyFinite.Tree |
      ¬ BGW.LocallyFinite.FiniteVertices τ} => treeMirror τ) = Subtype.val := by
    funext τ
    exact dite_eq_right τ.property
  rw [he]
  exact measurable_subtype_coe

/-- Mirroring a finite tree commutes with its encoding. -/
theorem treeMirror_toLocallyFinite (t : PlaneTree) :
    treeMirror t.toLocallyFinite = t.mirror.toLocallyFinite := by
  rw [treeMirror, dite_eq_left t.finiteVertices_toLocallyFinite]
  change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices
    t)).mirror.toLocallyFinite = _
  rw [Equiv.symm_apply_apply]

/-- Mirroring on the locally finite carrier is an involution. -/
theorem treeMirror_treeMirror (τ : BGW.LocallyFinite.Tree) : treeMirror (treeMirror τ) = τ := by
  by_cases hτ : BGW.LocallyFinite.FiniteVertices τ
  · obtain ⟨t, rfl⟩ := (BGW.LocallyFinite.exists_toLocallyFinite_iff τ).mpr hτ
    rw [treeMirror_toLocallyFinite, treeMirror_toLocallyFinite, PlaneTree.mirror_mirror]
  · simp only [treeMirror, dite_eq_right hτ]



private theorem size_mass (μ : PMF ℕ) (n : ℕ) {A : Set BGW.LocallyFinite.Tree}
    (hA : MeasurableSet A) :
    BGW.LocallyFinite.bienaymeLaw μ.toMeasure (A ∩ BGW.LocallyFinite.sizeEvent n) =
      ∑' t : PlaneTree, if t.size = n ∧ t.toLocallyFinite ∈ A then
        PlaneTree.weight (fun d => μ.toMeasure {d}) t else 0 := by
  have hfin : A ∩ BGW.LocallyFinite.sizeEvent n ⊆
      {τ | BGW.LocallyFinite.FiniteVertices τ} := fun _ h => h.2.1
  rw [← Set.inter_eq_left.mpr hfin,
    ← Measure.restrict_apply (hA.inter (BGW.LocallyFinite.measurableSet_sizeEvent n)),
    BGW.LocallyFinite.bienaymeLaw_restrict_finiteVertices,
    Measure.sum_apply _ (hA.inter (BGW.LocallyFinite.measurableSet_sizeEvent n))]
  apply tsum_congr
  intro t
  rw [Measure.smul_apply, Measure.dirac_apply' _
    (hA.inter (BGW.LocallyFinite.measurableSet_sizeEvent n)), smul_eq_mul]
  by_cases ht : t.size = n <;> by_cases ha : t.toLocallyFinite ∈ A <;>
    simp [BGW.LocallyFinite.toLocallyFinite_mem_sizeEvent_iff, ht, ha]

private theorem exactTreeLaw_toMeasure_of_not_admissible (μ : PMF ℕ) (n : ℕ)
    (hn : ¬Admissible μ n) :
    (exactTreeLaw μ n : Measure BGW.LocallyFinite.Tree) =
      Measure.dirac BGW.LocallyFinite.leaf := by
  unfold exactTreeLaw ProbabilityMeasure.toMeasure ProbabilityMeasure
  rw [dite_eq_right hn]

/-- **Mirror invariance** of the exact-size conditioned law, for every `n` (size and weight are
preserved; the Dirac leaf of the junk branch is mirror invariant). -/
theorem map_treeMirror_exactTreeLaw (μ : PMF ℕ) (n : ℕ) :
    (exactTreeLaw μ n).map treeMirror = exactTreeLaw μ n := by
  apply Subtype.ext
  by_cases hn : Admissible μ n
  · change (exactTreeLaw μ n).toMeasure.map treeMirror = _
    change (exactTreeLaw μ n).toMeasure.map treeMirror = (exactTreeLaw μ n).toMeasure
    rw [exactTreeLaw_toMeasure μ n hn]
    ext A hA
    rw [Measure.map_apply measurable_treeMirror hA,
      cond_apply (BGW.LocallyFinite.measurableSet_sizeEvent n),
      cond_apply (BGW.LocallyFinite.measurableSet_sizeEvent n)]
    congr 1
    rw [Set.inter_comm, size_mass μ n (measurable_treeMirror hA), Set.inter_comm,
      size_mass μ n hA]
    let e : PlaneTree ≃ PlaneTree :=
      ⟨PlaneTree.mirror, PlaneTree.mirror, PlaneTree.mirror_mirror, PlaneTree.mirror_mirror⟩
    rw [← e.tsum_eq]
    apply tsum_congr
    intro t
    simp only [e, Equiv.coe_fn_mk, PlaneTree.size_mirror, PlaneTree.weight_mirror,
      Set.mem_preimage, treeMirror_toLocallyFinite, PlaneTree.mirror_mirror]
  · change Measure.map treeMirror (exactTreeLaw μ n).toMeasure =
      (exactTreeLaw μ n).toMeasure
    rw [exactTreeLaw_toMeasure_of_not_admissible μ n hn]
    rw [Measure.map_dirac]
    congr 1
    rw [← PlaneTree.toLocallyFinite_leaf, treeMirror_toLocallyFinite]
    rfl


end BGW.StableTrees.ExactContour
