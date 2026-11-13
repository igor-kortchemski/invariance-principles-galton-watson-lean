/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExactContourBasic
public import BGW.StableTrees.ExactContourClock
public import BGW.StableTrees.ExactContourPrefix

/-!
# Exact-size height and contour laws

The paper clock uses twice the number of vertices. The library clock uses twice the
number of edges. In both laws the height and contour come from the same tree.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical

namespace BGW.StableTrees.ExactContour

open BGW.StableTrees.DiscreteForest BGW.StableTrees.TailPair

/-- The interpolated contour (original speed, `0` after time `2(z-1)`) of the decoded finite
tree; `0` for an infinite tree. -/
noncomputable def treeContourLin (τ : BGW.LocallyFinite.Tree) (s : ℝ) : ℝ :=
  if h : BGW.LocallyFinite.FiniteVertices τ then
    (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).contourLin s
  else 0

/-- The interpolated tree contour is continuous (the junk branch of `treeContourPath` never
occurs). -/
theorem continuous_treeContourLin (τ : BGW.LocallyFinite.Tree) :
    Continuous (treeContourLin τ) := by
  change Continuous (fun s => treeContourLin τ s)
  by_cases hτ : BGW.LocallyFinite.FiniteVertices τ
  · simpa only [treeContourLin, dite_eq_left hτ] using
      continuous_contourLin (PlaneTree.equivFiniteVertices.symm ⟨τ, hτ⟩)
  · simpa only [treeContourLin, dite_eq_right hτ] using
      (continuous_const : Continuous (fun _ : ℝ => (0 : ℝ)))

/-- **Tree contour path** on `[0,T]`: `t ↦ (B n / n) * treeContourLin τ (2 n t)`; junk `0` if the
interpolation were discontinuous (never, `continuous_treeContourLin`). -/
noncomputable def treeContourPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    (τ : BGW.LocallyFinite.Tree) : C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) :=
  if h : Continuous (treeContourLin τ) then
    ⟨fun t => B n / n * treeContourLin τ (2 * (n : ℝ) * (t : ℝ)),
      continuous_const.mul (h.comp (continuous_const.mul continuous_subtype_val))⟩
  else 0

/-- The (height, contour) pair path on `[0,1]` at time scales `nt` and `2nt`, amplitude
`B n / n` for both. -/
noncomputable def heightContourPath (B : ℕ → ℝ) (n : ℕ) (τ : BGW.LocallyFinite.Tree) :
    C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ) :=
  (treeHeightPath B n 1 τ, treeContourPath B n 1 τ)

/-- **The exact-size height/contour law** on `[0,1]`: height and contour of ONE BGW tree
conditioned on size exactly `n` (sealed K02 `exactTreeLaw`, totalized). -/
noncomputable def exactHeightContourLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (_hn : Admissible μ n) :
    ProbabilityMeasure (C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
  (exactTreeLaw μ n).map (heightContourPath B n)

/-- The uniform distance on `[0,a]` between the normalized contour at time `2nt` and the
normalized interpolated height at time `nt`, for one tree. -/
noncomputable def contourHeightError (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0)
    (τ : BGW.LocallyFinite.Tree) : ℝ :=
  ⨆ t : Set.Icc (0 : ℝ) (a : ℝ),
    |B n / n * treeContourLin τ (2 * (n : ℝ) * (t : ℝ)) -
      B n / n * treeHeightLin τ ((n : ℝ) * (t : ℝ))|

/-- The (height, contour) pair in the library contour convention (`s ↦ C(2(z-1)s)`, sealed
`PlaneTree.contourFunction`), scaled by `B n / n`; `0` contour for an infinite tree. -/
noncomputable def heightLibContourPath (B : ℕ → ℝ) (n : ℕ) (τ : BGW.LocallyFinite.Tree) :
    C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ) :=
  (treeHeightPath B n 1 τ,
    if h : BGW.LocallyFinite.FiniteVertices τ then
      (B n / n) • (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).contourFunction
    else 0)

/-- Measurability guard for the library-clock pair (Sol audit k13k16, finding 4). -/
theorem measurable_heightLibContourPath (B : ℕ → ℝ) (n : ℕ) :
    Measurable (heightLibContourPath B n) := by
  apply (measurable_treeHeightPath B n 1).prodMk
  apply measurable_of_measurable_on_compl_countable _ countable_finiteVertices
  have he : (fun τ : {τ : BGW.LocallyFinite.Tree |
      ¬ BGW.LocallyFinite.FiniteVertices τ} =>
      if h : BGW.LocallyFinite.FiniteVertices (τ : BGW.LocallyFinite.Tree) then
        (B n / n) • (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).contourFunction
      else 0) = fun _ => 0 := by
    funext τ
    exact dite_eq_right τ.property
  change Measurable (fun τ : {τ : BGW.LocallyFinite.Tree |
    ¬ BGW.LocallyFinite.FiniteVertices τ} =>
      if h : BGW.LocallyFinite.FiniteVertices (τ : BGW.LocallyFinite.Tree) then
        (B n / n) • (PlaneTree.equivFiniteVertices.symm ⟨τ, h⟩).contourFunction
      else 0)
  rw [he]
  exact measurable_const

/-- The exact-size height/contour law in the library contour convention. -/
noncomputable def exactHeightLibContourLaw (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ)
    (_hn : Admissible μ n) :
    ProbabilityMeasure (C(Set.Icc (0 : ℝ) 1, ℝ) × C(Set.Icc (0 : ℝ) 1, ℝ)) :=
  (exactTreeLaw μ n).map (heightLibContourPath B n)

/-- The contour path is a measurable observable of the tree. -/
theorem measurable_treeContourPath (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) :
    Measurable (treeContourPath B n T) := by
  apply measurable_of_measurable_on_compl_countable _ countable_finiteVertices
  have he : (fun τ : {τ : BGW.LocallyFinite.Tree |
      ¬ BGW.LocallyFinite.FiniteVertices τ} => treeContourPath B n T τ) =
      fun _ => 0 := by
    funext τ
    apply ContinuousMap.ext
    intro x
    rw [treeContourPath, dite_eq_left (continuous_treeContourLin _)]
    change B n / n * treeContourLin τ (2 * (n : ℝ) * x) = 0
    rw [treeContourLin, dite_eq_right τ.property, mul_zero]
  change Measurable (fun τ : {τ : BGW.LocallyFinite.Tree |
    ¬ BGW.LocallyFinite.FiniteVertices τ} => treeContourPath B n T τ)
  rw [he]
  exact measurable_const

/-- The height and contour of one tree form a measurable pair. -/
theorem measurable_heightContourPath (B : ℕ → ℝ) (n : ℕ) :
    Measurable (heightContourPath B n) :=
  (measurable_treeHeightPath B n 1).prodMk (measurable_treeContourPath B n 1)

/-- The mirrored tree's contour is the reflected contour (the `LocallyFinite` form of
`PlaneTree.contourLin_mirror`). -/
theorem treeContourLin_treeMirror (t : PlaneTree) {s : ℝ} (hs0 : 0 ≤ s)
    (hs : s ≤ 2 * ((t.size : ℝ) - 1)) :
    treeContourLin (treeMirror t.toLocallyFinite) s =
      treeContourLin t.toLocallyFinite (2 * ((t.size : ℝ) - 1) - s) := by
  rw [treeMirror_toLocallyFinite]
  simp only [treeContourLin, dite_eq_left (PlaneTree.finiteVertices_toLocallyFinite _)]
  change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices
    t.mirror)).contourLin s =
    (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).contourLin _
  simp only [Equiv.symm_apply_apply]
  exact PlaneTree.contourLin_mirror t hs0 hs


/-- On a finite tree, decoding the contour returns the original polygonal contour. -/
theorem treeContourLin_toLocallyFinite (t : PlaneTree) (s : ℝ) :
    treeContourLin t.toLocallyFinite s = t.contourLin s := by
  rw [treeContourLin, dite_eq_left t.finiteVertices_toLocallyFinite]
  change (PlaneTree.equivFiniteVertices.symm (PlaneTree.equivFiniteVertices t)).contourLin s = _
  rw [Equiv.symm_apply_apply]

/-- On a finite tree the contour path evaluates at the paper clock. -/
theorem treeContourPath_toLocallyFinite (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0) (t : PlaneTree)
    (s : Set.Icc (0 : ℝ) (T : ℝ)) :
    treeContourPath B n T t.toLocallyFinite s =
      B n / n * t.contourLin (2 * (n : ℝ) * (s : ℝ)) := by
  rw [treeContourPath, dite_eq_left (continuous_treeContourLin _)]
  exact congrArg (fun x => B n / n * x) (treeContourLin_toLocallyFinite t _)

/-- **Paper convention, exactly**: for a tree of size `n` the contour path at scale `2nt` is
`(B n / n)` times the sealed `PlaneTree.paperContourFunction` (`s ↦ C_{2ζ s}`). -/
theorem treeContourPath_eq_paperContourFunction (B : ℕ → ℝ) {n : ℕ} (t : PlaneTree)
    (ht : t.size = n) (s : unitInterval) :
    treeContourPath B n 1 t.toLocallyFinite s = B n / n * t.paperContourFunction s := by
  erw [treeContourPath_toLocallyFinite, PlaneTree.paperContourFunction_eq_contourLin, ht]

/-- **Library convention** (`2(n-1)t`, sealed `PlaneTree.contourFunction`): uniformly within
`2 |B n / n|` of the `2nt` convention. -/
theorem abs_treeContourPath_sub_contourFunction_le (B : ℕ → ℝ) {n : ℕ} (t : PlaneTree)
    (ht : t.size = n) (s : unitInterval) :
    |treeContourPath B n 1 t.toLocallyFinite s - B n / n * t.contourFunction s| ≤
      2 * |B n / n| := by
  erw [treeContourPath_toLocallyFinite, PlaneTree.contourFunction_eq_contourLin,
    ← mul_sub, abs_mul]
  have hd : ((2 * (t.size - 1) : ℕ) : ℝ) = 2 * (n : ℝ) - 2 := by
    rw [Nat.cast_mul, Nat.cast_sub (by have := PlaneTree.size_pos t; omega), ht]
    norm_num
    ring
  have hs0 : 0 ≤ (s : ℝ) := s.property.1
  have hh := PlaneTree.abs_contourLin_sub_le t
    (x := 2 * (n : ℝ) * (s : ℝ))
    (y := ((2 * (t.size - 1) : ℕ) : ℝ) * (s : ℝ)) (by positivity) (by positivity)
  have hdiff : |2 * (n : ℝ) * (s : ℝ) -
      ((2 * (t.size - 1) : ℕ) : ℝ) * (s : ℝ)| ≤ 2 := by
    rw [hd, show 2 * (n : ℝ) * (s : ℝ) - (2 * n - 2) * (s : ℝ) =
      2 * (s : ℝ) by ring, abs_of_nonneg (by positivity)]
    linarith [s.property.2]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hh.trans hdiff) (abs_nonneg (B n / n))

end BGW.StableTrees.ExactContour
