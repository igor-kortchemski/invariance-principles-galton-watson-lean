/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.CompleteMetricTimeChange
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Lattice
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Interpolating finite time-change data

A finite infimum of affine wedges extends finite data with prescribed lower and upper
secant bounds. This supplies controlled time changes without choosing interval indices.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace BGW.Skorokhod

private def slopeWedge (c C a b x : ℝ) : ℝ :=
  b + c * (x - a) + (C - c) * max (x - a) 0

private theorem slopeWedge_sub_bounds {c C a b s t : ℝ} (hcC : c ≤ C) (hst : s ≤ t) :
    c * (t - s) ≤ slopeWedge c C a b t - slopeWedge c C a b s ∧
      slopeWedge c C a b t - slopeWedge c C a b s ≤ C * (t - s) := by
  unfold slopeWedge
  rcases le_total a s with has | hsa
  · rw [max_eq_left (sub_nonneg.mpr has),
      max_eq_left (sub_nonneg.mpr (has.trans hst))]
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hcC) (sub_nonneg.mpr hst)]
  · rcases le_total t a with hta | hat
    · rw [max_eq_right (sub_nonpos.mpr hsa), max_eq_right (sub_nonpos.mpr hta)]
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hcC) (sub_nonneg.mpr hst)]
    · rw [max_eq_right (sub_nonpos.mpr hsa), max_eq_left (sub_nonneg.mpr hat)]
      constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr hcC) (sub_nonneg.mpr hat),
        mul_nonneg (sub_nonneg.mpr hcC) (sub_nonneg.mpr hsa)]

private noncomputable def finiteInterpolate {ι : Type*} [Fintype ι] [Nonempty ι]
    (c C : ℝ) (x y : ι → ℝ) (t : ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i => slopeWedge c C (x i) (y i) t)

private theorem finiteInterpolate_sub_bounds {ι : Type*} [Fintype ι] [Nonempty ι]
    {c C : ℝ} (hcC : c ≤ C) (x y : ι → ℝ) {s t : ℝ} (hst : s ≤ t) :
    c * (t - s) ≤ finiteInterpolate c C x y t - finiteInterpolate c C x y s ∧
      finiteInterpolate c C x y t - finiteInterpolate c C x y s ≤ C * (t - s) := by
  have hmin (u : ℝ) : ∃ i, slopeWedge c C (x i) (y i) u =
      finiteInterpolate c C x y u := by
    obtain ⟨i, hi, hle⟩ := (Finset.inf'_le_iff Finset.univ_nonempty).mp
      (le_refl (finiteInterpolate c C x y u))
    exact ⟨i, le_antisymm hle (Finset.inf'_le _ hi)⟩
  have hle (i : ι) (u : ℝ) :
      finiteInterpolate c C x y u ≤ slopeWedge c C (x i) (y i) u :=
    Finset.inf'_le _ (Finset.mem_univ i)
  obtain ⟨i, hi⟩ := hmin s
  obtain ⟨j, hj⟩ := hmin t
  have hbi := slopeWedge_sub_bounds (a := x i) (b := y i) hcC hst
  have hbj := slopeWedge_sub_bounds (a := x j) (b := y j) hcC hst
  constructor
  · linarith [hle j s]
  · linarith [hle i t]

private theorem finiteInterpolate_apply {ι : Type*} [Fintype ι] [Nonempty ι]
    {c C : ℝ} (x y : ι → ℝ)
    (hxy : ∀ i j, x i ≤ x j →
      c * (x j - x i) ≤ y j - y i ∧ y j - y i ≤ C * (x j - x i)) (i : ι) :
    finiteInterpolate c C x y (x i) = y i := by
  apply le_antisymm
  · apply (Finset.inf'_le _ (Finset.mem_univ i)).trans
    simp [slopeWedge]
  · apply Finset.le_inf'
    intro j _
    unfold slopeWedge
    rcases le_total (x i) (x j) with hij | hji
    · rw [max_eq_right (sub_nonpos.mpr hij)]
      have := (hxy i j hij).1
      nlinarith
    · rw [max_eq_left (sub_nonneg.mpr hji)]
      have := (hxy j i hji).2
      nlinarith

private theorem continuous_finiteInterpolate {ι : Type*} [Fintype ι] [Nonempty ι]
    (c C : ℝ) (x y : ι → ℝ) : Continuous (finiteInterpolate c C x y) := by
  apply Continuous.finset_inf'_apply
  intro i _
  unfold slopeWedge
  fun_prop

/-- Finite data satisfying positive lower and upper secant bounds extend to a time change
with the same secant bounds. The endpoint indices need not be distinct. -/
theorem exists_timeChange_of_finite_secant_bounds {T : ℝ} {ι : Type*}
    [Fintype ι] [Nonempty ι] (x y : ι → Icc (0 : ℝ) T) (i₀ iT : ι)
    (hx₀ : (x i₀ : ℝ) = 0) (hxT : (x iT : ℝ) = T)
    (hy₀ : (y i₀ : ℝ) = 0) (hyT : (y iT : ℝ) = T)
    {c C : ℝ} (hc : 0 < c) (hcC : c ≤ C)
    (hxy : ∀ i j, x i ≤ x j →
      c * ((x j : ℝ) - x i) ≤ (y j : ℝ) - y i ∧
        (y j : ℝ) - y i ≤ C * ((x j : ℝ) - x i)) :
    ∃ σ : TimeChange T, (∀ i, σ (x i) = y i) ∧
      ∀ s t : Icc (0 : ℝ) T, s ≤ t →
        c * ((t : ℝ) - s) ≤ (σ t : ℝ) - σ s ∧
          (σ t : ℝ) - σ s ≤ C * ((t : ℝ) - s) := by
  let F := finiteInterpolate c C (fun i => (x i : ℝ)) (fun i => (y i : ℝ))
  have hnode (i : ι) : F (x i) = y i := finiteInterpolate_apply _ _ hxy i
  have hF0 : F 0 = 0 := by simpa [hx₀, hy₀] using hnode i₀
  have hFT : F T = T := by simpa [hxT, hyT] using hnode iT
  have hbounds {s t : ℝ} (hst : s ≤ t) :
      c * (t - s) ≤ F t - F s ∧ F t - F s ≤ C * (t - s) :=
    finiteInterpolate_sub_bounds hcC _ _ hst
  have hstrict : StrictMono F := by
    intro s t hst
    have hpos := mul_pos hc (sub_pos.mpr hst)
    have h := (hbounds hst.le).1
    linarith
  have hcont : Continuous F := continuous_finiteInterpolate _ _ _ _
  let f : Icc (0 : ℝ) T → Icc (0 : ℝ) T := fun t =>
    ⟨F t, by
      constructor
      · simpa only [hF0] using hstrict.monotone t.2.1
      · simpa only [hFT] using hstrict.monotone t.2.2⟩
  have hsurj : Function.Surjective f := by
    intro u
    have hT : 0 ≤ T := (x i₀).2.1.trans (x i₀).2.2
    have hu : (u : ℝ) ∈ Icc (F 0) (F T) := by
      rw [hF0, hFT]
      exact u.2
    obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc hT hcont.continuousOn hu
    exact ⟨⟨t, ht⟩, Subtype.ext hFt⟩
  let σ : TimeChange T := StrictMono.orderIsoOfSurjective f
    (fun s t hst => hstrict hst) hsurj
  refine ⟨σ, ?_, ?_⟩
  · intro i
    exact Subtype.ext (hnode i)
  · intro s t hst
    exact hbounds hst

/-- Exponential two-sided secant bounds control logarithmic slope. -/
theorem TimeChange.logSlope_le_of_secant_bounds {T r : ℝ} (σ : TimeChange T)
    (h : ∀ s t : Icc (0 : ℝ) T, s < t →
      Real.exp (-r) * ((t : ℝ) - s) ≤ (σ t : ℝ) - σ s ∧
        (σ t : ℝ) - σ s ≤ Real.exp r * ((t : ℝ) - s)) :
    σ.logSlope ≤ ENNReal.ofReal r := by
  refine iSup_le fun s => iSup_le fun t => iSup_le fun hst => ?_
  have hpos : 0 < (t : ℝ) - s := sub_pos.mpr hst
  have hratio : 0 < ((σ t : ℝ) - σ s) / ((t : ℝ) - s) :=
    div_pos (sub_pos.mpr (σ.strictMono hst)) hpos
  apply ENNReal.ofReal_le_ofReal
  apply abs_le.mpr
  constructor
  · exact (Real.le_log_iff_exp_le hratio).mpr
      ((le_div_iff₀ hpos).mpr (h s t hst).1)
  · exact (Real.log_le_iff_le_exp hratio).mpr
      ((div_le_iff₀ hpos).mpr (h s t hst).2)

end BGW.Skorokhod
