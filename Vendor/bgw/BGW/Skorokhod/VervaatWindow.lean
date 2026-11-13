/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Continuous
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Local correction of a time change

A triangular perturbation of the identity moves one interior time to a nearby
time and is the identity outside a prescribed window. Its slope stays positive.
-/

@[expose] public section

open Set

namespace BGW.Skorokhod

/-- Move `g` to `a` by a time change supported in the radius `η` window around `g`.
The displacement is at most the distance between the two times. -/
theorem exists_local_timeChange (g a : Icc (0 : ℝ) 1) {η : ℝ} (hη : 0 < η)
    (hleft : η ≤ (g : ℝ)) (hright : (g : ℝ) + η ≤ 1)
    (hnear : |(a : ℝ) - g| < η) :
    ∃ κ : TimeChange 1, κ g = a ∧
      (∀ t : Icc (0 : ℝ) 1, η ≤ |(t : ℝ) - g| → κ t = t) ∧
      ∀ t : Icc (0 : ℝ) 1, |(κ t : ℝ) - t| ≤ |(a : ℝ) - g| := by
  let w : ℝ → ℝ := fun t => max (η - |t - g|) 0
  let k : ℝ := ((a : ℝ) - g) / η
  let F : ℝ → ℝ := fun t => t + k * w t
  have hw (t : ℝ) : 0 ≤ w t ∧ w t ≤ η :=
    ⟨le_max_right _ _, max_le (by linarith [abs_nonneg (t - g)]) hη.le⟩
  have hwlip (s t : ℝ) : |w s - w t| ≤ |s - t| := by
    calc
      |w s - w t| ≤ |(η - |s - g|) - (η - |t - g|)| :=
        abs_max_sub_max_le_abs _ _ 0
      _ = abs (|s - g| - |t - g|) := by
        rw [show (η - |s - g|) - (η - |t - g|) = -(|s - g| - |t - g|) by ring,
          abs_neg]
      _ ≤ |(s - g) - (t - g)| := abs_abs_sub_abs_le _ _
      _ = |s - t| := by congr 1; ring
  have hk : |k| < 1 := by
    dsimp [k]
    rw [abs_div, abs_of_pos hη]
    exact (div_lt_one hη).mpr hnear
  have hstrict : StrictMono F := by
    intro s t hst
    have hab : |k * (w t - w s)| ≤ |k| * (t - s) := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hwlip t s) (abs_nonneg k)).trans_eq
        (by rw [abs_of_pos (sub_pos.mpr hst)])
    have hbound := (abs_le.mp hab).1
    have hpos := mul_pos (sub_pos.mpr hk) (sub_pos.mpr hst)
    dsimp [F]
    nlinarith
  have hcont : Continuous F := continuous_id.add
    (continuous_const.mul (((continuous_const.sub
      (continuous_id.sub continuous_const).abs).max continuous_const)))
  have hout (t : ℝ) (ht : η ≤ |t - g|) : F t = t := by
    simp [F, w, max_eq_right (sub_nonpos.mpr ht)]
  have hzero : F 0 = 0 := hout 0 (by simpa [abs_of_nonneg g.2.1] using hleft)
  have hone : F 1 = 1 := hout 1 (by rw [abs_of_nonneg (sub_nonneg.mpr g.2.2)]; linarith)
  have hfg : F g = a := by
    dsimp [F, w, k]
    rw [sub_self, abs_zero, sub_zero, max_eq_left hη.le, div_mul_cancel₀ _ hη.ne']
    ring
  let φ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
    ⟨F t, by
      constructor
      · simpa only [hzero] using hstrict.monotone t.2.1
      · simpa only [hone] using hstrict.monotone t.2.2⟩
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : (y : ℝ) ∈ Icc (F 0) (F 1) := by rw [hzero, hone]; exact y.2
    obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc zero_le_one hcont.continuousOn hy
    exact ⟨⟨t, ht⟩, Subtype.ext hFt⟩
  let κ : TimeChange 1 := StrictMono.orderIsoOfSurjective φ
    (fun s t hst => hstrict hst) hsurj
  refine ⟨κ, Subtype.ext hfg, fun t ht => Subtype.ext (hout t ht), ?_⟩
  intro t
  change |F t - t| ≤ |(a : ℝ) - g|
  calc
    |F t - t| = |k| * w t := by dsimp [F]; rw [add_sub_cancel_left, abs_mul,
      abs_of_nonneg (hw t).1]
    _ ≤ |k| * η := mul_le_mul_of_nonneg_left (hw t).2 (abs_nonneg _)
    _ = |(a : ℝ) - g| := by
      dsimp [k]
      rw [abs_div, abs_of_pos hη, div_mul_cancel₀ _ hη.ne']

end BGW.Skorokhod
