/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightExcursionMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Exact scaling of excursion height approximations

Positive space-time dilation transports interval infima and multiplies occupation time by
the time dilation. No sequence identification or probability law enters this calculation.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Positive stable scaling transports a future infimum on the corresponding time window. -/
theorem futureInf_scaleLoc (θ : ℝ) (c : Ioi (0 : ℝ)) (f : DLoc)
    {s t : ℝ≥0} (hst : s ≤ t) :
    futureInf (scaleLoc θ c f) ((c : ℝ).toNNReal * t) ((c : ℝ).toNNReal * s) =
      (c : ℝ) ^ (1 / θ) * futureInf f t s := by
  let k : ℝ≥0 := (c : ℝ).toNNReal
  let a : ℝ := (c : ℝ) ^ (1 / θ)
  have hk : 0 < k := Real.toNNReal_pos.mpr c.2
  have ha : 0 < a := Real.rpow_pos_of_pos c.2 _
  have hkst : k * s ≤ k * t := mul_le_mul_of_nonneg_left hst hk.le
  have hlow : a * futureInf f t s ≤ futureInf (scaleLoc θ c f) (k * t) (k * s) := by
    let : Nonempty (Icc (min (k * s) (k * t)) (k * t)) :=
      ⟨⟨k * t, min_le_right _ _, le_rfl⟩⟩
    apply le_ciInf
    intro v
    have hvlo : k * s ≤ (v : ℝ≥0) := by simpa only [min_eq_left hkst] using v.2.1
    have hv : v / k ∈ Icc (min s t) t := by
      rw [min_eq_left hst]
      exact ⟨(le_div_iff₀ hk).mpr (by simpa only [mul_comm] using hvlo),
        (div_le_iff₀ hk).mpr (by simpa only [mul_comm] using v.2.2)⟩
    exact mul_le_mul_of_nonneg_left (futureInf_le_eval f t s (v / k) hv) ha.le
  have hupp : futureInf (scaleLoc θ c f) (k * t) (k * s) / a ≤ futureInf f t s := by
    let : Nonempty (Icc (min s t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
    apply le_ciInf
    intro v
    have hvlo : s ≤ (v : ℝ≥0) := by simpa only [min_eq_left hst] using v.2.1
    have hv : k * v ∈ Icc (min (k * s) (k * t)) (k * t) := by
      rw [min_eq_left hkst]
      exact ⟨mul_le_mul_of_nonneg_left hvlo hk.le,
        mul_le_mul_of_nonneg_left v.2.2 hk.le⟩
    have hh := futureInf_le_eval (scaleLoc θ c f) (k * t) (k * s) (k * v) hv
    change futureInf (scaleLoc θ c f) (k * t) (k * s) ≤ a * f.1 (k * v / k) at hh
    rw [mul_div_cancel_left₀ _ hk.ne'] at hh
    exact (div_le_iff₀ ha).mpr (by simpa only [mul_comm] using hh)
  exact le_antisymm ((div_le_iff₀ ha).mp hupp |>.trans_eq (mul_comm _ a)) hlow

/-- The height occupation approximation obeys exact space-time scaling at every cutoff. -/
theorem heightApprox_scaleLoc (θ : ℝ) (c : Ioi (0 : ℝ)) (f : DLoc) (t : ℝ≥0) (ε : ℝ) :
    heightApprox ε (scaleLoc θ c f) ((c : ℝ).toNNReal * t) =
      (c : ℝ) ^ (1 - 1 / θ) * heightApprox (ε / (c : ℝ) ^ (1 / θ)) f t := by
  let k : ℝ≥0 := (c : ℝ).toNNReal
  let a : ℝ := (c : ℝ) ^ (1 / θ)
  have hk : 0 < k := Real.toNNReal_pos.mpr c.2
  have ha : 0 < a := Real.rpow_pos_of_pos c.2 _
  let A : Set ℝ := {s | 0 ≤ s ∧ s ≤ (t : ℝ) ∧
    f.1 s.toNNReal < futureInf f t s.toNNReal + ε / a}
  let B : Set ℝ := {s | 0 ≤ s ∧ s ≤ ((k * t : ℝ≥0) : ℝ) ∧
    (scaleLoc θ c f).1 s.toNNReal < futureInf (scaleLoc θ c f) (k * t) s.toNNReal + ε}
  have hpre : (fun s : ℝ => (c : ℝ) * s) ⁻¹' B = A := by
    ext s
    have hktime : ((k * t : ℝ≥0) : ℝ) = (c : ℝ) * t := by
      simp only [NNReal.coe_mul, k, Real.coe_toNNReal _ c.2.le]
    by_cases hs : 0 ≤ s ∧ s ≤ (t : ℝ)
    · have hprod : ((c : ℝ) * s).toNNReal = k * s.toNNReal := by
        simpa only [k, Real.toNNReal_coe] using Real.toNNReal_mul (q := s) c.2.le
      have hst : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hs.2
      change (0 ≤ (c : ℝ) * s ∧ (c : ℝ) * s ≤ ((k * t : ℝ≥0) : ℝ) ∧ _) ↔
        (0 ≤ s ∧ s ≤ (t : ℝ) ∧ _)
      rw [hktime, hprod, futureInf_scaleLoc θ c f hst]
      change (0 ≤ (c : ℝ) * s ∧ (c : ℝ) * s ≤ (c : ℝ) * t ∧
        a * f.1 (k * s.toNNReal / k) < a * futureInf f t s.toNNReal + ε) ↔ _
      rw [mul_div_cancel_left₀ _ hk.ne']
      have hεeq : a * (futureInf f t s.toNNReal + ε / a) =
          a * futureInf f t s.toNNReal + ε := by field_simp
      rw [← hεeq, mul_lt_mul_iff_right₀ ha]
      simp only [hs.1, hs.2, mul_nonneg c.2.le hs.1,
        (mul_le_mul_iff_right₀ c.2).mpr hs.2, true_and]
    · have hnot : ¬ (0 ≤ (c : ℝ) * s ∧ (c : ℝ) * s ≤ ((k * t : ℝ≥0) : ℝ)) := by
        rw [hktime]
        intro h
        exact hs ⟨(mul_nonneg_iff_of_pos_left c.2).mp h.1,
          (mul_le_mul_iff_right₀ c.2).mp h.2⟩
      change (0 ≤ (c : ℝ) * s ∧ (c : ℝ) * s ≤ ((k * t : ℝ≥0) : ℝ) ∧ _) ↔
        (0 ≤ s ∧ s ≤ (t : ℝ) ∧ _)
      tauto
  have hinv : B = (fun s : ℝ => (c : ℝ)⁻¹ * s) ⁻¹' A := by
    ext s
    have hh := congrArg (fun S : Set ℝ => ((c : ℝ)⁻¹ * s) ∈ S) hpre
    simpa only [mem_preimage, mul_inv_cancel_left₀ c.2.ne', eq_iff_iff] using hh
  have hvol : volume B = ENNReal.ofReal (c : ℝ) * volume A := by
    rw [hinv, Real.volume_preimage_mul_left (inv_ne_zero c.2.ne'), inv_inv,
      abs_of_pos c.2]
  have hcoef : (c : ℝ) ^ (1 - 1 / θ) * a = (c : ℝ) := by
    rw [show a = (c : ℝ) ^ (1 / θ) from rfl, ← Real.rpow_add c.2,
      sub_add_cancel, Real.rpow_one]
  change ε⁻¹ * (volume B).toReal =
    (c : ℝ) ^ (1 - 1 / θ) * ((ε / a)⁻¹ * (volume A).toReal)
  rw [hvol, ENNReal.toReal_mul, ENNReal.toReal_ofReal c.2.le]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  calc
    _ = (c : ℝ) * (ε⁻¹ * (volume A).toReal) := by ring
    _ = ((c : ℝ) ^ (1 - 1 / θ) * a) * (ε⁻¹ * (volume A).toReal) :=
      congrArg (fun z : ℝ => z * (ε⁻¹ * (volume A).toReal)) hcoef.symm
    _ = _ := by simp only [div_eq_mul_inv, one_mul]; ring

end BGW.StableTrees
