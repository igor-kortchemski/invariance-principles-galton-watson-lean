/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.TimeChange
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Basic.ENNReal.Real

/-!
# Logarithmic slope of time changes

Billingsley's logarithmic slope controls composition, inversion and displacement.
The extended nonnegative range includes time changes with unbounded logarithmic slope.
-/

@[expose] public section

open Set
open scoped ENNReal

namespace BGW.Skorokhod

variable {T : ℝ}

/-- Billingsley's slope size `‖σ‖° = sup_{s < t} |log ((σ t - σ s) / (t - s))|` of a time
change, in `ℝ≥0∞` (it may be infinite). -/
noncomputable def TimeChange.logSlope (σ : TimeChange T) : ℝ≥0∞ :=
  ⨆ (s : Set.Icc (0 : ℝ) T) (t : Set.Icc (0 : ℝ) T) (_ : s < t),
    ENNReal.ofReal |Real.log (((σ t : ℝ) - σ s) / ((t : ℝ) - s))|

/-- Every secant logarithmic slope is bounded by the slope size. -/
theorem TimeChange.ofReal_abs_log_le_logSlope (σ : TimeChange T)
    {s t : Icc (0 : ℝ) T} (hst : s < t) :
    ENNReal.ofReal |Real.log (((σ t : ℝ) - σ s) / ((t : ℝ) - s))| ≤ σ.logSlope :=
  le_iSup_of_le s (le_iSup_of_le t (le_iSup_of_le hst le_rfl))

/-- The identity time change has zero logarithmic slope. -/
@[simp] theorem TimeChange.logSlope_refl :
    TimeChange.logSlope (OrderIso.refl (Icc (0 : ℝ) T)) = 0 := by
  apply le_antisymm _ zero_le
  refine iSup_le fun s => iSup_le fun t => iSup_le fun hst => ?_
  have hne : (t : ℝ) - s ≠ 0 := ne_of_gt (sub_pos.mpr hst)
  simp [hne]

/-- Inversion preserves logarithmic slope. -/
@[simp] theorem TimeChange.logSlope_symm (σ : TimeChange T) :
    TimeChange.logSlope σ.symm = σ.logSlope := by
  have hle : ∀ τ : TimeChange T, TimeChange.logSlope τ.symm ≤ τ.logSlope := by
    intro τ
    refine iSup_le fun s => iSup_le fun t => iSup_le fun hst => ?_
    have hpre : τ.symm s < τ.symm t := τ.symm.strictMono hst
    have h := τ.ofReal_abs_log_le_logSlope hpre
    simp only [OrderIso.apply_symm_apply] at h
    have hinv : ((τ.symm t : ℝ) - τ.symm s) / ((t : ℝ) - s) =
        (((t : ℝ) - s) / ((τ.symm t : ℝ) - τ.symm s))⁻¹ := by
      rw [inv_div]
    rw [hinv, Real.log_inv, abs_neg]
    exact h
  exact le_antisymm (hle σ) (by simpa using hle σ.symm)

/-- Logarithmic slope is subadditive under composition. -/
theorem TimeChange.logSlope_trans_le (σ τ : TimeChange T) :
    TimeChange.logSlope (σ.trans τ) ≤ σ.logSlope + τ.logSlope := by
  refine iSup_le fun s => iSup_le fun t => iSup_le fun hst => ?_
  have hσ : (σ s : ℝ) < σ t := σ.strictMono hst
  have hτ : (τ (σ s) : ℝ) < τ (σ t) := τ.strictMono (σ.strictMono hst)
  have hprod : ((τ (σ t) : ℝ) - τ (σ s)) / ((t : ℝ) - s) =
      (((σ t : ℝ) - σ s) / ((t : ℝ) - s)) *
        (((τ (σ t) : ℝ) - τ (σ s)) / ((σ t : ℝ) - σ s)) := by
    field_simp
  change ENNReal.ofReal |Real.log
    (((τ (σ t) : ℝ) - τ (σ s)) / ((t : ℝ) - s))| ≤ _
  rw [hprod, Real.log_mul (ne_of_gt (div_pos (sub_pos.mpr hσ) (sub_pos.mpr hst)))
    (ne_of_gt (div_pos (sub_pos.mpr hτ) (sub_pos.mpr hσ)))]
  calc
    ENNReal.ofReal |Real.log (((σ t : ℝ) - σ s) / ((t : ℝ) - s)) +
        Real.log (((τ (σ t) : ℝ) - τ (σ s)) / ((σ t : ℝ) - σ s))| ≤
        ENNReal.ofReal (|Real.log (((σ t : ℝ) - σ s) / ((t : ℝ) - s))| +
          |Real.log (((τ (σ t) : ℝ) - τ (σ s)) / ((σ t : ℝ) - σ s))|) :=
      ENNReal.ofReal_le_ofReal (abs_add_le _ _)
    _ = _ := ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ σ.logSlope + τ.logSlope := add_le_add
      (σ.ofReal_abs_log_le_logSlope hst)
      (τ.ofReal_abs_log_le_logSlope (σ.strictMono hst))

/-- A bound on logarithmic slope bounds every secant slope exponentially. -/
theorem TimeChange.sub_le_exp_mul_sub (σ : TimeChange T) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : σ.logSlope ≤ ENNReal.ofReal r) {s t : Icc (0 : ℝ) T} (hst : s ≤ t) :
    (σ t : ℝ) - σ s ≤ Real.exp r * ((t : ℝ) - s) := by
  rcases hst.eq_or_lt with hst | hst
  · simp [hst]
  have habs := (ENNReal.ofReal_le_ofReal_iff hr0).mp
    ((σ.ofReal_abs_log_le_logSlope hst).trans hr)
  have hratio := (Real.log_le_iff_le_exp
    (div_pos (sub_pos.mpr (σ.strictMono hst)) (sub_pos.mpr hst))).mp
      ((le_abs_self _).trans habs)
  exact (div_le_iff₀ (sub_pos.mpr (show (s : ℝ) < t from hst))).mp hratio

/-- Finite logarithmic slope controls displacement from the identity on `[0,T]`. -/
theorem TimeChange.abs_sub_le_mul_exp_sub_one (σ : TimeChange T) {r : ℝ}
    (hr0 : 0 ≤ r) (hr : σ.logSlope ≤ ENNReal.ofReal r) (t : Icc (0 : ℝ) T) :
    |(σ t : ℝ) - t| ≤ (t : ℝ) * (Real.exp r - 1) := by
  have hT : 0 ≤ T := t.2.1.trans t.2.2
  let z : Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hz : σ z = z := σ.apply_zero hT
  have hupper := σ.sub_le_exp_mul_sub hr0 hr (s := z) t.2.1
  have hinv : TimeChange.logSlope σ.symm ≤ ENNReal.ofReal r := by
    simpa using hr
  have hlower := TimeChange.sub_le_exp_mul_sub σ.symm hr0 hinv (s := z) (σ t).2.1
  have hzinv : σ.symm z = z := TimeChange.apply_zero σ.symm hT
  simp only [hz, hzinv, OrderIso.symm_apply_apply, z, sub_zero] at hupper hlower
  have hnonneg : 0 ≤ Real.exp r - 1 := sub_nonneg.mpr (Real.one_le_exp_iff.mpr hr0)
  rcases le_total (t : ℝ) (σ t : ℝ) with ht | ht
  · rw [abs_of_nonneg (sub_nonneg.mpr ht)]
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr ht)]
    have hmul := mul_le_mul_of_nonneg_right ht hnonneg
    nlinarith

end BGW.Skorokhod
