/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureCounts
public import BGW.StableTrees.ExcursionMeasureIntensity
public import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp

/-! The exponential transform on extended nonnegative reals and finite-subset excursion pgfs.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- `exp (-x)` on `ℝ≥0∞`, with `exp (-∞) = 0`. -/
noncomputable def expNeg (x : ℝ≥0∞) : ℝ≥0∞ :=
  if x = ⊤ then 0 else ENNReal.ofReal (Real.exp (-x.toReal))

/-- The exponential transform is the continuous extended-real exponential of the negated input. -/
theorem expNeg_eq_ereal (x : ℝ≥0∞) : expNeg x = EReal.exp (-(x : EReal)) := by
  by_cases hx : x = ⊤
  · simp [expNeg, hx]
  · rw [expNeg, ite_eq_right hx, ← EReal.coe_ennreal_toReal hx, ← EReal.coe_neg, EReal.exp_coe]

/-- The exponential transform is continuous, including its value zero at infinity. -/
theorem continuous_expNeg : Continuous expNeg := by
  simp_rw [funext expNeg_eq_ereal]
  exact ENNReal.continuous_exp.comp (continuous_coe_ennreal_ereal.neg)

/-- The exponential transform decreases with its argument. -/
theorem antitone_expNeg : Antitone expNeg := by
  intro x y hxy
  rw [expNeg_eq_ereal, expNeg_eq_ereal]
  exact EReal.exp_monotone (EReal.neg_le_neg_iff.mpr (EReal.coe_ennreal_le_coe_ennreal_iff.mpr hxy))

/-- The exponential transform at zero is one. -/
@[simp] theorem expNeg_zero : expNeg 0 = 1 := by simp [expNeg]

/-- The exponential transform at infinity is zero. -/
@[simp] theorem expNeg_top : expNeg ⊤ = 0 := by simp [expNeg]

/-- Exponential transforms take values at most one. -/
theorem expNeg_le_one (x : ℝ≥0∞) : expNeg x ≤ 1 := by
  simpa using antitone_expNeg (show 0 ≤ x from bot_le)

/-- The exponential transform takes sums to products. -/
theorem expNeg_add (x y : ℝ≥0∞) : expNeg (x + y) = expNeg x * expNeg y := by
  simp only [expNeg_eq_ereal, EReal.coe_ennreal_add]
  rw [EReal.neg_add (Or.inl (EReal.coe_ennreal_ne_bot x))
    (Or.inr (EReal.coe_ennreal_ne_bot y)), sub_eq_add_neg, EReal.exp_add]

/-- Multiplication by a natural number becomes an exponential-transform power. -/
theorem expNeg_mul_nat (x : ℝ≥0∞) (n : ℕ) : expNeg (x * n) = expNeg x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp only [Nat.cast_add, Nat.cast_one, mul_add, mul_one, expNeg_add, ih, pow_succ]

/-- Joint real pgfs for arbitrary disjoint measurable subsets of a bounded lifetime-slab box. -/
theorem excursion_pgf_subsets {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    (T ε : ℝ≥0) (hε : 0 < ε) {k : ℕ} (B : Fin k → Set (ℝ≥0 × Excursion))
    (hB : ∀ i, MeasurableSet (B i))
    (hsub : ∀ i, B i ⊆ Ioc 0 T ×ˢ {e : Excursion | ε < e.lifetime})
    (hd : Pairwise (Function.onFun Disjoint B)) (z : Fin k → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) :
    (∫ f, ∏ i, z i ^ natCount (ξ f) (B i) ∂(stableLocalLaw θ : Measure DLoc)) =
      Real.exp (∑ i, ((lebNN.prod (excursionMeasure θ)) (B i)).toReal * (z i - 1)) := by
  obtain ⟨hlevy, hslab⟩ := isTimeSimpleLevy_of_ae_eq_excursionPointMeasure hθ hξ hae
  have hz (i : Fin k) : ‖(z i : ℂ)‖ ≤ 1 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hz0 i)] using hz1 i
  have hh := integral_complex_pgf_subsets hlevy (hslab ε hε).2 T B hB hsub hd
    (fun i => (z i : ℂ)) hz
  have hmean (i : Fin k) : (∫ f, (natCount (ξ f) (B i) : ℝ)
      ∂(stableLocalLaw θ : Measure DLoc)) = ((lebNN.prod (excursionMeasure θ)) (B i)).toReal := by
    rw [integral_natCount_subset hlevy (hslab ε hε).2 (hB i) (hsub i),
      lintegral_pointMeasure_eq_prod hθ hξ hae (hB i)]
  simp_rw [hmean] at hh
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  convert hh using 1 <;> simp

end BGW.StableTrees
