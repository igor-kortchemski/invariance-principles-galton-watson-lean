/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Probability.DoobL2Resolvent
import Mathlib.Probability.BorelCantelli
import Mathlib.Probability.Moments.Variance

/-!
# Maximal bounds for centered independent partial sums

Independent integrable centered increments yield a martingale of inclusive partial sums.
Its second moment is the sum of increment second moments, giving Doob's explicit maximal bound.
This complements the tail-based walk inequalities in `RealWalkMaximal` without duplicating them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
namespace BGW.Probability

/-- Independent integrable centered increments give a martingale of inclusive partial sums. -/
theorem martingale_centered_partialSums {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hm : ∀ i, StronglyMeasurable (X i)) (hi : iIndepFun X P)
    (hint : ∀ i, Integrable (X i) P) (hzero : ∀ i, ∫ ω, X i ω ∂P = 0) :
    Martingale (fun n ω => ∑ i ∈ Finset.range (n + 1), X i ω)
      (Filtration.natural X hm) P := by
  let ℱ := Filtration.natural X hm
  let M (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range (n + 1), X i ω
  have hadp : StronglyAdapted ℱ M := by
    intro n
    apply Finset.stronglyMeasurable_fun_sum
    intro i hi
    exact (Filtration.stronglyAdapted_natural hm i).mono
      (ℱ.mono (by have := Finset.mem_range.mp hi; omega))
  have hM (n : ℕ) : Integrable (M n) P := integrable_finsetSum _ (fun i _ => hint i)
  apply martingale_nat hadp hM
  intro n
  have he : M (n + 1) = M n + X (n + 1) := by
    funext ω
    simp only [M, Pi.add_apply, Finset.sum_range_succ]
  change M n =ᵐ[P] P[M (n + 1) | ℱ n]
  rw [he]
  have hc := hi.condExp_natural_ae_eq_of_lt hm (Nat.lt_succ_self n)
  rw [hzero] at hc
  have hadd := condExp_add (hM n) (hint (n + 1)) (ℱ n)
  have hself := condExp_of_stronglyMeasurable (ℱ.le n) (hadp n) (hM n)
  filter_upwards [hadd, hc] with ω ha hz
  rw [ha]
  change M n ω = P[M n | ℱ n] ω + P[X (n + 1) | ℱ n] ω
  rw [hself, hz, add_zero]

/-- The centered second moment of independent partial sums is the sum of their variances. -/
theorem integral_partialSum_sq_eq_sum {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hmem : ∀ i, MemLp (X i) 2 P) (hi : iIndepFun X P)
    (hzero : ∀ i, ∫ ω, X i ω ∂P = 0) (s : Finset ℕ) :
    (∫ ω, (∑ i ∈ s, X i ω) ^ 2 ∂P) = ∑ i ∈ s, ∫ ω, (X i ω) ^ 2 ∂P := by
  have hsum : MemLp (fun ω => ∑ i ∈ s, X i ω) 2 P :=
    memLp_finsetSum s (fun i _ => hmem i)
  have hs0 : (∫ ω, ∑ i ∈ s, X i ω ∂P) = 0 := by
    rw [integral_finsetSum _ (fun i _ => (hmem i).integrable (by norm_num))]
    simp only [hzero, Finset.sum_const_zero]
  have hv := IndepFun.variance_sum (s := s) (fun i _ => hmem i)
    (fun i _ j _ hij => hi.indepFun hij)
  have hvsum : Var[(fun ω => ∑ i ∈ s, X i ω); P] =
      ∑ i ∈ s, Var[X i; P] := by
    have he : (fun ω => ∑ i ∈ s, X i ω) = ∑ i ∈ s, X i := by
      funext ω
      exact (Finset.sum_apply _ _ _).symm
    rw [he]
    exact hv
  rw [variance_eq_integral hsum.aemeasurable, hs0] at hvsum
  simp only [sub_zero] at hvsum
  rw [hvsum]
  apply Finset.sum_congr rfl
  intro i _
  rw [variance_eq_integral (hmem i).aemeasurable, hzero]
  simp only [sub_zero]

/-- A second-moment maximal bound for independent centered increments, allowing one
extra terminal increment in the upper bound. -/
theorem measure_partialSum_maximal_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsProbabilityMeasure P] {X : ℕ → Ω → ℝ}
    (hm : ∀ i, StronglyMeasurable (X i)) (hi : iIndepFun X P)
    (hmem : ∀ i, MemLp (X i) 2 P) (hzero : ∀ i, ∫ ω, X i ω ∂P = 0)
    (m : ℕ) {r : ℝ} (hr : 0 < r) :
    P {ω | ∃ N ∈ Finset.range (m + 1), r < |∑ i ∈ Finset.range N, X i ω|} ≤
      ENNReal.ofReal (4 * (∑ i ∈ Finset.range (m + 1), ∫ ω, (X i ω) ^ 2 ∂P) / r ^ 2) := by
  let M (n : ℕ) (ω : Ω) : ℝ := ∑ i ∈ Finset.range (n + 1), X i ω
  let R (ω : Ω) : ℝ := (Finset.range (m + 1)).sup'
    Finset.nonempty_range_add_one (fun k => |M k ω|)
  have hM := martingale_centered_partialSums hm hi
    (fun i => (hmem i).integrable (by norm_num)) hzero
  have hMn : MemLp (M m) 2 P := memLp_finsetSum _ (fun i _ => hmem i)
  have hDoob := BGW.Probability.integral_sq_sup_le_four_mul_of_martingale hM m hMn
  have hR2 : Integrable (fun ω => R ω ^ 2) P := hDoob.1
  have hb : (∫ ω, R ω ^ 2 ∂P) ≤
      4 * ∑ i ∈ Finset.range (m + 1), ∫ ω, (X i ω) ^ 2 ∂P := by
    have he := integral_partialSum_sq_eq_sum hmem hi hzero (Finset.range (m + 1))
    exact hDoob.2.trans_eq (congrArg (fun x : ℝ => 4 * x) he)
  let E := {ω | ∃ N ∈ Finset.range (m + 1), r < |∑ i ∈ Finset.range N, X i ω|}
  have hsub : E ⊆ {ω | r ^ 2 ≤ R ω ^ 2} := by
    intro ω hω
    rcases hω with ⟨N, hN, hex⟩
    rcases N with _ | j
    · simp only [Finset.range_zero, Finset.sum_empty, abs_zero] at hex
      exact (hr.not_gt hex).elim
    · have hj : j ∈ Finset.range (m + 1) := by
        apply Finset.mem_range.mpr
        have := Finset.mem_range.mp hN
        omega
      have hsup := Finset.le_sup' (fun k => |M k ω|) hj
      change |M j ω| ≤ R ω at hsup
      change r < |M j ω| at hex
      have hpos : 0 ≤ |M j ω| := abs_nonneg _
      change r ^ 2 ≤ R ω ^ 2
      nlinarith
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Eventually.of_forall fun ω => sq_nonneg (R ω)) hR2 (r ^ 2)
  have hreal : P.real E ≤
      4 * (∑ i ∈ Finset.range (m + 1), ∫ ω, (X i ω) ^ 2 ∂P) / r ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    have hmono := mul_le_mul_of_nonneg_left (measureReal_mono (μ := P) hsub) (sq_nonneg r)
    nlinarith only [hmono, hmark, hb]
  rw [← ofReal_measureReal (μ := P) (s := E)]
  exact ENNReal.ofReal_le_ofReal hreal

end BGW.Probability
