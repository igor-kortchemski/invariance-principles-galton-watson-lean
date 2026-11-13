/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
public import Mathlib.Basic.ENNReal.Operations
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Basic.ENNReal.Real
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The offspring generating function in `[0, ∞]`

For an offspring law `μ` on `ℕ`, `offspringGF μ s = ∑ k, μ {k} * s ^ k` in `ℝ≥0∞`, with
`0 ^ 0 = 1`. Only elementary facts are proved: the values at `0` and `1`, monotonicity, and the
uniqueness of the fixed point `1` in `[0, 1]` for a law of mean at most one with `μ {1} ≠ 1`
(`eq_one_of_offspringGF_eq`), and, for a law of mean greater than one (infinite mean allowed), a
point `s < 1` with `f s ≤ s` (`exists_lt_one_offspringGF_le`). The extinction results use
monotonicity; the normalization results use the uniqueness; the supercritical classification uses
the point below one. Adapted from `PoissonDeclumping/Bienayme/Normalization.lean`, where the
generating function is defined on a probability mass function.
-/

@[expose] public section

namespace BGW

open MeasureTheory
open scoped ENNReal

/-- The generating function `s ↦ ∑ k, μ {k} * s ^ k` of an offspring law, with values in `ℝ≥0∞`. -/
noncomputable def offspringGF (μ : Measure ℕ) (s : ℝ≥0∞) : ℝ≥0∞ := ∑' k : ℕ, μ {k} * s ^ k

/-- `f 0 = μ {0}`. -/
theorem offspringGF_zero (μ : Measure ℕ) : offspringGF μ 0 = μ {0} := by
  rw [offspringGF, tsum_eq_single 0]
  · simp
  · intro k hk
    simp [zero_pow hk]

/-- The point masses of a probability measure on `ℕ` sum to one. -/
theorem tsum_measure_singleton (μ : Measure ℕ) [IsProbabilityMeasure μ] : ∑' k : ℕ, μ {k} = 1 := by
  rw [← measure_iUnion (fun _ _ hij => Set.disjoint_singleton.mpr hij)
      (fun _ => measurableSet_singleton _), Set.iUnion_of_singleton, measure_univ]

/-- `f 1 = 1` for a probability measure. -/
theorem offspringGF_one (μ : Measure ℕ) [IsProbabilityMeasure μ] : offspringGF μ 1 = 1 := by
  simp only [offspringGF, one_pow, mul_one]
  exact tsum_measure_singleton μ

/-- The generating function is monotone on `[0, ∞]`; no hypothesis on `μ` is needed. -/
theorem offspringGF_mono (μ : Measure ℕ) : Monotone (offspringGF μ) := fun _ _ hst =>
  ENNReal.tsum_le_tsum fun k => by gcongr

/-! ### The fixed point `1` is unique for mean at most one -/

/-- A law of mean exactly one with `μ {1} ≠ 1` puts mass on some `j ≥ 2`. -/
private theorem exists_two_le_ne_zero (μ : Measure ℕ)
    (hm : ∑' k : ℕ, (k : ℝ≥0∞) * μ {k} = 1) (hne : μ {1} ≠ 1) : ∃ j : ℕ, 2 ≤ j ∧ μ {j} ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  rw [tsum_eq_single 1] at hm
  · simpa using hm
  · intro j hj
    rcases j with _ | _ | j
    · simp
    · exact absurd rfl hj
    · simp [h (j + 2) (by omega)]

/-- Strict Bernoulli inequality: `1 + j (x - 1) < x ^ j` for `0 ≤ x < 1` and `j ≥ 2`. -/
private theorem one_add_mul_sub_lt_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
    ∀ m : ℕ, 1 + ((m + 2 : ℕ) : ℝ) * (x - 1) < x ^ (m + 2)
  | 0 => by
    push_cast
    nlinarith [sq_pos_of_pos (sub_pos.2 hx1)]
  | m + 1 => by
    have ih := one_add_mul_sub_lt_pow hx0 hx1 m
    have hm : (0 : ℝ) ≤ m := m.cast_nonneg
    push_cast at ih ⊢
    rw [pow_succ]
    nlinarith [sq_pos_of_pos (sub_pos.2 hx1), mul_le_mul_of_nonneg_right ih.le hx0]

/-- For an offspring law of mean at most one with `μ {1} ≠ 1`, the only fixed point of the
generating function in `[0, 1]` is `1`. -/
theorem eq_one_of_offspringGF_eq (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : ∑' k : ℕ, (k : ℝ≥0∞) * μ {k} ≤ 1) (hne : μ {1} ≠ 1) {s : ℝ≥0∞} (hs : s ≤ 1)
    (hfix : offspringGF μ s = s) : s = 1 := by
  by_contra hs1
  have hst : s ≠ ∞ := ne_top_of_le_ne_top ENNReal.one_ne_top hs
  have hslt : s < 1 := lt_of_le_of_ne hs hs1
  set x := s.toReal with hxdef
  have hx0 : 0 ≤ x := ENNReal.toReal_nonneg
  have hx1 : x < 1 := by
    rw [hxdef]
    exact ENNReal.toReal_lt_of_lt_ofReal (by simpa using hslt)
  have hsx : s = ENNReal.ofReal x := (ENNReal.ofReal_toReal hst).symm
  -- `s ^ k + k (1 - s)` as a real number
  have hkey : ∀ k : ℕ, s ^ k + (k : ℝ≥0∞) * (1 - s) =
      ENNReal.ofReal (x ^ k + (k : ℝ) * (1 - x)) := by
    intro k
    rw [hsx, ENNReal.ofReal_add (pow_nonneg hx0 k)
      (mul_nonneg k.cast_nonneg (by linarith)), ENNReal.ofReal_pow hx0,
      ENNReal.ofReal_mul k.cast_nonneg, ENNReal.ofReal_natCast,
      ENNReal.ofReal_sub _ hx0, ENNReal.ofReal_one]
  have hle : ∀ k : ℕ, 1 ≤ s ^ k + (k : ℝ≥0∞) * (1 - s) := by
    intro k
    rw [hkey, ENNReal.one_le_ofReal]
    have := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ x by linarith) k
    linarith
  have hsum : ∑' k : ℕ, μ {k} * (s ^ k + (k : ℝ≥0∞) * (1 - s)) =
      s + (1 - s) * ∑' k : ℕ, (k : ℝ≥0∞) * μ {k} := by
    simp only [mul_add, ENNReal.tsum_add]
    have : ∀ k : ℕ, μ {k} * ((k : ℝ≥0∞) * (1 - s)) = (1 - s) * ((k : ℝ≥0∞) * μ {k}) := by
      intro k; ring
    simp only [this, ENNReal.tsum_mul_left]
    rw [show ∑' k : ℕ, μ {k} * s ^ k = offspringGF μ s from rfl, hfix]
  have hge : (1 : ℝ≥0∞) ≤ ∑' k : ℕ, μ {k} * (s ^ k + (k : ℝ≥0∞) * (1 - s)) := by
    calc (1 : ℝ≥0∞) = ∑' k : ℕ, μ {k} * 1 := by simp [tsum_measure_singleton]
      _ ≤ _ := ENNReal.tsum_le_tsum fun k => by gcongr; exact hle k
  have h1s : (1 - s) ≠ 0 := (tsub_pos_of_lt hslt).ne'
  have h1st : (1 - s) ≠ ∞ := ENNReal.sub_ne_top ENNReal.one_ne_top
  rcases hm.lt_or_eq with hlt | heq
  · -- mean below one
    have : s + (1 - s) * ∑' k : ℕ, (k : ℝ≥0∞) * μ {k} < 1 := by
      calc s + (1 - s) * ∑' k : ℕ, (k : ℝ≥0∞) * μ {k} < s + (1 - s) * 1 :=
            (ENNReal.add_lt_add_iff_left hst).2 ((ENNReal.mul_lt_mul_iff_right h1s h1st).2 hlt)
        _ = 1 := by rw [mul_one, add_tsub_cancel_of_le hs]
    rw [hsum] at hge
    exact absurd hge (not_le.2 this)
  · -- mean one: a strict term from some `j ≥ 2`
    obtain ⟨j, hj, hμj⟩ := exists_two_le_ne_zero μ heq hne
    have hlt : 1 < s ^ j + (j : ℝ≥0∞) * (1 - s) := by
      rw [hkey, ENNReal.one_lt_ofReal]
      obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hj
      have := one_add_mul_sub_lt_pow hx0 hx1 m
      linarith
    have hlt' : ∑' k : ℕ, μ {k} * 1 <
        ∑' k : ℕ, μ {k} * (s ^ k + (k : ℝ≥0∞) * (1 - s)) := by
      refine ENNReal.tsum_lt_tsum (i := j) ?_ (fun k => by gcongr; exact hle k) ?_
      · simp [tsum_measure_singleton]
      · exact (ENNReal.mul_lt_mul_iff_right hμj (measure_ne_top _ _)).2 hlt
    rw [hsum, heq, mul_one, add_tsub_cancel_of_le hs] at hlt'
    simp [tsum_measure_singleton] at hlt'

/-! ### A point below one for mean greater than one -/

/-- For `x ∈ [0, 1]` and `k ≤ N`, `k x ^ N (1 - x) ≤ 1 - x ^ k`. -/
private theorem mul_pow_mul_sub_le_one_sub_pow {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {k N : ℕ}
    (hk : k ≤ N) : (k : ℝ) * x ^ N * (1 - x) ≤ 1 - x ^ k := by
  rw [← geom_sum_mul_neg]
  refine mul_le_mul_of_nonneg_right ?_ (by linarith)
  have h := Finset.card_nsmul_le_sum (Finset.range k) (fun i => x ^ i) (x ^ N) fun i hi =>
    pow_le_pow_of_le_one hx0 hx1 (by have := Finset.mem_range.mp hi; omega)
  simpa using h

/-- For an offspring law of mean greater than one, possibly infinite, there is `s < 1` with
`f s ≤ s`. The mean is truncated to a finite part `M > 1`; with `x ^ N = M⁻¹` one has
`1 - f x ≥ ∑_{k < N} μ {k} (1 - x ^ k) ≥ x ^ N (1 - x) M = 1 - x`. -/
theorem exists_lt_one_offspringGF_le (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (hm : 1 < ∑' k : ℕ, (k : ℝ≥0∞) * μ {k}) : ∃ s : ℝ≥0∞, s < 1 ∧ offspringGF μ s ≤ s := by
  rw [ENNReal.tsum_eq_iSup_nat, lt_iSup_iff] at hm
  obtain ⟨N, hN⟩ := hm
  set M : ℝ≥0∞ := ∑ k ∈ Finset.range N, (k : ℝ≥0∞) * μ {k} with hM
  have hMtop : M ≠ ∞ := ENNReal.sum_ne_top.2 fun k _ =>
    ENNReal.mul_ne_top (ENNReal.natCast_ne_top k) (measure_ne_top _ _)
  have hN0 : N ≠ 0 := by
    rintro rfl
    simp [hM] at hN
  set r : ℝ := M.toReal with hr
  have hr1 : 1 < r := by
    have := (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hMtop).2 hN
    simpa using this
  have hr0 : 0 < r := by linarith
  set x : ℝ := (r⁻¹) ^ ((N : ℝ)⁻¹) with hx
  have hx0 : 0 ≤ x := Real.rpow_nonneg (inv_nonneg.2 hr0.le) _
  have hx1 : x < 1 :=
    Real.rpow_lt_one (inv_nonneg.2 hr0.le) (inv_lt_one_of_one_lt₀ hr1)
      (inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero hN0)))
  have hxN : x ^ N = r⁻¹ := Real.rpow_inv_natCast_pow (inv_nonneg.2 hr0.le) hN0
  refine ⟨ENNReal.ofReal x, ENNReal.ofReal_lt_one.2 hx1, ?_⟩
  set c : ℕ → ℝ≥0∞ := fun k => ENNReal.ofReal (1 - x ^ k) with hc
  have hsplit : ∀ k : ℕ, ENNReal.ofReal x ^ k + c k = 1 := fun k => by
    rw [hc, ← ENNReal.ofReal_pow hx0, ← ENNReal.ofReal_add (pow_nonneg hx0 k)
      (sub_nonneg.2 (pow_le_one₀ hx0 hx1.le)), add_sub_cancel, ENNReal.ofReal_one]
  have hsum : offspringGF μ (ENNReal.ofReal x) + ∑' k : ℕ, μ {k} * c k = 1 := by
    rw [offspringGF, ← ENNReal.tsum_add]
    simp_rw [← mul_add, hsplit, mul_one]
    exact tsum_measure_singleton μ
  have hlow : ENNReal.ofReal (1 - x) ≤ ∑' k : ℕ, μ {k} * c k := by
    calc ENNReal.ofReal (1 - x) = ENNReal.ofReal ((1 - x) * x ^ N) * M := by
          rw [← ENNReal.ofReal_toReal hMtop, ← hr, ← ENNReal.ofReal_mul (mul_nonneg
            (sub_nonneg.2 hx1.le) (pow_nonneg hx0 N)), hxN, mul_assoc, inv_mul_cancel₀ hr0.ne',
            mul_one]
      _ = ∑ k ∈ Finset.range N, μ {k} * ENNReal.ofReal ((k : ℝ) * x ^ N * (1 - x)) := by
          rw [hM, Finset.mul_sum]
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [show (k : ℝ) * x ^ N * (1 - x) = k * ((1 - x) * x ^ N) by ring,
            ENNReal.ofReal_mul k.cast_nonneg, ENNReal.ofReal_natCast]
          ring
      _ ≤ ∑ k ∈ Finset.range N, μ {k} * c k := by
          refine Finset.sum_le_sum fun k hk => ?_
          gcongr
          exact ENNReal.ofReal_le_ofReal (mul_pow_mul_sub_le_one_sub_pow hx0 hx1.le
            (Finset.mem_range.mp hk).le)
      _ ≤ ∑' k : ℕ, μ {k} * c k := ENNReal.sum_le_tsum _
  have h1x : ENNReal.ofReal x + ENNReal.ofReal (1 - x) = 1 := by
    rw [← ENNReal.ofReal_add hx0 (sub_nonneg.2 hx1.le), add_sub_cancel, ENNReal.ofReal_one]
  refine (ENNReal.add_le_add_iff_right
    (ENNReal.ofReal_ne_top (r := 1 - x))).1 ?_
  rw [h1x]
  calc offspringGF μ (ENNReal.ofReal x) + ENNReal.ofReal (1 - x)
      ≤ offspringGF μ (ENNReal.ofReal x) + ∑' k : ℕ, μ {k} * c k := by gcongr
    _ = 1 := hsum

end BGW
