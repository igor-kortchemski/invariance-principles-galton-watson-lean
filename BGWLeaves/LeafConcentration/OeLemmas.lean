module

public import BGWLeaves.LeafConcentration.Defs
import Mathlib.Analysis.PSeries

/-!
# Leaf concentration: calculus of `oe_ε`

Proof of `IsOe.tail` (Remark 2.4 of arXiv:1110.2163v4, `rem:oe`) together
with the helper lemmas `polyExp_absorb`, `IsOe.poly_mul`, `IsOe.add` used by the other modules.
-/

@[expose] public section

namespace BGWLeaves.LeafConcentration.OeLemmas

open Filter
open scoped Topology

/-- `m^s e^{-d m} ≤ (s/d)^s` for `m ≥ 0`, `s > 0`, `d > 0`. -/
private lemma rpow_mul_exp_le {s d : ℝ} (hs : 0 < s) (hd : 0 < d) {m : ℝ} (hm : 0 ≤ m) :
    m ^ s * Real.exp (-d * m) ≤ (s / d) ^ s := by
  have h1 : m * Real.exp (-(d / s) * m) ≤ s / d := by
    have hy : d / s * m ≤ Real.exp (d / s * m) := by
      have := Real.add_one_le_exp (d / s * m)
      linarith
    have hpos : 0 < Real.exp (d / s * m) := Real.exp_pos _
    have : Real.exp (-(d / s) * m) = (Real.exp (d / s * m))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    rw [this, ← div_eq_mul_inv, div_le_iff₀ hpos]
    have hds : 0 < d / s := div_pos hd hs
    calc m = (s / d) * (d / s * m) := by field_simp
      _ ≤ s / d * Real.exp (d / s * m) := by gcongr
      _ = _ := by ring
  have h2 : (m * Real.exp (-(d / s) * m)) ^ s ≤ (s / d) ^ s :=
    Real.rpow_le_rpow (by positivity) h1 hs.le
  calc m ^ s * Real.exp (-d * m) = (m * Real.exp (-(d / s) * m)) ^ s := by
        rw [Real.mul_rpow hm (Real.exp_pos _).le, ← Real.exp_mul]
        congr 2
        field_simp
    _ ≤ _ := h2

/-- A polynomial times `exp (-d n^ε)` is bounded. -/
private lemma pow_mul_exp_bdd {ε : ℝ} (hε : 0 < ε) (q : ℝ) {d : ℝ} (hd : 0 < d) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n : ℕ, (n : ℝ) ^ q * Real.exp (-d * (n : ℝ) ^ ε) ≤ C := by
  set s := q / ε with hs
  refine ⟨max 1 ((s / d) ^ s), le_max_left _ _, fun n => ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.zero_rpow hε.ne', mul_zero, Real.exp_zero, mul_one]
    by_cases hq : q = 0
    · simp [hq]
    · simp [Real.zero_rpow hq]
  · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    set m : ℝ := (n : ℝ) ^ ε with hm
    have hm1 : 1 ≤ m := Real.one_le_rpow hn1 hε.le
    have hnq : (n : ℝ) ^ q = m ^ s := by
      rw [hm, ← Real.rpow_mul (by positivity), hs]; congr 1; field_simp
    rw [hnq]
    rcases le_or_gt s 0 with hs0 | hs0
    · have : m ^ s ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hm1 hs0
      have h2 : Real.exp (-d * m) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith
      calc m ^ s * Real.exp (-d * m) ≤ 1 * 1 :=
            mul_le_mul this h2 (Real.exp_pos _).le zero_le_one
        _ ≤ _ := by simp
    · exact (rpow_mul_exp_le hs0 hd (by positivity)).trans (le_max_right _ _)

/-- Polynomial losses are absorbed by reducing the exponential constant. -/
theorem polyExp_absorb {ε : ℝ} (hε : 0 < ε) (q : ℝ) {c c' : ℝ} (_hc' : 0 < c') (hlt : c' < c) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ,
      (n : ℝ) ^ q * Real.exp (-c * (n : ℝ) ^ ε) ≤ C * Real.exp (-c' * (n : ℝ) ^ ε) := by
  obtain ⟨C, hC1, hC⟩ := pow_mul_exp_bdd hε q (sub_pos.2 hlt)
  refine ⟨C, by linarith, fun n => ?_⟩
  have h := hC n
  have e : Real.exp (-c * (n : ℝ) ^ ε) =
      Real.exp (-(c - c') * (n : ℝ) ^ ε) * Real.exp (-c' * (n : ℝ) ^ ε) := by
    rw [← Real.exp_add]; congr 1; ring
  calc (n : ℝ) ^ q * Real.exp (-c * (n : ℝ) ^ ε)
      = ((n : ℝ) ^ q * Real.exp (-(c - c') * (n : ℝ) ^ ε)) * Real.exp (-c' * (n : ℝ) ^ ε) := by
        rw [e]; ring
    _ ≤ C * Real.exp (-c' * (n : ℝ) ^ ε) := mul_le_mul_of_nonneg_right h (Real.exp_pos _).le

/-- A polynomial factor does not change the exponent of an `oe_ε` bound. -/
theorem IsOe.poly_mul {ε : ℝ} (hε : 0 < ε) {x : ℕ → ℝ} (hx : IsOe ε x) (q : ℝ) :
    IsOe ε (fun n => (n : ℝ) ^ q * x n) := by
  obtain ⟨C, c, hC, hc, h⟩ := hx
  obtain ⟨C', hC', hab⟩ := polyExp_absorb hε q (half_pos hc) (half_lt_self hc)
  refine ⟨C * C', c / 2, mul_pos hC hC', half_pos hc, fun n => ?_⟩
  have hn : 0 ≤ (n : ℝ) ^ q := Real.rpow_nonneg (Nat.cast_nonneg n) q
  calc (n : ℝ) ^ q * x n ≤ (n : ℝ) ^ q * (C * Real.exp (-c * (n : ℝ) ^ ε)) :=
        mul_le_mul_of_nonneg_left (h n) hn
    _ = C * ((n : ℝ) ^ q * Real.exp (-c * (n : ℝ) ^ ε)) := by ring
    _ ≤ C * (C' * Real.exp (-(c / 2) * (n : ℝ) ^ ε)) :=
        mul_le_mul_of_nonneg_left (hab n) hC.le
    _ = C * C' * Real.exp (-(c / 2) * (n : ℝ) ^ ε) := by ring

/-- Sums of two `oe_ε` sequences are `oe_ε`. -/
theorem IsOe.add {ε : ℝ} {x y : ℕ → ℝ} (hx : IsOe ε x) (hy : IsOe ε y) :
    IsOe ε (fun n => x n + y n) := by
  obtain ⟨C₁, c₁, hC₁, hc₁, h₁⟩ := hx
  obtain ⟨C₂, c₂, hC₂, hc₂, h₂⟩ := hy
  refine ⟨C₁ + C₂, min c₁ c₂, add_pos hC₁ hC₂, lt_min hc₁ hc₂, fun n => ?_⟩
  have hn : 0 ≤ (n : ℝ) ^ ε := Real.rpow_nonneg (Nat.cast_nonneg n) ε
  have e1 : Real.exp (-c₁ * (n : ℝ) ^ ε) ≤ Real.exp (-min c₁ c₂ * (n : ℝ) ^ ε) := by
    apply Real.exp_le_exp.2
    nlinarith [min_le_left c₁ c₂]
  have e2 : Real.exp (-c₂ * (n : ℝ) ^ ε) ≤ Real.exp (-min c₁ c₂ * (n : ℝ) ^ ε) := by
    apply Real.exp_le_exp.2
    nlinarith [min_le_right c₁ c₂]
  calc x n + y n ≤ C₁ * Real.exp (-c₁ * (n : ℝ) ^ ε) + C₂ * Real.exp (-c₂ * (n : ℝ) ^ ε) :=
        add_le_add (h₁ n) (h₂ n)
    _ ≤ C₁ * Real.exp (-min c₁ c₂ * (n : ℝ) ^ ε) + C₂ * Real.exp (-min c₁ c₂ * (n : ℝ) ^ ε) :=
        add_le_add (mul_le_mul_of_nonneg_left e1 hC₁.le) (mul_le_mul_of_nonneg_left e2 hC₂.le)
    _ = (C₁ + C₂) * Real.exp (-min c₁ c₂ * (n : ℝ) ^ ε) := by ring

/-- `k ↦ exp (-c k^ε)` is summable. -/
private lemma summable_exp_neg_rpow {ε : ℝ} (hε : 0 < ε) {c : ℝ} (hc : 0 < c) :
    Summable fun k : ℕ => Real.exp (-c * (k : ℝ) ^ ε) := by
  obtain ⟨C, hC1, hC⟩ := pow_mul_exp_bdd hε 2 hc
  refine Summable.of_norm_bounded_eventually_nat (g := fun k : ℕ => C * ((k : ℝ) ^ 2)⁻¹)
    ((Real.summable_nat_pow_inv.2 (by norm_num)).mul_left C) ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have := hC k
  rw [show ((k : ℝ) ^ (2 : ℝ)) = (k : ℝ) ^ 2 by norm_cast] at this
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  linarith

/-- **Remark 2.4 (`rem:oe`)**: if `x_n ≥ 0` is `oe_ε(n)` then `y_n = ∑_{k ≥ n} x_k` is well defined
(`x` is summable, so the `tsum` is not the junk value `0`) and is `oe_ε(n)` with the same exponent
(a smaller constant `c` is needed). -/
theorem IsOe.tail {ε : ℝ} (hε : 0 < ε) {x : ℕ → ℝ} (hx0 : ∀ n, 0 ≤ x n) (hx : IsOe ε x) :
    Summable x ∧ IsOe ε (fun n => ∑' k : ℕ, x (n + k)) := by
  obtain ⟨C, c, hC, hc, h⟩ := hx
  have hsum : Summable x :=
    Summable.of_nonneg_of_le hx0 h ((summable_exp_neg_rpow hε hc).mul_left C)
  refine ⟨hsum, ?_⟩
  have hs2 := summable_exp_neg_rpow hε (half_pos hc)
  set G : ℝ := ∑' k : ℕ, Real.exp (-(c / 2) * (k : ℝ) ^ ε) with hG
  have hG1 : 1 ≤ G := by
    have h0 : Real.exp (-(c / 2) * ((0 : ℕ) : ℝ) ^ ε) = 1 := by
      simp [Real.zero_rpow hε.ne']
    calc (1 : ℝ) = Real.exp (-(c / 2) * ((0 : ℕ) : ℝ) ^ ε) := h0.symm
      _ ≤ G := hs2.le_tsum 0 (fun j _ => (Real.exp_pos _).le)
  refine ⟨C * G, c / 2, by positivity, half_pos hc, fun n => ?_⟩
  have hsn : Summable fun k => x (n + k) := hsum.comp_injective (add_right_injective n)
  have hb : ∀ k : ℕ, x (n + k) ≤
      C * Real.exp (-(c / 2) * (n : ℝ) ^ ε) * Real.exp (-(c / 2) * (k : ℝ) ^ ε) := by
    intro k
    refine (h (n + k)).trans ?_
    rw [mul_assoc, ← Real.exp_add]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hC.le
    have h1 : (n : ℝ) ^ ε ≤ ((n + k : ℕ) : ℝ) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast Nat.le_add_right n k) hε.le
    have h2 : (k : ℝ) ^ ε ≤ ((n + k : ℕ) : ℝ) ^ ε :=
      Real.rpow_le_rpow (Nat.cast_nonneg k) (by exact_mod_cast Nat.le_add_left k n) hε.le
    nlinarith
  calc ∑' k : ℕ, x (n + k)
      ≤ ∑' k : ℕ, C * Real.exp (-(c / 2) * (n : ℝ) ^ ε) * Real.exp (-(c / 2) * (k : ℝ) ^ ε) :=
        hsn.tsum_le_tsum hb (hs2.mul_left _)
    _ = C * Real.exp (-(c / 2) * (n : ℝ) ^ ε) * G := by rw [tsum_mul_left]
    _ = C * G * Real.exp (-(c / 2) * (n : ℝ) ^ ε) := by ring

end BGWLeaves.LeafConcentration.OeLemmas
