/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.RealAttraction
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Normalizer bounds for real stable attraction

The normalizer diverges, and its ratio theorem is uniform on compact ranges of index ratios.
Dyadic chaining then gives Potter bounds without assuming that the normalizer is monotone.

References: W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
ch. XVII; N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular Variation* (1987), §1.5
(Potter bounds).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex Set
open scoped Topology

namespace BGW.StableTrees

open BGW.Probability.RealWalk

private theorem exists_charFun_norm_lt_one {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) :
    ∃ t : ℝ, ‖charFun (ν : Measure ℝ) t‖ < 1 := by
  by_contra hnot
  push Not at hnot
  have heq (t : ℝ) : ‖charFun (ν : Measure ℝ) t‖ = 1 :=
    le_antisymm (norm_charFun_le_one t) (hnot t)
  have hlim := h.tendsto_charFun_pow_moving (m := fun n : ℕ => n) tendsto_id
    (u := fun _ : ℕ => (1 : ℝ)) (u₀ := 1) tendsto_const_nhds
  have hnorm := hlim.norm
  have hnorm' : Tendsto (fun n => ‖charFun (ν : Measure ℝ) (1 / B n)‖ ^ n) atTop
      (𝓝 (‖charFun (stableLaw θ : Measure ℝ) 1‖)) := by
    simpa only [norm_pow] using hnorm
  have hconst : (fun n => ‖charFun (ν : Measure ℝ) (1 / B n)‖ ^ n) =
      (fun _ : ℕ => (1 : ℝ)) := by
    funext n
    rw [heq]
    simp
  have hlimone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop
      (𝓝 (‖charFun (stableLaw θ : Measure ℝ) 1‖)) := hconst ▸ hnorm'
  have hEq := tendsto_nhds_unique hlimone tendsto_const_nhds
  have hnormlt : ‖charFun (stableLaw θ : Measure ℝ) 1‖ < 1 := by
    rw [charFun_stableLaw h.index_mem, Scalar.norm_stableCF
      (by linarith [h.index_mem.1] : θ ≠ 0)]
    apply Real.exp_lt_one_iff.2
    exact mul_neg_of_neg_of_pos (Scalar.cos_pi_mul_div_two_neg h.index_mem)
      (by positivity : 0 < |(1 : ℝ)| ^ θ)
  exact (ne_of_lt hnormlt) hEq

/-- The normalizer diverges: `B n → +∞`, without monotonicity. -/
theorem IsRealStableAttracted.tendsto_norming_atTop {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) : Tendsto B atTop atTop := by
  obtain ⟨t, ht⟩ := exists_charFun_norm_lt_one h
  by_contra hn
  rw [tendsto_atTop_atTop] at hn
  push Not at hn
  obtain ⟨K, hK⟩ := hn
  have hpos : ∀ᶠ n in atTop, 0 < B n := h.pos
  have hfreq : ∃ᶠ n in atTop, B n ∈ Icc (0 : ℝ) K := by
    have hf : ∃ᶠ n in atTop, B n < K := by
      rw [frequently_atTop]
      exact hK
    exact (hf.and_eventually hpos).mono fun n hn => ⟨hn.2.le, hn.1.le⟩
  obtain ⟨L, hL, φ, hφ, hBφ⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_Icc 0 K) hfreq
  rw [closure_Icc] at hL
  have hs : Tendsto (fun j => t * B (φ j)) atTop (𝓝 (t * L)) := tendsto_const_nhds.mul hBφ
  have hcf := h.tendsto_charFun_pow_moving hφ.tendsto_atTop hs
  have hid : ∀ᶠ j in atTop, (t * B (φ j)) / B (φ j) = t := by
    filter_upwards [hφ.tendsto_atTop.eventually h.pos] with j hj
    exact mul_div_cancel_right₀ t hj.ne'
  have hcf' : Tendsto (fun j => charFun (ν : Measure ℝ) t ^ φ j) atTop
      (𝓝 (charFun (stableLaw θ : Measure ℝ) (t * L))) := by
    refine hcf.congr' ?_
    filter_upwards [hid] with j hj
    rw [hj]
  have hlim0 : Tendsto (fun j => ‖charFun (ν : Measure ℝ) t‖ ^ φ j) atTop (𝓝 0) := by
    exact (tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) ht).comp hφ.tendsto_atTop
  have hlimcf : Tendsto (fun j => ‖charFun (ν : Measure ℝ) t‖ ^ φ j) atTop
      (𝓝 (‖charFun (stableLaw θ : Measure ℝ) (t * L)‖)) := by
    simpa only [norm_pow] using hcf'.norm
  have hzero : ‖charFun (stableLaw θ : Measure ℝ) (t * L)‖ = 0 :=
    tendsto_nhds_unique hlimcf hlim0
  have hposcf : 0 < ‖charFun (stableLaw θ : Measure ℝ) (t * L)‖ := by
    rw [charFun_stableLaw h.index_mem, Scalar.norm_stableCF
      (by linarith [h.index_mem.1] : θ ≠ 0)]
    exact Real.exp_pos _
  linarith

/-- Uniform convergence of the ratio on compact index ranges. -/
theorem IsRealStableAttracted.uniform_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ, a * n ≤ m → (m : ℝ) ≤ b * n →
      |B m / B n - ((m : ℝ) / n) ^ (1 / θ)| ≤ ε := by
  have _habUsed : a ≤ b := hab
  intro ε hε
  by_contra hnot
  push Not at hnot
  choose q hq using hnot
  choose m hm using fun j => (hq j).2
  have hqtop : Tendsto q atTop atTop := tendsto_atTop_mono (fun j => (hq j).1) tendsto_id
  let r : ℕ → ℝ := fun j => (m j : ℝ) / q j
  have hrmem : ∀ᶠ j in atTop, r j ∈ Icc a b := by
    filter_upwards [eventually_ge_atTop 1] with j hj
    have hqj : 0 < q j := lt_of_lt_of_le (by omega) (hq j).1
    have hqjR : 0 < (q j : ℝ) := Nat.cast_pos.mpr hqj
    change a ≤ (m j : ℝ) / q j ∧ (m j : ℝ) / q j ≤ b
    constructor
    · rw [le_div_iff₀ hqjR]
      exact (hm j).1
    · rw [div_le_iff₀ hqjR]
      exact (hm j).2.1
  obtain ⟨w, hw, φ, hφ, hrφ⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_Icc a b) hrmem.frequently
  rw [closure_Icc] at hw
  have hwpos : 0 < w := lt_of_lt_of_le ha hw.1
  have hratio : Tendsto (fun k => B (m (φ k)) / B (q (φ k))) atTop
      (𝓝 (w ^ (1 / θ))) := by
    apply h.tendsto_norming_ratio hwpos (hqtop.comp hφ.tendsto_atTop)
    convert hrφ using 1
    funext k
    rfl
  have hpow : Tendsto (fun k => r (φ k) ^ (1 / θ)) atTop (𝓝 (w ^ (1 / θ))) :=
    (Real.continuousAt_rpow_const w (1 / θ) (Or.inl hwpos.ne')).tendsto.comp hrφ
  have hdiff : Tendsto
      (fun k => B (m (φ k)) / B (q (φ k)) - r (φ k) ^ (1 / θ)) atTop (𝓝 0) := by
    have := hratio.sub hpow
    simpa using this
  have hsmall : ∀ᶠ k in atTop,
      |B (m (φ k)) / B (q (φ k)) - r (φ k) ^ (1 / θ)| < ε := by
    have hball := (Metric.tendsto_nhds.1 hdiff) ε hε
    filter_upwards [hball] with k hk
    simpa [Real.dist_eq] using hk
  obtain ⟨k, hk⟩ := hsmall.exists
  have hbad := (hm (φ k)).2.2
  have hbad' : ε < |B (m (φ k)) / B (q (φ k)) - r (φ k) ^ (1 / θ)| := by
    simpa [r] using hbad
  exact (lt_asymm hk hbad')

private theorem exists_ordered_potter_bounds {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {δ A : ℝ}
    (hδ : 0 < δ) (hA : 1 < A) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ n,
      B m / B n ≤ A * ((m : ℝ) / n) ^ (1 / θ + δ) ∧
        A⁻¹ * ((m : ℝ) / n) ^ (1 / θ - δ) ≤ B m / B n := by
  have hθpos : 0 < θ := by linarith [h.index_mem.1]
  have hρpos : 0 < 1 / θ := one_div_pos.mpr hθpos
  set D : ℝ := (2 : ℝ) ^ δ with hD
  have hD1 : 1 < D := by
    rw [hD]
    exact Real.one_lt_rpow (by norm_num) hδ
  have hAinvlt : A⁻¹ < 1 := (inv_lt_one₀ (by linarith : 0 < A)).2 hA
  have hDinvlt : D⁻¹ < 1 := inv_lt_one_of_one_lt₀ hD1
  set η : ℝ := min (min (A - 1) (D - 1)) (min (1 - A⁻¹) (1 - D⁻¹)) with hη
  have hηpos : 0 < η := by
    rw [hη]
    exact lt_min (lt_min (by linarith) (by linarith)) (lt_min (by linarith) (by linarith))
  have hηleA : η ≤ A - 1 := by
    rw [hη]
    exact (min_le_left _ _).trans (min_le_left _ _)
  have hηleD : η ≤ D - 1 := by
    rw [hη]
    exact (min_le_left _ _).trans (min_le_right _ _)
  have hηleAinv : η ≤ 1 - A⁻¹ := by
    rw [hη]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hηleDinv : η ≤ 1 - D⁻¹ := by
    rw [hη]
    exact (min_le_right _ _).trans (min_le_right _ _)
  have hηA : 1 + η ≤ A := by
    linarith
  have hηD : 1 + η ≤ D := by
    linarith
  have hηAinv : A⁻¹ ≤ 1 - η := by
    linarith
  have hηDinv : D⁻¹ ≤ 1 - η := by
    linarith
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 h.pos
  obtain ⟨N₂, hN₂⟩ := h.uniform_ratio (a := 1) (b := 2) (by norm_num) (by norm_num)
    η hηpos
  let N := max N₁ (max N₂ 1)
  have hN₂leN : N₂ ≤ N :=
    le_trans (le_max_left N₂ 1) (le_max_right N₁ (max N₂ 1))
  have hNlower : 1 ≤ N := le_trans (le_max_right N₂ 1)
    (le_max_right N₁ (max N₂ 1))
  have hNpos : ∀ n ≥ N, 0 < B n := by
    intro n hn
    exact hN₁ n (le_trans (le_max_left _ _) hn)
  have hlocal : ∀ n ≥ N, ∀ m : ℕ, n ≤ m → m ≤ 2 * n →
      B m / B n ≤ (1 + η) * ((m : ℝ) / n) ^ (1 / θ) ∧
        (1 - η) * ((m : ℝ) / n) ^ (1 / θ) ≤ B m / B n := by
    intro n hn m hnm hm
    have hn₂ : N₂ ≤ n := le_trans hN₂leN hn
    have hn1 : 1 ≤ n := le_trans hNlower hn
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn1
    have hx : 1 ≤ (m : ℝ) / n := by
      rw [le_div_iff₀ hnR, one_mul]
      exact_mod_cast hnm
    have hxpow : 1 ≤ ((m : ℝ) / n) ^ (1 / θ) :=
      Real.one_le_rpow hx (le_of_lt hρpos)
    have hnmR : (n : ℝ) ≤ m := by exact_mod_cast hnm
    have hmR : (m : ℝ) ≤ 2 * n := by exact_mod_cast hm
    have hu := hN₂ n hn₂ m (by simpa only [one_mul] using hnmR) (by exact_mod_cast hm)
    have habs := abs_le.mp hu
    constructor
    · calc B m / B n = (B m / B n - ((m : ℝ) / n) ^ (1 / θ)) +
            ((m : ℝ) / n) ^ (1 / θ) := by ring
        _ ≤ η + ((m : ℝ) / n) ^ (1 / θ) := by
          calc
            _ = ((m : ℝ) / n) ^ (1 / θ) +
                (B m / B n - ((m : ℝ) / n) ^ (1 / θ)) := by ring
            _ ≤ ((m : ℝ) / n) ^ (1 / θ) + η := by nlinarith [habs.2]
            _ = _ := by ring
        _ ≤ (1 + η) * ((m : ℝ) / n) ^ (1 / θ) := by
          nlinarith [mul_nonneg hηpos.le (sub_nonneg.mpr hxpow)]
    · have hmul : η ≤ η * ((m : ℝ) / n) ^ (1 / θ) := by
        nlinarith [mul_nonneg hηpos.le (sub_nonneg.mpr hxpow)]
      calc (1 - η) * ((m : ℝ) / n) ^ (1 / θ) ≤
            ((m : ℝ) / n) ^ (1 / θ) - η := by nlinarith
        _ ≤ B m / B n := by linarith [habs.1]
  have hdoubleUpper : ∀ n ≥ N,
      B (2 * n) / B n ≤ (2 : ℝ) ^ (1 / θ + δ) := by
    intro n hn
    have hx : ((2 * n : ℕ) : ℝ) / n = 2 := by
      have hn1 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) (le_trans hNlower hn)))
      push_cast
      field_simp
    have hu := hlocal n hn (2 * n) (by omega) le_rfl
    rw [hx] at hu
    rw [Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    calc B (2 * n) / B n ≤ (1 + η) * 2 ^ (1 / θ) := hu.1
      _ ≤ D * 2 ^ (1 / θ) := mul_le_mul_of_nonneg_right hηD (by positivity)
      _ = 2 ^ (1 / θ) * 2 ^ δ := by rw [hD]; ring
  have hdoubleLower : ∀ n ≥ N,
      (2 : ℝ) ^ (1 / θ - δ) ≤ B (2 * n) / B n := by
    intro n hn
    have hx : ((2 * n : ℕ) : ℝ) / n = 2 := by
      have hn1 : (n : ℝ) ≠ 0 := by
        exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) (le_trans hNlower hn)))
      push_cast
      field_simp
    have hu := hlocal n hn (2 * n) (by omega) le_rfl
    rw [hx] at hu
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2)]
    calc 2 ^ (1 / θ) / 2 ^ δ = D⁻¹ * 2 ^ (1 / θ) := by rw [hD, div_eq_mul_inv, mul_comm]
      _ ≤ (1 - η) * 2 ^ (1 / θ) :=
        mul_le_mul_of_nonneg_right hηDinv (by positivity)
      _ ≤ B (2 * n) / B n := hu.2
  have key : ∀ k : ℕ, ∀ x : ℕ, N ≤ x → ∀ y : ℕ, x ≤ y → y ≤ 2 ^ k * x →
      B y / B x ≤ A * ((y : ℝ) / x) ^ (1 / θ + δ) ∧
        A⁻¹ * ((y : ℝ) / x) ^ (1 / θ - δ) ≤ B y / B x := by
    intro k
    induction k with
    | zero =>
      intro x hx y hxy hy
      have hEq : y = x := le_antisymm (by simpa using hy) hxy
      subst y
      have hBx : 0 < B x := hNpos x hx
      have hx1 : 1 ≤ x := le_trans hNlower hx
      have hxR : (x : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by norm_num) hx1))
      rw [div_self hxR, Real.one_rpow, Real.one_rpow]
      constructor
      · rw [div_self hBx.ne']
        nlinarith [hA]
      · rw [div_self hBx.ne']
        have hApos : 0 < A := by linarith
        simpa using (inv_le_one₀ hApos).2 hA.le
    | succ k ih =>
      intro x hx y hxy hy
      have hx1 : 1 ≤ x := le_trans hNlower hx
      have hxR : (0 : ℝ) < x := by exact_mod_cast hx1
      have hyx : (1 : ℝ) ≤ (y : ℝ) / x := by
        rw [le_div_iff₀ hxR, one_mul]
        exact_mod_cast hxy
      by_cases h2 : y ≤ 2 * x
      · obtain ⟨hu, hl⟩ := hlocal x hx y hxy h2
        have hpowu : ((y : ℝ) / x) ^ (1 / θ) ≤
            ((y : ℝ) / x) ^ (1 / θ + δ) :=
          Real.rpow_le_rpow_of_exponent_le hyx (by linarith)
        have hpowℓ : ((y : ℝ) / x) ^ (1 / θ - δ) ≤
            ((y : ℝ) / x) ^ (1 / θ) :=
          Real.rpow_le_rpow_of_exponent_le hyx (by linarith)
        constructor
        · calc B y / B x ≤ (1 + η) * ((y : ℝ) / x) ^ (1 / θ) := hu
            _ ≤ A * ((y : ℝ) / x) ^ (1 / θ) :=
              mul_le_mul_of_nonneg_right hηA (Real.rpow_nonneg (by positivity) _)
            _ ≤ A * ((y : ℝ) / x) ^ (1 / θ + δ) :=
              mul_le_mul_of_nonneg_left hpowu (by positivity)
        · calc A⁻¹ * ((y : ℝ) / x) ^ (1 / θ - δ) ≤
              (1 - η) * ((y : ℝ) / x) ^ (1 / θ - δ) :=
                mul_le_mul_of_nonneg_right hηAinv (Real.rpow_nonneg (by positivity) _)
            _ ≤ (1 - η) * ((y : ℝ) / x) ^ (1 / θ) :=
                mul_le_mul_of_nonneg_left hpowℓ (by
                  have hApos : 0 < A := by linarith
                  exact le_trans (le_of_lt (inv_pos.mpr hApos)) hηAinv)
            _ ≤ B y / B x := hl
      · have h2' : 2 * x ≤ y := le_of_not_ge h2
        have hx' : N ≤ 2 * x := le_trans hx (by omega)
        have hy' : y ≤ 2 ^ k * (2 * x) := by
          rw [pow_succ] at hy
          calc y ≤ 2 ^ k * 2 * x := hy
            _ = 2 ^ k * (2 * x) := by ring
        obtain ⟨hu, hl⟩ := ih (2 * x) hx' y h2' hy'
        have hdoubleU := hdoubleUpper x hx
        have hdoubleL := hdoubleLower x hx
        have hBpos : 0 < B (2 * x) := hNpos (2 * x) hx'
        have hBxpos : 0 < B x := hNpos x hx
        have hBypos : 0 < B y := hNpos y (le_trans hx' h2')
        have hratio : B y / B x =
            (B y / B (2 * x)) * (B (2 * x) / B x) := by
          field_simp [hBpos.ne', hBxpos.ne']
        have hsplit (r : ℝ) : ((y : ℝ) / x) ^ r =
            ((y : ℝ) / ((2 * x : ℕ) : ℝ)) ^ r * (2 : ℝ) ^ r := by
          rw [← Real.mul_rpow (by positivity) (by norm_num)]
          congr 1
          push_cast
          field_simp
        have hfirstpos : 0 ≤ A * ((y : ℝ) / ((2 * x : ℕ) : ℝ)) ^ (1 / θ + δ) := by
          positivity
        constructor
        · calc B y / B x = (B y / B (2 * x)) * (B (2 * x) / B x) := hratio
            _ ≤ (A * ((y : ℝ) / ((2 * x : ℕ) : ℝ)) ^ (1 / θ + δ)) *
                (2 : ℝ) ^ (1 / θ + δ) :=
                  mul_le_mul hu hdoubleU (by positivity) hfirstpos
            _ = A * ((y : ℝ) / x) ^ (1 / θ + δ) := by rw [hsplit]; ring
        · calc A⁻¹ * ((y : ℝ) / x) ^ (1 / θ - δ) =
              (A⁻¹ * ((y : ℝ) / ((2 * x : ℕ) : ℝ)) ^ (1 / θ - δ)) *
                (2 : ℝ) ^ (1 / θ - δ) := by rw [hsplit]; ring
            _ ≤ (B y / B (2 * x)) * (B (2 * x) / B x) :=
              mul_le_mul hl hdoubleL (by positivity)
                (div_nonneg hBypos.le hBpos.le)
            _ = B y / B x := hratio.symm
  refine ⟨N, ?_⟩
  intro n hn m hnm
  have hn1 : 1 ≤ n := le_trans hNlower hn
  have hbound : m ≤ 2 ^ m * n := by
    calc m ≤ 2 ^ m := Nat.lt_two_pow_self.le
      _ ≤ 2 ^ m * n := Nat.le_mul_of_pos_right _ hn1
  exact key m n hn m hnm hbound

/-- For any fixed finite set of indices, its normalizers are negligible compared with `B n`. -/
private theorem eventually_abs_ratio_lt_finite {B : ℕ → ℝ} (hB : Tendsto B atTop atTop)
    (M : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m < M, |B m / B n| < ε := by
  let C : ℝ := ∑ m ∈ Finset.range M, |B m|
  have hC : 0 ≤ C := by
    change 0 ≤ ∑ m ∈ Finset.range M, |B m|
    exact Finset.sum_nonneg fun m hm => abs_nonneg _
  have hlarge : ∀ᶠ n in atTop, C / ε < B n := hB.eventually_gt_atTop (C / ε)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hlarge
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.1
    (show ∀ᶠ n in atTop, 0 < B n from hB.eventually_gt_atTop 0)
  refine ⟨max N₁ N₂, ?_⟩
  intro n hn m hm
  have hnlarge : C / ε < B n := hN₁ n (le_trans (le_max_left _ _) hn)
  have hnpos : 0 < B n := hN₂ n (le_trans (le_max_right _ _) hn)
  have hmC : |B m| ≤ C := by
    change |B m| ≤ ∑ k ∈ Finset.range M, |B k|
    exact Finset.single_le_sum (f := fun k => |B k|)
      (fun k hk => abs_nonneg _) (Finset.mem_range.mpr hm)
  calc
    |B m / B n| = |B m| / B n := by rw [abs_div, abs_of_pos hnpos]
    _ ≤ C / B n := div_le_div_of_nonneg_right hmC hnpos.le
    _ < ε := (div_lt_iff₀ hnpos).2 (by nlinarith [((div_lt_iff₀ hε).1 hnlarge)])

/-- Potter-type upper bound without monotonicity: for every `ε' > 0` and every `A > 1`, for
all large indices `m, n` (both `≥ N`), `B m / B n ≤ A * max ((m/n)^(1/θ + ε'))
((m/n)^(1/θ - ε'))`. -/
theorem IsRealStableAttracted.potter_upper {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) {ε' A : ℝ} (hε' : 0 < ε') (hA : 1 < A) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      B m / B n ≤ A * max (((m : ℝ) / n) ^ (1 / θ + ε')) (((m : ℝ) / n) ^ (1 / θ - ε')) := by
  obtain ⟨N₀, hN₀⟩ := exists_ordered_potter_bounds h hε' hA
  obtain ⟨Npos, hpos⟩ := Filter.eventually_atTop.1 h.pos
  let N := max 1 (max N₀ Npos)
  have hN₀le : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hNposle : Npos ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  have hNgeone : 1 ≤ N := le_max_left _ _
  refine ⟨N, fun n hn m hm => ?_⟩
  rcases le_total n m with hnm | hmn
  · obtain ⟨hu, _⟩ := hN₀ n (le_trans hN₀le hn) m hnm
    exact hu.trans (mul_le_mul_of_nonneg_left (le_max_left _ _) (by linarith))
  · have hordered := hN₀ m (le_trans hN₀le hm) n hmn
    have hθpos : 0 < θ := by linarith [h.index_mem.1]
    have hρpos : 0 < 1 / θ := one_div_pos.mpr hθpos
    have hx : 0 < (m : ℝ) / n := by
      have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) (le_trans hNgeone hm)
      have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans hNgeone hn)
      exact div_pos (by exact_mod_cast hmpos) (by exact_mod_cast hnpos)
    have hxle : (m : ℝ) / n ≤ 1 := by
      have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hnR : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num) (le_trans hNgeone hn))
      rw [div_le_one₀ hnR]
      exact hmnR
    have hBn : 0 < B n := by
      exact hpos n (le_trans hNposle hn)
    have hBm : 0 < B m := by
      exact hpos m (le_trans hNposle hm)
    have hratioInv : (B n / B m)⁻¹ = B m / B n := by
      field_simp [hBn.ne', hBm.ne']
    have hpowinv (r : ℝ) : ((n : ℝ) / m) ^ r = (((m : ℝ) / n) ^ r)⁻¹ := by
      rw [← Real.inv_rpow hx.le, inv_div]
    have hinvLower := hordered.2
    rw [hpowinv (1 / θ - ε')] at hinvLower
    have hratioUpper : B m / B n ≤ A * ((m : ℝ) / n) ^ (1 / θ - ε') := by
      have hLpos : 0 < A⁻¹ * (((m : ℝ) / n) ^ (1 / θ - ε'))⁻¹ := by positivity
      have hRpos : 0 < B n / B m := div_pos hBn hBm
      have hinv := (inv_le_inv₀ hRpos hLpos).2 hinvLower
      calc
        B m / B n = (B n / B m)⁻¹ := hratioInv.symm
        _ ≤ (A⁻¹ * (((m : ℝ) / n) ^ (1 / θ - ε'))⁻¹)⁻¹ := hinv
        _ = A * ((m : ℝ) / n) ^ (1 / θ - ε') := by
          field_simp [hA.ne', (Real.rpow_pos_of_pos hx _).ne']
    have hratioLeMax : ((m : ℝ) / n) ^ (1 / θ - ε') ≤
        max (((m : ℝ) / n) ^ (1 / θ + ε')) (((m : ℝ) / n) ^ (1 / θ - ε')) :=
      le_max_right _ _
    exact hratioUpper.trans (mul_le_mul_of_nonneg_left hratioLeMax (by linarith))

/-- Potter-type lower bound: same hypotheses, `B m / B n ≥ A⁻¹ * min (…) (…)`. -/
theorem IsRealStableAttracted.potter_lower {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) {ε' A : ℝ} (hε' : 0 < ε') (hA : 1 < A) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ m ≥ N,
      A⁻¹ * min (((m : ℝ) / n) ^ (1 / θ + ε')) (((m : ℝ) / n) ^ (1 / θ - ε')) ≤ B m / B n := by
  obtain ⟨N₀, hN₀⟩ := exists_ordered_potter_bounds h hε' hA
  obtain ⟨Npos, hpos⟩ := Filter.eventually_atTop.1 h.pos
  let N := max 1 (max N₀ Npos)
  have hN₀le : N₀ ≤ N := le_trans (le_max_left _ _) (le_max_right _ _)
  have hNposle : Npos ≤ N := le_trans (le_max_right _ _) (le_max_right _ _)
  have hNgeone : 1 ≤ N := le_max_left _ _
  refine ⟨N, fun n hn m hm => ?_⟩
  rcases le_total n m with hnm | hmn
  · obtain ⟨_, hl⟩ := hN₀ n (le_trans hN₀le hn) m hnm
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) (by positivity)).trans hl
  · have hordered := hN₀ m (le_trans hN₀le hm) n hmn
    have hθpos : 0 < θ := by linarith [h.index_mem.1]
    have hx : 0 < (m : ℝ) / n := by
      have hmpos : 0 < m := lt_of_lt_of_le (by norm_num) (le_trans hNgeone hm)
      have hnpos : 0 < n := lt_of_lt_of_le (by norm_num) (le_trans hNgeone hn)
      exact div_pos (by exact_mod_cast hmpos) (by exact_mod_cast hnpos)
    have hxle : (m : ℝ) / n ≤ 1 := by
      have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
      have hnR : 0 < (n : ℝ) := by
        exact_mod_cast (lt_of_lt_of_le (by norm_num) (le_trans hNgeone hn))
      rw [div_le_one₀ hnR]
      exact hmnR
    have hBn : 0 < B n := by
      exact hpos n (le_trans hNposle hn)
    have hBm : 0 < B m := by
      exact hpos m (le_trans hNposle hm)
    have hratioInv : (B n / B m)⁻¹ = B m / B n := by
      field_simp [hBn.ne', hBm.ne']
    have hpowinv (r : ℝ) : ((n : ℝ) / m) ^ r = (((m : ℝ) / n) ^ r)⁻¹ := by
      rw [← Real.inv_rpow hx.le, inv_div]
    have hupper := hordered.1
    rw [hpowinv (1 / θ + ε')] at hupper
    have hratioLower : A⁻¹ * ((m : ℝ) / n) ^ (1 / θ + ε') ≤ B m / B n := by
      have hLpos : 0 < A * (((m : ℝ) / n) ^ (1 / θ + ε'))⁻¹ := by positivity
      have hRpos : 0 < B n / B m := div_pos hBn hBm
      have hinv := (inv_le_inv₀ hLpos hRpos).2 hupper
      calc
        A⁻¹ * ((m : ℝ) / n) ^ (1 / θ + ε') =
            (A * (((m : ℝ) / n) ^ (1 / θ + ε'))⁻¹)⁻¹ := by
          field_simp [hA.ne', (Real.rpow_pos_of_pos hx _).ne']
        _ ≤ (B n / B m)⁻¹ := hinv
        _ = B m / B n := hratioInv
    have hminLe : min (((m : ℝ) / n) ^ (1 / θ + ε'))
        (((m : ℝ) / n) ^ (1 / θ - ε')) ≤ ((m : ℝ) / n) ^ (1 / θ + ε') :=
      min_le_left _ _
    exact (mul_le_mul_of_nonneg_left hminLe (by positivity)).trans hratioLower

/-- Uniformly small ratios for small positive indices (Node 5), in absolute value: finitely many
indices with nonpositive normalizer values are absorbed by the divergence of `B n`. -/
theorem IsRealStableAttracted.small_index_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (h : IsRealStableAttracted ν θ B) :
    ∀ ε > 0, ∃ δ > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ δ * n + 2 → |B m / B n| ≤ ε := by
  intro ε hε
  have hθpos : 0 < θ := by linarith [h.index_mem.1]
  have hρpos : 0 < 1 / θ := one_div_pos.mpr hθpos
  let β : ℝ := (1 / θ) / 2
  have hβpos : 0 < β := by dsimp [β]; exact half_pos hρpos
  have hcontPow : ContinuousAt (fun x : ℝ => (2 : ℝ) * (2 * x) ^ β) 0 := by
    have hlin : ContinuousAt (fun x : ℝ => (2 : ℝ) * x) 0 :=
      continuousAt_const.mul continuousAt_id
    have hpow : ContinuousAt (fun y : ℝ => y ^ β) 0 :=
      Real.continuousAt_rpow_const (0 : ℝ) β (Or.inr hβpos.le)
    have hpowComp : ContinuousAt (fun x : ℝ => ((2 : ℝ) * x) ^ β) 0 := by
      change ContinuousAt ((fun y : ℝ => y ^ β) ∘ fun x : ℝ => (2 : ℝ) * x) 0
      exact hpow.comp_of_eq hlin (by simp : (fun x : ℝ => (2 : ℝ) * x) 0 = (0 : ℝ))
    exact continuousAt_const.mul hpowComp
  let f : ℝ → ℝ := fun x => 2 * (2 * x) ^ β
  have hf0 : f 0 < ε := by
    simp [f, Real.zero_rpow hβpos.ne']
    exact hε
  have hnear : ∀ᶠ x : ℝ in 𝓝 0, f x < ε := by
    simpa only [f] using hcontPow.eventually (Iio_mem_nhds hf0)
  obtain ⟨r, hrpos, hr⟩ := Metric.eventually_nhds_iff_ball.mp hnear
  let δ : ℝ := min (r / 2) (1 / 8)
  have hδpos : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (by norm_num)
  have hδle : δ ≤ 1 / 8 := by
    dsimp [δ]
    exact min_le_right _ _
  have hδltR : δ < r := by
    dsimp [δ]
    exact (min_le_left _ _).trans_lt (by linarith)
  have hδball : δ ∈ Metric.ball 0 r := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδpos]
    exact hδltR
  have hδf : f δ < ε := hr δ hδball
  obtain ⟨Np, hP⟩ := h.potter_upper (ε' := β) (A := 2) hβpos (by norm_num)
  obtain ⟨Npos, hpos⟩ := Filter.eventually_atTop.1 h.pos
  let M := max Np Npos
  obtain ⟨Nf, hF⟩ := eventually_abs_ratio_lt_finite h.tendsto_norming_atTop M hε
  have hdiv : Tendsto (fun n : ℕ => (2 : ℝ) / n) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_const_nhds.mul (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)))
  obtain ⟨Ndiv, hNdiv⟩ := Filter.eventually_atTop.1
    (hdiv.eventually (Iio_mem_nhds hδpos))
  let N := max 1 (max Np (max Nf (max Npos Ndiv)))
  have hNgeone : 1 ≤ N := le_max_left _ _
  have hNple : Np ≤ N := by
    dsimp [N]
    exact le_trans (le_max_left Np (max Nf (max Npos Ndiv))) (le_max_right 1 _)
  have hNfle : Nf ≤ N := by
    dsimp [N]
    exact le_trans (le_trans (le_max_left Nf (max Npos Ndiv))
      (le_max_right Np _)) (le_max_right 1 _)
  have hNposle : Npos ≤ N := by
    dsimp [N]
    exact le_trans (le_trans (le_max_left Npos Ndiv)
      (le_trans (le_max_right Nf _) (le_max_right Np _))) (le_max_right 1 _)
  have hNdivle : Ndiv ≤ N := by
    dsimp [N]
    exact le_trans (le_trans (le_max_right Npos Ndiv)
      (le_trans (le_max_right Nf _) (le_max_right Np _))) (le_max_right 1 _)
  refine ⟨δ, hδpos, N, fun n hn m hm1 hmBound => ?_⟩
  by_cases hmSmall : m < M
  · exact (hF n (le_trans hNfle hn) m hmSmall).le
  · have hmM : M ≤ m := le_of_not_gt hmSmall
    have hmP : Np ≤ m := le_trans (le_max_left Np Npos) hmM
    have hmNpos : Npos ≤ m := le_trans (le_max_right Np Npos) hmM
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) (le_trans hNgeone hn))
    have hmR : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm1)
    have hx : 0 < (m : ℝ) / n := div_pos hmR hnR
    have htwoDiv : (2 : ℝ) / n < δ := hNdiv n (le_trans hNdivle hn)
    have hxle : (m : ℝ) / n ≤ δ + (2 : ℝ) / n := by
      apply (div_le_iff₀ hnR).2
      calc
        (m : ℝ) ≤ δ * n + 2 := hmBound
        _ = (δ + (2 : ℝ) / n) * n := by
          field_simp [hnR.ne']
    have hxsmall : (m : ℝ) / n ≤ 2 * δ := by linarith
    have hzpos : 0 < 2 * δ := by positivity
    have hzone : 2 * δ ≤ 1 := by nlinarith [hδle]
    have hplus : 1 / θ + β = 3 * β := by dsimp [β]; ring
    have hminus : 1 / θ - β = β := by dsimp [β]; ring
    have hpowPlus : ((m : ℝ) / n) ^ (1 / θ + β) ≤ (2 * δ) ^ β := by
      rw [hplus]
      calc
        ((m : ℝ) / n) ^ (3 * β) ≤ (2 * δ) ^ (3 * β) :=
          Real.rpow_le_rpow hx.le hxsmall (by positivity)
        _ ≤ (2 * δ) ^ β :=
          Real.rpow_le_rpow_of_exponent_ge hzpos hzone (by nlinarith)
    have hpowMinus : ((m : ℝ) / n) ^ (1 / θ - β) ≤ (2 * δ) ^ β := by
      rw [hminus]
      exact Real.rpow_le_rpow hx.le hxsmall (by positivity)
    have hmax : max (((m : ℝ) / n) ^ (1 / θ + β))
        (((m : ℝ) / n) ^ (1 / θ - β)) ≤ (2 * δ) ^ β := max_le hpowPlus hpowMinus
    have hratio := (hP n (le_trans hNple hn) m hmP).trans
      (mul_le_mul_of_nonneg_left hmax (by norm_num))
    have hratioPos : 0 < B m / B n :=
      div_pos (hpos m hmNpos) (hpos n (le_trans hNposle hn))
    rw [abs_of_pos hratioPos]
    exact (hratio.trans_lt (by simpa [f] using hδf)).le

/-- Bounded ratios on finite time windows (Node 5), in absolute value. -/
theorem IsRealStableAttracted.bounded_index_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) (A : ℝ) :
    ∃ C > 0, ∃ N : ℕ, ∀ n ≥ N, ∀ m : ℕ,
      1 ≤ m → (m : ℝ) ≤ A * n + 2 → |B m / B n| ≤ C := by
  have hθpos : 0 < θ := by linarith [h.index_mem.1]
  have hρpos : 0 < 1 / θ := one_div_pos.mpr hθpos
  let β : ℝ := (1 / θ) / 2
  have hβpos : 0 < β := by dsimp [β]; exact half_pos hρpos
  have hplus : 1 / θ + β = 3 * β := by dsimp [β]; ring
  have hminus : 1 / θ - β = β := by dsimp [β]; ring
  obtain ⟨Np, hP⟩ := h.potter_upper (ε' := β) (A := 2) hβpos (by norm_num)
  obtain ⟨Npos, hpos⟩ := Filter.eventually_atTop.1 h.pos
  let M := max Np Npos
  obtain ⟨Nf, hF⟩ := eventually_abs_ratio_lt_finite h.tendsto_norming_atTop M
    (ε := 1) (by norm_num)
  let K : ℝ := max 1 (A + 2)
  have hKone : 1 ≤ K := by dsimp [K]; exact le_max_left _ _
  let C : ℝ := 2 * K ^ (3 * β) + 1
  have hCpos : 0 < C := by dsimp [C]; positivity
  let N := max 1 (max Np (max Nf Npos))
  have hNgeone : 1 ≤ N := le_max_left _ _
  have hNple : Np ≤ N := by
    dsimp [N]
    exact le_trans (le_max_left Np (max Nf Npos)) (le_max_right 1 _)
  have hNfle : Nf ≤ N := by
    dsimp [N]
    exact le_trans (le_trans (le_max_left Nf Npos) (le_max_right Np _)) (le_max_right 1 _)
  have hNposle : Npos ≤ N := by
    dsimp [N]
    exact le_trans (le_max_right Nf Npos) (le_trans (le_max_right Np _) (le_max_right 1 _))
  refine ⟨C, hCpos, N, fun n hn m hm1 hmBound => ?_⟩
  by_cases hmSmall : m < M
  · have hfinite := hF n (le_trans hNfle hn) m hmSmall
    have h1C : 1 ≤ C := by
      have hpowNonneg : 0 ≤ K ^ (3 * β) := Real.rpow_nonneg (by linarith [hKone]) _
      dsimp [C]
      nlinarith [hpowNonneg]
    dsimp [C]
    exact hfinite.le.trans h1C
  · have hmM : M ≤ m := le_of_not_gt hmSmall
    have hmP : Np ≤ m := le_trans (le_max_left Np Npos) hmM
    have hmNpos : Npos ≤ m := le_trans (le_max_right Np Npos) hmM
    have hnR : 0 < (n : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num) (le_trans hNgeone hn))
    have hmR : 0 < (m : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hm1)
    have hx : 0 < (m : ℝ) / n := div_pos hmR hnR
    have hxleA : (m : ℝ) / n ≤ A + (2 : ℝ) / n := by
      apply (div_le_iff₀ hnR).2
      calc
        (m : ℝ) ≤ A * n + 2 := hmBound
        _ = (A + (2 : ℝ) / n) * n := by field_simp [hnR.ne']
    have htwoDiv : (2 : ℝ) / n ≤ 2 := by
      rw [div_le_iff₀ hnR]
      have hnRone : 1 ≤ (n : ℝ) := by exact_mod_cast (le_trans hNgeone hn)
      nlinarith
    have hxK : (m : ℝ) / n ≤ K := by
      have hAdiv : A + (2 : ℝ) / n ≤ A + 2 := by linarith [htwoDiv]
      have hAK : A + 2 ≤ K := by dsimp [K]; exact le_max_right _ _
      exact hxleA.trans (hAdiv.trans hAK)
    have hpowPlus : ((m : ℝ) / n) ^ (1 / θ + β) ≤ K ^ (3 * β) := by
      rw [hplus]
      exact Real.rpow_le_rpow hx.le hxK (by positivity)
    have hpowMinus : ((m : ℝ) / n) ^ (1 / θ - β) ≤ K ^ (3 * β) := by
      rw [hminus]
      calc
        ((m : ℝ) / n) ^ β ≤ K ^ β := Real.rpow_le_rpow hx.le hxK hβpos.le
        _ ≤ K ^ (3 * β) :=
          Real.rpow_le_rpow_of_exponent_le hKone (by nlinarith)
    have hmax : max (((m : ℝ) / n) ^ (1 / θ + β))
        (((m : ℝ) / n) ^ (1 / θ - β)) ≤ K ^ (3 * β) := max_le hpowPlus hpowMinus
    have hratio := (hP n (le_trans hNple hn) m hmP).trans
      (mul_le_mul_of_nonneg_left hmax (by norm_num))
    have hratioPos : 0 < B m / B n := div_pos (hpos m hmNpos) (hpos n (le_trans hNposle hn))
    rw [abs_of_pos hratioPos]
    dsimp [C]
    linarith

end BGW.StableTrees
