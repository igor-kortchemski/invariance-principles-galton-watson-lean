/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SurvivalScale
import BGW.StableTrees.CriticalSupport
import Mathlib.Algebra.Order.Ring.Abs

/-!
# The offspring defect at zero

The function `u ↦ g(1-u)-(1-u)` is the decrement in the survival recursion.  This module
establishes its elementary positivity and monotonicity properties.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace BGW.StableTrees.Survival

/-- The defect of the offspring generating function at `1-u`. -/
noncomputable def offspringDefect (μ : PMF ℕ) (u : ℝ) : ℝ := realGF μ (1 - u) - (1 - u)

private theorem summable_mean_weight (μ : PMF ℕ) (hc : IsCritical μ) :
    Summable (fun k : ℕ => (k : ℝ) * (μ k).toReal) := by
  have hs : (∑' k : ℕ, (k : ℝ≥0∞) * μ k) ≠ ∞ := by rw [hc]; exact ENNReal.one_ne_top
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast] using
    (ENNReal.summable_toReal hs)

private theorem tsum_mean_weight (μ : PMF ℕ) (hc : IsCritical μ) :
    (∑' k : ℕ, (k : ℝ) * (μ k).toReal) = 1 := by
  have h := (ENNReal.tsum_toReal_eq (f := fun k : ℕ => (k : ℝ≥0∞) * μ k)
    (fun k => ENNReal.mul_ne_top (by simp) (μ.apply_ne_top k))).symm
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast] at h
  rw [hc] at h
  simpa using h

private theorem summable_pmf_weight (μ : PMF ℕ) : Summable (fun k : ℕ => (μ k).toReal) := by
  apply ENNReal.summable_toReal
  exact PMF.tsum_coe_ne_top μ

private theorem tsum_pmf_weight (μ : PMF ℕ) : (∑' k : ℕ, (μ k).toReal) = 1 := by
  calc
    _ = (∑' k : ℕ, μ k).toReal := (ENNReal.tsum_toReal_eq (fun k => μ.apply_ne_top k)).symm
    _ = 1 := by rw [PMF.tsum_coe]; simp

/-- Criticality expresses the defect as a sum of nonnegative Bernoulli remainders. -/
theorem offspringDefect_eq_tsum (μ : PMF ℕ) (hc : IsCritical μ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    offspringDefect μ u = ∑' k : ℕ, (μ k).toReal * ((1 - u) ^ k - 1 + k * u) := by
  have hp := summable_pmf_weight μ
  have hm := summable_mean_weight μ hc
  have hreal : Summable (fun k : ℕ => (μ k).toReal * (1 - u) ^ k) := by
    apply Summable.of_nonneg_of_le _ _ hp
    · intro k
      exact mul_nonneg ENNReal.toReal_nonneg (pow_nonneg (by linarith) k)
    · intro k
      simpa using mul_le_mul_of_nonneg_left (pow_le_one₀ (by linarith) (by linarith))
        ENNReal.toReal_nonneg
  have hmu : Summable (fun k : ℕ => (μ k).toReal * (k * u)) := by
    apply Summable.congr (hm.mul_right u)
    intro k
    ring
  have hmu_tsum : (∑' k : ℕ, (μ k).toReal * (k * u)) = u := by
    have he : (fun k : ℕ => (μ k).toReal * (k * u)) =
        (fun k : ℕ => ((k : ℝ) * (μ k).toReal) * u) := by
      funext k
      ring
    rw [he, tsum_mul_right, tsum_mean_weight μ hc]
    simp
  have hrem := hreal.sub hp
  symm
  calc
    (∑' k : ℕ, (μ k).toReal * ((1 - u) ^ k - 1 + k * u)) =
        ∑' k : ℕ, (((μ k).toReal * (1 - u) ^ k - (μ k).toReal) +
          (μ k).toReal * (k * u)) := by
      apply tsum_congr
      intro k
      ring
    _ = (∑' k : ℕ, ((μ k).toReal * (1 - u) ^ k - (μ k).toReal)) +
        ∑' k : ℕ, (μ k).toReal * (k * u) := (hrem.hasSum.add hmu.hasSum).tsum_eq
    _ = realGF μ (1 - u) - 1 + u := by
      rw [(hreal.hasSum.sub hp.hasSum).tsum_eq, hmu_tsum, tsum_pmf_weight]
      rfl
    _ = offspringDefect μ u := by dsimp [offspringDefect]; ring

private theorem summable_defect_terms (μ : PMF ℕ) (hc : IsCritical μ) {u : ℝ}
    (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    Summable (fun k : ℕ => (μ k).toReal * ((1 - u) ^ k - 1 + k * u)) := by
  apply Summable.of_nonneg_of_le _ _ ((summable_mean_weight μ hc).mul_left 2)
  · intro k
    have hpow := one_add_mul_sub_le_pow (a := 1 - u) (by linarith) k
    have hterm : 0 ≤ (1 - u) ^ k - 1 + k * u := by
      convert sub_nonneg.mpr hpow using 1; ring
    exact mul_nonneg ENNReal.toReal_nonneg hterm
  · intro k
    have hab : |(1 - u) - 1| = u := by
      rw [show (1 - u) - 1 = -u by ring, abs_neg, abs_of_nonneg hu0]
    have hmax : max |(1 - u)| |(1 : ℝ)| ≤ 1 := by
      rw [abs_of_nonneg (sub_nonneg.mpr hu1), abs_one]
      exact max_le (by linarith) le_rfl
    have hp := abs_pow_sub_pow_le (n := k) (a := 1 - u) (b := (1 : ℝ))
    have hterm : (1 - u) ^ k - 1 + k * u ≤ 2 * (k * u) := by
      have hpm : max |(1 - u)| |(1 : ℝ)| ^ (k - 1) ≤ 1 :=
        pow_le_one₀ (by positivity) hmax
      have hk : (1 - u) ^ k - 1 ≤ k * u := by
        calc
          (1 - u) ^ k - 1 ≤ |(1 - u) ^ k - 1| := le_abs_self _
          _ ≤ |(1 - u) - 1| * k * max |(1 - u)| |(1 : ℝ)| ^ (k - 1) := by
            simpa using hp
          _ ≤ u * k * 1 := by rw [hab]; gcongr
          _ = k * u := by ring
      have hku : 0 ≤ (k : ℝ) * u := mul_nonneg (Nat.cast_nonneg k) hu0
      linarith
    calc
      (μ k).toReal * ((1 - u) ^ k - 1 + k * u) ≤ (μ k).toReal * (2 * (k * u)) :=
        mul_le_mul_of_nonneg_left hterm ENNReal.toReal_nonneg
      _ ≤ 2 * ((k : ℝ) * (μ k).toReal) := by
        have hk : (k : ℝ) * u ≤ k := mul_le_of_le_one_right (Nat.cast_nonneg k) hu1
        nlinarith [ENNReal.toReal_nonneg (a := μ k)]

/-- The offspring defect is nonnegative on `[0,1]`. -/
theorem offspringDefect_nonneg {μ : PMF ℕ} (hc : IsCritical μ) {u : ℝ}
    (_hu0 : 0 ≤ u) (hu1 : u ≤ 1) : 0 ≤ offspringDefect μ u := by
  rw [offspringDefect_eq_tsum μ hc _hu0 hu1]
  apply tsum_nonneg
  intro k
  have hpow := one_add_mul_sub_le_pow (a := 1 - u) (by linarith) k
  apply mul_nonneg ENNReal.toReal_nonneg
  convert sub_nonneg.mpr hpow using 1; ring

/-- The offspring defect is nondecreasing on `[0,1]`. -/
theorem offspringDefect_monotoneOn {μ : PMF ℕ} (hc : IsCritical μ) :
    MonotoneOn (offspringDefect μ) (Set.Icc 0 1) := by
  intro u hu v hv huv
  rw [offspringDefect_eq_tsum μ hc hu.1 hu.2,
    offspringDefect_eq_tsum μ hc hv.1 hv.2]
  apply (summable_defect_terms μ hc hu.1 hu.2).tsum_le_tsum _
    (summable_defect_terms μ hc hv.1 hv.2)
  intro k
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  have ha0 : 0 ≤ 1 - v := sub_nonneg.mpr hv.2
  have hb0 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2
  have hmax : max |(1 - u)| |(1 - v)| ≤ 1 := by
    rw [abs_of_nonneg hb0, abs_of_nonneg ha0]
    exact max_le (by linarith [hu.1]) (by linarith [hv.1])
  have hp := abs_pow_sub_pow_le (n := k) (a := 1 - u) (b := 1 - v)
  have hd : (1 - u) ^ k - (1 - v) ^ k ≤ k * (v - u) := by
    calc
      (1 - u) ^ k - (1 - v) ^ k ≤ |(1 - u) ^ k - (1 - v) ^ k| := le_abs_self _
      _ ≤ |(1 - u) - (1 - v)| * k * max |(1 - u)| |(1 - v)| ^ (k - 1) := hp
      _ ≤ (v - u) * k * 1 := by
        have he : |(1 - u) - (1 - v)| = v - u := by
          rw [show (1 - u) - (1 - v) = v - u by ring, abs_of_nonneg (sub_nonneg.mpr huv)]
        rw [he]
        have hpm : max |(1 - u)| |(1 - v)| ^ (k - 1) ≤ 1 :=
          pow_le_one₀ (by positivity) hmax
        gcongr
      _ = k * (v - u) := by ring
  linarith

private theorem strict_bernoulli {u : ℝ} (hu0 : 0 < u) (hu1 : u ≤ 1) :
    ∀ k : ℕ, 1 + ((k + 2 : ℕ) : ℝ) * (-u) < (1 - u) ^ (k + 2)
  | 0 => by
    push_cast
    nlinarith [sq_pos_of_pos hu0]
  | k + 1 => by
    have ih := strict_bernoulli hu0 hu1 k
    have hx0 : 0 ≤ 1 - u := sub_nonneg.mpr hu1
    have hx1 : 1 - u < 1 := by linarith
    rw [pow_succ]
    calc
      (1 - u) ^ (k + 2) * (1 - u) ≥ (1 + ((k + 2 : ℕ) : ℝ) * (-u)) * (1 - u) :=
        mul_le_mul_of_nonneg_right ih.le hx0
      _ > 1 + ((k + 1 + 2 : ℕ) : ℝ) * (-u) := by
        push_cast
        nlinarith [sq_pos_of_pos hu0]

/-- The offspring defect is strictly positive away from zero under critical nondegeneracy. -/
theorem offspringDefect_pos {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {u : ℝ}
    (hu0 : 0 < u) (hu1 : u ≤ 1) : 0 < offspringDefect μ u := by
  obtain ⟨j, hj2, hj⟩ := hc.exists_two_le_ne_zero hne
  rw [offspringDefect_eq_tsum μ hc hu0.le hu1]
  refine (summable_defect_terms μ hc hu0.le hu1).tsum_pos (fun k => ?_) j ?_
  · have hpow := one_add_mul_sub_le_pow (a := 1 - u) (by linarith) k
    apply mul_nonneg ENNReal.toReal_nonneg
    convert sub_nonneg.mpr hpow using 1; ring
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hj2
    have hp := strict_bernoulli hu0 hu1 m
    have hterm : 0 < (1 - u) ^ (m + 2) - 1 + (m + 2 : ℕ) * u := by
      convert sub_pos.mpr hp using 1; ring
    simpa [Nat.add_comm] using mul_pos (ENNReal.toReal_pos hj (μ.apply_ne_top _)) hterm

/-- The offspring defect vanishes at zero. -/
@[simp] theorem offspringDefect_zero (μ : PMF ℕ) : offspringDefect μ 0 = 0 := by
  simp only [offspringDefect, sub_zero, realGF, one_pow, mul_one, sub_eq_zero]
  exact tsum_pmf_weight μ

private theorem eventually_reciprocal_find_properties {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {u : ℕ → ℝ} (hu : ∀ᶠ n in atTop, 0 < u n)
    (hu0 : Tendsto u atTop (𝓝[>] 0)) :
    ∃ m : ℕ → ℕ, Tendsto m atTop atTop ∧ (∀ᶠ n in atTop, 1 ≤ m n) ∧
      (∀ᶠ n in atTop, 1 / B (m n) ≤ u n) ∧ (∀ᶠ n in atTop, u n ≤ 1 / B (m n - 1)) := by
  have hinv : Tendsto (fun n => 1 / u n) atTop atTop := by
    exact hu0.inv_tendsto_nhdsGT_zero.congr (fun n => by simp only [Pi.inv_apply, one_div])
  have hex (n : ℕ) : ∃ j : ℕ, 1 / u n < B j :=
    ((tendsto_B_atTop h).eventually_gt_atTop (1 / u n)).exists
  let m : ℕ → ℕ := fun n => Nat.find (hex n)
  have hspec (n : ℕ) : 1 / u n < B (m n) := Nat.find_spec (hex n)
  have hm : Tendsto m atTop atTop := by
    rw [tendsto_atTop_atTop]
    intro b
    let M : ℕ := b + 1
    apply eventually_atTop.1
    filter_upwards [hinv.eventually_gt_atTop (max (B M) 0), hu] with n hn hun
    have hnot : ¬m n < M := by
      intro hlt
      have hle : m n ≤ M := hlt.le
      have hB : B (m n) ≤ B M := h.monotone hle
      have hspec' := hspec n
      linarith [le_max_left (B M) 0, le_max_right (B M) 0]
    have hMr : b ≤ M := Nat.le_add_right b 1
    exact hMr.trans (le_of_not_gt hnot)
  have hm1 : ∀ᶠ n in atTop, 1 ≤ m n := hm.eventually_ge_atTop 1
  have hlo : ∀ᶠ n in atTop, 1 / B (m n) ≤ u n := by
    filter_upwards [hu, hm.eventually_ge_atTop 2] with n hun hmn
    have hB : 0 < B (m n) := h.pos (m n) (by omega)
    exact (one_div_le hB hun).mpr (hspec n).le
  have hhi : ∀ᶠ n in atTop, u n ≤ 1 / B (m n - 1) := by
    filter_upwards [hu, hm.eventually_ge_atTop 2] with n hun hmn
    have hnot := Nat.find_min (hex n) (show m n - 1 < m n by omega)
    have hle : B (m n - 1) ≤ 1 / u n := le_of_not_gt hnot
    have hB : 0 < B (m n - 1) := h.pos (m n - 1) (by omega)
    have hs := (le_div_iff₀ hun).mp hle
    exact (le_div_iff₀ hB).mpr (by nlinarith)
  exact ⟨m, hm, hm1, hlo, hhi⟩

private theorem tendsto_inv_natFloor_succ {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => ((m n : ℝ) - 1) / m n) atTop (𝓝 1) := by
  have hmR : Tendsto (fun n => (m n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hm
  have hz := tendsto_inv_atTop_zero.comp hmR
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hz
  simp only [sub_zero] at ht
  apply ht.congr'
  filter_upwards [hmR.eventually_gt_atTop 0] with n hn
  change (1 - (m n : ℝ)⁻¹) = ((m n : ℝ) - 1) / (m n : ℝ)
  field_simp

private theorem tendsto_natCast_div_pred {m : ℕ → ℕ} (hm : Tendsto m atTop atTop) :
    Tendsto (fun n => (m n : ℝ) / ((m n : ℝ) - 1)) atTop (𝓝 1) := by
  have hm' : Tendsto (fun n => m n - 1) atTop atTop := (tendsto_sub_atTop_nat 1).comp hm
  have hmR : Tendsto (fun n => ((m n - 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hm'
  have hz := tendsto_inv_atTop_zero.comp hmR
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).add hz
  simp only [add_zero] at ht
  apply ht.congr'
  filter_upwards [hm.eventually_gt_atTop 2] with n hn
  have hnn : m n - 1 + 1 = m n := by omega
  have hpos : (0 : ℝ) < ((m n - 1 : ℕ) : ℝ) := by exact_mod_cast (show 0 < m n - 1 by omega)
  rw [← hnn]
  push_cast
  rw [add_sub_cancel_right]
  dsimp only [Function.comp_def, one_div]
  field_simp [hpos.ne']

/-- The offspring defect is regularly varying at zero, along every sequence tending to zero. -/
theorem tendsto_offspringDefect_ratio {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {c : ℝ} (hc : 0 < c) {u : ℕ → ℝ}
    (hu : ∀ᶠ n in atTop, 0 < u n) (hu0 : Tendsto u atTop (𝓝[>] 0)) :
    Tendsto (fun n => offspringDefect μ (c * u n) / offspringDefect μ (u n)) atTop
      (𝓝 (c ^ θ)) := by
  obtain ⟨m, hm, hm1, hlo, hhi⟩ := eventually_reciprocal_find_properties h hu hu0
  have hm' : Tendsto (fun n => m n - 1) atTop atTop := (tendsto_sub_atTop_nat 1).comp hm
  have hnorm (d : ℝ) (hd : 0 < d) : Tendsto (fun n => (m n : ℝ) *
      offspringDefect μ (d / B (m n))) atTop (𝓝 (d ^ θ)) := by
    apply (tendsto_realGF_expansion h hd).comp hm |>.congr
    intro n
    dsimp only [Function.comp_def]
    rw [offspringDefect]
  have hnorm' (d : ℝ) (hd : 0 < d) : Tendsto (fun n => ((m n - 1 : ℕ) : ℝ) *
      offspringDefect μ (d / B (m n - 1))) atTop (𝓝 (d ^ θ)) := by
    apply (tendsto_realGF_expansion h hd).comp hm' |>.congr
    intro n
    dsimp only [Function.comp_def]
    rw [offspringDefect]
  have hmratio : Tendsto (fun n => ((m n : ℝ) - 1) / m n) atTop (𝓝 1) :=
    tendsto_inv_natFloor_succ hm
  have hmratio' : Tendsto (fun n => (m n : ℝ) / ((m n : ℝ) - 1)) atTop (𝓝 1) :=
    tendsto_natCast_div_pred hm
  have hleft := ((hnorm c hc).div (hnorm' 1 one_pos) (by simp : (1 : ℝ) ^ θ ≠ 0)).mul
    hmratio
  have hright := ((hnorm' c hc).div (hnorm 1 one_pos) (by simp : (1 : ℝ) ^ θ ≠ 0)).mul
    hmratio'
  simp only [Real.one_rpow, div_one, mul_one] at hleft hright
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hleft hright
  · filter_upwards [hm.eventually_ge_atTop 2, hlo, hhi,
      ((tendsto_B_atTop h).comp hm).eventually_gt_atTop (max 1 c),
      ((tendsto_B_atTop h).comp hm').eventually_gt_atTop (max 1 c), hu] with
      n hmn hlon hhin hBm hBp hun
    have hBm' : 0 < B (m n) := h.pos (m n) (by omega)
    have hBp' : 0 < B (m n - 1) := h.pos (m n - 1) (by omega)
    have h1Bm : 0 < 1 / B (m n) := one_div_pos.mpr hBm'
    have h1Bp : 0 < 1 / B (m n - 1) := one_div_pos.mpr hBp'
    have h1Bmle : 1 / B (m n) ≤ 1 := by
      have h1 : (1 : ℝ) ≤ B (m n) := (le_max_left _ _).trans hBm.le
      exact (div_le_iff₀ hBm').mpr (by simpa using h1)
    have h1Bple : 1 / B (m n - 1) ≤ 1 := by
      have h1 : (1 : ℝ) ≤ B (m n - 1) := (le_max_left _ _).trans hBp.le
      exact (div_le_iff₀ hBp').mpr (by simpa using h1)
    have hcBmle : c / B (m n) ≤ 1 := by
      have h1 : c ≤ B (m n) := (le_max_right _ _).trans hBm.le
      exact (div_le_iff₀ hBm').mpr (by simpa using h1)
    have hcBple : c / B (m n - 1) ≤ 1 := by
      have h1 : c ≤ B (m n - 1) := (le_max_right _ _).trans hBp.le
      exact (div_le_iff₀ hBp').mpr (by simpa using h1)
    have hDpos : 0 < offspringDefect μ (1 / B (m n - 1)) :=
      offspringDefect_pos h.critical h.nondegenerate h1Bp h1Bple
    have hden : 0 < offspringDefect μ (u n) :=
      offspringDefect_pos h.critical h.nondegenerate hun (hhin.trans h1Bple)
    have hnumlo : offspringDefect μ (c / B (m n)) ≤ offspringDefect μ (c * u n) :=
      offspringDefect_monotoneOn h.critical
        ⟨div_nonneg hc.le hBm'.le, hcBmle⟩
        ⟨mul_nonneg hc.le hun.le, (show c * u n ≤ c / B (m n - 1) by
            convert mul_le_mul_of_nonneg_left hhin hc.le using 1; field_simp).trans hcBple⟩
        (by
          have hm := mul_le_mul_of_nonneg_left hlon hc.le
          convert hm using 1; field_simp)
    have hdlo : offspringDefect μ (1 / B (m n)) ≤ offspringDefect μ (u n) :=
      offspringDefect_monotoneOn h.critical ⟨h1Bm.le, h1Bmle⟩
        ⟨hun.le, hhin.trans h1Bple⟩ hlon
    have hnumhi : offspringDefect μ (c * u n) ≤ offspringDefect μ (c / B (m n - 1)) :=
      offspringDefect_monotoneOn h.critical
        ⟨mul_nonneg hc.le hun.le, (show c * u n ≤ c / B (m n - 1) by
            convert mul_le_mul_of_nonneg_left hhin hc.le using 1; field_simp).trans hcBple⟩
        ⟨div_nonneg hc.le hBp'.le, hcBple⟩
        (by
          have hm := mul_le_mul_of_nonneg_left hhin hc.le
          convert hm using 1; field_simp)
    have hdhi : offspringDefect μ (u n) ≤ offspringDefect μ (1 / B (m n - 1)) :=
      offspringDefect_monotoneOn h.critical ⟨hun.le, hhin.trans h1Bple⟩
        ⟨h1Bp.le, h1Bple⟩ hhin
    have hlefteq : ((fun n => (m n : ℝ) * offspringDefect μ (c / B (m n))) /
          (fun n => (m n - 1 : ℕ) * offspringDefect μ (1 / B (m n - 1)))) n *
          (((m n : ℝ) - 1) / m n) =
        offspringDefect μ (c / B (m n)) / offspringDefect μ (1 / B (m n - 1)) := by
      have hmpos : (0 : ℝ) < m n := by exact_mod_cast (show 0 < m n by omega)
      have hprev : ((m n - 1 : ℕ) : ℝ) = (m n : ℝ) - 1 := by
        have hm1 : 1 ≤ m n := by omega
        rw [Nat.cast_sub hm1, Nat.cast_one]
      dsimp only [Pi.div_apply]
      rw [hprev]
      have hm'pos : (0 : ℝ) < (m n : ℝ) - 1 := by
        have hm1 : (1 : ℝ) < m n := by exact_mod_cast (show 1 < m n by omega)
        linarith
      have hCpos : 0 < offspringDefect μ (c / B (m n)) :=
        offspringDefect_pos h.critical h.nondegenerate (by positivity) hcBmle
      have hCprev : 0 < offspringDefect μ (c / B (m n - 1)) :=
        offspringDefect_pos h.critical h.nondegenerate (by positivity) hcBple
      field_simp [hmpos.ne', hm'pos.ne', hDpos.ne', hCpos.ne', hCprev.ne']
    rw [hlefteq]
    exact div_le_div₀ (offspringDefect_nonneg h.critical (mul_nonneg hc.le hun.le)
      ((show c * u n ≤ c / B (m n - 1) by
        convert mul_le_mul_of_nonneg_left hhin hc.le using 1; field_simp).trans hcBple))
      hnumlo hden hdhi
  · filter_upwards [hm.eventually_ge_atTop 2, hlo, hhi,
      ((tendsto_B_atTop h).comp hm).eventually_gt_atTop (max 1 c),
      ((tendsto_B_atTop h).comp hm').eventually_gt_atTop (max 1 c), hu] with
      n hmn hlon hhin hBm hBp hun
    have hBm' : 0 < B (m n) := h.pos (m n) (by omega)
    have hBp' : 0 < B (m n - 1) := h.pos (m n - 1) (by omega)
    have h1Bm : 0 < 1 / B (m n) := one_div_pos.mpr hBm'
    have h1Bp : 0 < 1 / B (m n - 1) := one_div_pos.mpr hBp'
    have h1Bmle : 1 / B (m n) ≤ 1 := by
      have h1 : (1 : ℝ) ≤ B (m n) := (le_max_left _ _).trans hBm.le
      exact (div_le_iff₀ hBm').mpr (by simpa using h1)
    have h1Bple : 1 / B (m n - 1) ≤ 1 := by
      have h1 : (1 : ℝ) ≤ B (m n - 1) := (le_max_left _ _).trans hBp.le
      exact (div_le_iff₀ hBp').mpr (by simpa using h1)
    have hcBmle : c / B (m n) ≤ 1 := by
      have h1 : c ≤ B (m n) := (le_max_right _ _).trans hBm.le
      exact (div_le_iff₀ hBm').mpr (by simpa using h1)
    have hcBple : c / B (m n - 1) ≤ 1 := by
      have h1 : c ≤ B (m n - 1) := (le_max_right _ _).trans hBp.le
      exact (div_le_iff₀ hBp').mpr (by simpa using h1)
    have hDpos : 0 < offspringDefect μ (1 / B (m n)) :=
      offspringDefect_pos h.critical h.nondegenerate h1Bm h1Bmle
    have hden : 0 < offspringDefect μ (u n) :=
      offspringDefect_pos h.critical h.nondegenerate hun (hhin.trans h1Bple)
    have hnumlo : offspringDefect μ (c / B (m n)) ≤ offspringDefect μ (c * u n) :=
      offspringDefect_monotoneOn h.critical
        ⟨div_nonneg hc.le hBm'.le, hcBmle⟩
        ⟨mul_nonneg hc.le hun.le, (show c * u n ≤ c / B (m n - 1) by
            convert mul_le_mul_of_nonneg_left hhin hc.le using 1; field_simp).trans hcBple⟩
        (by
          have hm := mul_le_mul_of_nonneg_left hlon hc.le
          convert hm using 1; field_simp)
    have hdlo : offspringDefect μ (1 / B (m n)) ≤ offspringDefect μ (u n) :=
      offspringDefect_monotoneOn h.critical ⟨h1Bm.le, h1Bmle⟩
        ⟨hun.le, hhin.trans h1Bple⟩ hlon
    have hnumhi : offspringDefect μ (c * u n) ≤ offspringDefect μ (c / B (m n - 1)) :=
      offspringDefect_monotoneOn h.critical
        ⟨mul_nonneg hc.le hun.le, (show c * u n ≤ c / B (m n - 1) by
            convert mul_le_mul_of_nonneg_left hhin hc.le using 1; field_simp).trans hcBple⟩
        ⟨div_nonneg hc.le hBp'.le, hcBple⟩
        (by
          have hm := mul_le_mul_of_nonneg_left hhin hc.le
          convert hm using 1; field_simp)
    have hdhi : offspringDefect μ (u n) ≤ offspringDefect μ (1 / B (m n - 1)) :=
      offspringDefect_monotoneOn h.critical ⟨hun.le, hhin.trans h1Bple⟩
        ⟨h1Bp.le, h1Bple⟩ hhin
    have hrighteq : ((fun n => ((m n - 1 : ℕ) : ℝ) * offspringDefect μ (c / B (m n - 1))) /
          (fun n => (m n : ℝ) * offspringDefect μ (1 / B (m n)))) n *
          ((m n : ℝ) / ((m n : ℝ) - 1)) =
        offspringDefect μ (c / B (m n - 1)) / offspringDefect μ (1 / B (m n)) := by
      have hmpos : (0 : ℝ) < m n := by exact_mod_cast (show 0 < m n by omega)
      have hprev : ((m n - 1 : ℕ) : ℝ) = (m n : ℝ) - 1 := by
        have hm1 : 1 ≤ m n := by omega
        rw [Nat.cast_sub hm1, Nat.cast_one]
      dsimp only [Pi.div_apply]
      rw [hprev]
      have hm'pos : (0 : ℝ) < (m n : ℝ) - 1 := by
        have hm1 : (1 : ℝ) < m n := by exact_mod_cast (show 1 < m n by omega)
        linarith
      have hCpos : 0 < offspringDefect μ (c / B (m n)) :=
        offspringDefect_pos h.critical h.nondegenerate (by positivity) hcBmle
      have hCprev : 0 < offspringDefect μ (c / B (m n - 1)) :=
        offspringDefect_pos h.critical h.nondegenerate (by positivity) hcBple
      field_simp [hmpos.ne', hm'pos.ne', hDpos.ne', hCpos.ne', hCprev.ne']
    rw [hrighteq]
    exact div_le_div₀ (a := offspringDefect μ (c * u n))
      (b := offspringDefect μ (u n)) (c := offspringDefect μ (c / B (m n - 1)))
      (d := offspringDefect μ (1 / B (m n)))
      (offspringDefect_nonneg h.critical (div_nonneg hc.le hBp'.le) hcBple)
      hnumhi hDpos hdlo

end BGW.StableTrees.Survival
