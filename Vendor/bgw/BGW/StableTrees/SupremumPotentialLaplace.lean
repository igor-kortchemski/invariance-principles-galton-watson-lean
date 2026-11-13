/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Laplace integrals for the stable scale series

Gamma integrals and absolute summability justify termwise integration.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.StableTrees

private theorem integrable_series {μ : Measure ℝ} {F : ℕ → ℝ → ℝ}
    (hi : ∀ n, Integrable (F n) μ) (hs : ∀ᵐ x ∂μ, Summable (fun n => F n x))
    (hn : Summable (fun n => ∫ x, ‖F n x‖ ∂μ)) :
    Integrable (fun x => ∑' n, F n x) μ := by
  have hm (n : ℕ) : AEStronglyMeasurable (fun x => ∑ i ∈ Finset.range n, F i x) μ :=
    (Finset.range n).aestronglyMeasurable_fun_sum (fun i _ => (hi i).1)
  have ht : ∀ᵐ x ∂μ, Tendsto (fun n => ∑ i ∈ Finset.range n, F i x)
      atTop (𝓝 (∑' n, F n x)) := hs.mono (fun _ hx => hx.tendsto_sum_tsum_nat)
  have hmeas := aestronglyMeasurable_of_tendsto_ae _ hm ht
  have he (i : ℕ) : ∫⁻ x, ‖F i x‖ₑ ∂μ = ‖∫ x, ‖F i x‖ ∂μ‖ₑ :=
    (enorm_integral_norm_eq_lintegral_enorm (hi i)).symm
  have hf : (∑' i, ∫⁻ x, ‖F i x‖ₑ ∂μ) < ∞ := by
    rw [funext he]
    exact (tsum_enorm_ne_top_iff_summable_norm.2 hn.norm).lt_top
  refine ⟨hmeas, ?_⟩
  change ∫⁻ x, ‖∑' n, F n x‖ₑ ∂μ < ∞
  calc
    _ ≤ ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ := lintegral_mono (fun _ => enorm_tsum_le_tsum_enorm)
    _ = ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ := lintegral_tsum (fun n => (hi n).1.enorm)
    _ < ∞ := hf

/-- The normalized Gamma density has Laplace integral `λ⁻ᵃ` on the positive half-line. -/
theorem integral_exp_neg_mul_normalized_rpow {a lam : ℝ} (ha : 0 < a) (hlam : 0 < lam) :
    IntegrableOn (fun x => Real.exp (-lam * x) * x ^ (a - 1) / Real.Gamma a) (Ioi 0) ∧
    (∫ x in Ioi 0, Real.exp (-lam * x) * x ^ (a - 1) / Real.Gamma a) =
      (1 / lam) ^ a := by
  have ht : (∫ x in Ioi 0, Real.exp (-lam * x) * x ^ (a - 1)) =
      (1 / lam) ^ a * Real.Gamma a := by
    calc
      _ = ∫ x in Ioi 0, x ^ (a - 1) * Real.exp (-(lam * x)) := by
        apply setIntegral_congr_fun measurableSet_Ioi
        intro x _
        change Real.exp (-lam * x) * x ^ (a - 1) =
          x ^ (a - 1) * Real.exp (-(lam * x))
        rw [neg_mul]
        exact mul_comm _ _
      _ = _ := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hlam
  have hg := Real.Gamma_pos_of_pos ha
  have hi : IntegrableOn (fun x => Real.exp (-lam * x) * x ^ (a - 1)) (Ioi 0) := by
    apply Integrable.of_integral_ne_zero
    rw [ht]
    exact (mul_pos (Real.rpow_pos_of_pos (div_pos zero_lt_one hlam) _) hg).ne'
  refine ⟨hi.div_const _, ?_⟩
  rw [integral_div, ht, mul_div_cancel_right₀ _ hg.ne']

private theorem laplace_gamma_series {θ q lam c : ℝ} (hθ : 1 < θ) (hq : 0 ≤ q)
    (hlam : 0 < lam) (hc : c ≤ 1)
    (hpoint : ∀ x : ℝ, 0 < x → Summable (fun n : ℕ =>
      q ^ n * x ^ (θ * (n + 1) - c - 1) / Real.Gamma (θ * (n + 1) - c)))
    (hgeom : Summable (fun n : ℕ => q ^ n * (1 / lam) ^ (θ * (n + 1) - c))) :
    IntegrableOn (fun x => Real.exp (-lam * x) * ∑' n : ℕ,
      q ^ n * x ^ (θ * (n + 1) - c - 1) / Real.Gamma (θ * (n + 1) - c)) (Ioi 0) ∧
    (∫ x in Ioi 0, Real.exp (-lam * x) * ∑' n : ℕ,
      q ^ n * x ^ (θ * (n + 1) - c - 1) / Real.Gamma (θ * (n + 1) - c)) =
      ∑' n : ℕ, q ^ n * (1 / lam) ^ (θ * (n + 1) - c) := by
  let F := fun (n : ℕ) (x : ℝ) => Real.exp (-lam * x) *
    (q ^ n * x ^ (θ * (n + 1) - c - 1) / Real.Gamma (θ * (n + 1) - c))
  have ha (n : ℕ) : 0 < θ * (n + 1) - c := by
    have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    nlinarith
  have he (n : ℕ) : F n = fun x => q ^ n *
      (Real.exp (-lam * x) * x ^ (θ * (n + 1) - c - 1) /
        Real.Gamma (θ * (n + 1) - c)) := by funext x; dsimp [F]; ring
  have hi (n : ℕ) : IntegrableOn (F n) (Ioi 0) := by
    rw [he]
    exact (integral_exp_neg_mul_normalized_rpow (ha n) hlam).1.const_mul _
  have hInt (n : ℕ) : (∫ x in Ioi 0, F n x) =
      q ^ n * (1 / lam) ^ (θ * (n + 1) - c) := by
    rw [he, integral_const_mul, (integral_exp_neg_mul_normalized_rpow (ha n) hlam).2]
  have hnorm (n : ℕ) : (∫ x in Ioi 0, ‖F n x‖) =
      q ^ n * (1 / lam) ^ (θ * (n + 1) - c) := by
    rw [← hInt n]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro x hx
    change ‖F n x‖ = F n x
    rw [Real.norm_eq_abs, abs_of_nonneg]
    dsimp [F]
    exact mul_nonneg (Real.exp_pos _).le
      (div_nonneg (mul_nonneg (pow_nonneg hq _) (Real.rpow_nonneg (le_of_lt hx) _))
        (Real.Gamma_pos_of_pos (ha n)).le)
  have hn : Summable (fun n => ∫ x in Ioi 0, ‖F n x‖) := by
    simpa only [hnorm] using hgeom
  have hs : ∀ᵐ x ∂volume.restrict (Ioi 0), Summable (fun n => F n x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (hpoint x hx).mul_left _
  have heq : (fun x => Real.exp (-lam * x) * ∑' n : ℕ,
      q ^ n * x ^ (θ * (n + 1) - c - 1) / Real.Gamma (θ * (n + 1) - c)) =
      (fun x => ∑' n, F n x) := by
    funext x
    exact (tsum_mul_left).symm
  rw [heq]
  refine ⟨integrable_series hi hs hn, ?_⟩
  rw [← integral_tsum_of_summable_integral_norm hi hn]
  exact tsum_congr hInt

private theorem gamma_series_geometric {θ q lam : ℝ} (hθ : 0 < θ) (hq : 0 < q)
    (hlam : q ^ (1 / θ) < lam) (c : ℝ) :
    Summable (fun n : ℕ => q ^ n * (1 / lam) ^ (θ * (n + 1) - c)) ∧
    (∑' n : ℕ, q ^ n * (1 / lam) ^ (θ * (n + 1) - c)) =
      (1 / lam) ^ (θ - c) / (1 - q * (1 / lam) ^ θ) := by
  have hl : 0 < lam := (Real.rpow_pos_of_pos hq _).trans hlam
  have hi : 0 < 1 / lam := div_pos zero_lt_one hl
  have hql : q < lam ^ θ := by
    exact (Real.rpow_inv_lt_iff_of_pos hq.le hl.le hθ).1 (by simpa only [one_div] using hlam)
  have hr0 : 0 ≤ q * (1 / lam) ^ θ := by positivity
  have hr : q * (1 / lam) ^ θ < 1 := by
    rw [one_div, Real.inv_rpow hl.le, ← div_eq_mul_inv]
    exact (div_lt_one (Real.rpow_pos_of_pos hl _)).2 hql
  have he : (fun n : ℕ => q ^ n * (1 / lam) ^ (θ * (n + 1) - c)) =
      (fun n : ℕ => (1 / lam) ^ (θ - c) * (q * (1 / lam) ^ θ) ^ n) := by
    funext n
    rw [show θ * (n + 1) - c = θ * n + (θ - c) by ring,
      Real.rpow_add hi, Real.rpow_mul_natCast hi.le, mul_pow]
    ring
  rw [he]
  refine ⟨(summable_geometric_of_lt_one hr0 hr).mul_left _, ?_⟩
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr]
  ring

private theorem laplace_stableSeries_pair {θ q lam : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hq : 0 < q) (hlam : q ^ (1 / θ) < lam) :
    (IntegrableOn (fun x => Real.exp (-lam * x) * stableSeries θ q x) (Ioi 0) ∧
      (∫ x in Ioi 0, Real.exp (-lam * x) * stableSeries θ q x) = 1 / (lam ^ θ - q)) ∧
    (IntegrableOn (fun x => Real.exp (-lam * x) * stableSeriesDeriv θ q x) (Ioi 0) ∧
      (∫ x in Ioi 0, Real.exp (-lam * x) * stableSeriesDeriv θ q x) = lam / (lam ^ θ - q)) := by
  have ht : 0 < θ := by linarith [hθ.1]
  have hl : 0 < lam := (Real.rpow_pos_of_pos hq _).trans hlam
  have hql : q < lam ^ θ :=
    (Real.rpow_inv_lt_iff_of_pos hq.le hl.le ht).1 (by simpa only [one_div] using hlam)
  have hA : lam ^ θ ≠ 0 := (Real.rpow_pos_of_pos hl _).ne'
  have hAq : lam ^ θ - q ≠ 0 := (sub_pos.mpr hql).ne'
  have hgeom0 := gamma_series_geometric ht hq hlam 0
  have hgeom1 := gamma_series_geometric ht hq hlam 1
  have h0 := laplace_gamma_series hθ.1 hq.le hl (c := 0) (by norm_num)
    (fun x hx => by simpa only [sub_zero, stableSeriesTerm] using
      summable_stableSeriesTerm hθ q hx.le) hgeom0.1
  have h1 := laplace_gamma_series hθ.1 hq.le hl (c := 1) le_rfl
    (fun x hx => by
      simpa only [stableSeriesDerivTerm, sub_sub, one_add_one_eq_two] using
        summable_stableSeriesDerivTerm hθ q hx) hgeom1.1
  have he0 : (fun x => Real.exp (-lam * x) * stableSeries θ q x) =ᵐ[volume.restrict (Ioi 0)]
      (fun x => Real.exp (-lam * x) * ∑' n : ℕ,
        q ^ n * x ^ (θ * (n + 1) - 0 - 1) / Real.Gamma (θ * (n + 1) - 0)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    simp only [stableSeries, ite_eq_left (le_of_lt hx), stableSeriesTerm, sub_zero]
  have he1 : (fun x => Real.exp (-lam * x) * stableSeriesDeriv θ q x) =ᵐ[volume.restrict (Ioi 0)]
      (fun x => Real.exp (-lam * x) * ∑' n : ℕ,
        q ^ n * x ^ (θ * (n + 1) - 1 - 1) / Real.Gamma (θ * (n + 1) - 1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 0 < x at hx
    simp only [stableSeriesDeriv, ite_eq_left hx, stableSeriesDerivTerm, sub_sub,
      one_add_one_eq_two]
  refine ⟨⟨h0.1.congr he0.symm, ?_⟩, ⟨h1.1.congr he1.symm, ?_⟩⟩
  · rw [integral_congr_ae he0, h0.2, hgeom0.2, sub_zero, one_div,
      Real.inv_rpow hl.le]
    field_simp
  · rw [integral_congr_ae he1, h1.2, hgeom1.2,
      Real.rpow_sub (by positivity : 0 < 1 / lam), Real.rpow_one,
      one_div, Real.inv_rpow hl.le]
    field_simp

/-- The tilted scale series and its derivative are integrable, with geometric Laplace sum. -/
theorem integral_exp_neg_mul_stableSeries {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {lam : ℝ} (hlam : q ^ (1 / θ) < lam) :
    Integrable (fun x => Real.exp (-lam * x) * stableSeries θ q x) (volume.restrict (Ioi 0)) ∧
    Integrable (fun x => Real.exp (-lam * x) * stableSeriesDeriv θ q x)
      (volume.restrict (Ioi 0)) ∧
    ∫ x in Ioi 0, Real.exp (-lam * x) * stableSeries θ q x = 1 / (lam ^ θ - q) := by
  obtain ⟨h0, h1⟩ := laplace_stableSeries_pair hθ hq hlam
  exact ⟨h0.1, h1.1, h0.2⟩

/-- Transform of `W_q' - Φ W_q`: `(λ-Φ)/(λ^θ-q) = (Φ/q) F_q(λ)`. -/
theorem integral_exp_neg_mul_stableSeriesDeriv_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) {lam : ℝ} (hlam : q ^ (1 / θ) < lam) :
    ∫ x in Ioi 0, Real.exp (-lam * x) *
        (stableSeriesDeriv θ q x - q ^ (1 / θ) * stableSeries θ q x) =
      (lam - q ^ (1 / θ)) / (lam ^ θ - q) := by
  obtain ⟨h0, h1⟩ := laplace_stableSeries_pair hθ hq hlam
  simp_rw [mul_sub, ← mul_assoc, mul_comm (Real.exp (-lam * _)) (q ^ (1 / θ)), mul_assoc]
  rw [integral_sub h1.1 (h0.1.const_mul _), integral_const_mul, h1.2, h0.2]
  ring

end BGW.StableTrees
