/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableLocalMarkov

import BGW.StableTrees.Attraction.DomainCriterion

/-!
# Positive jumps of the stable process: Laplace and tail estimates

This module computes the second difference of the stable Laplace transform and derives the
frequent polynomial lower bound for the positive tail needed to detect jumps of the host process.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- `x ↦ e^{-λx}` is integrable under the stable law for `λ ≥ 0` (its integral `e^{λ^θ}` is
nonzero). -/
theorem integrable_exp_neg_mul_stableLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    Integrable (fun x => Real.exp (-lam * x)) (stableLaw θ : Measure ℝ) := by
  by_contra h
  have hL := integral_exp_neg_mul_stableLaw hθ hlam
  rw [integral_undef h] at hL
  exact (Real.exp_ne_zero (lam ^ θ)) hL.symm

private theorem one_sub_exp_sq_eq (lam : ℝ) :
    (fun x => (1 - Real.exp (-lam * x)) ^ 2) =
      (fun x => 1 - 2 * Real.exp (-lam * x) + Real.exp (-(2 * lam) * x)) := by
  funext x
  rw [show -(2 * lam) * x = -lam * x + -lam * x by ring, Real.exp_add]
  ring

/-- Second difference of the Laplace transform: `E(1 - e^{-λX})^2 = e^{(2λ)^θ} - 2e^{λ^θ} + 1`. -/
theorem integral_one_sub_exp_sq_stableLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    ∫ x, (1 - Real.exp (-lam * x)) ^ 2 ∂(stableLaw θ : Measure ℝ) =
      Real.exp ((2 * lam) ^ θ) - 2 * Real.exp (lam ^ θ) + 1 := by
  have h1 := integrable_exp_neg_mul_stableLaw hθ hlam
  have h2 : Integrable (fun x => Real.exp (-(2 * lam) * x))
      (stableLaw θ : Measure ℝ) :=
    integrable_exp_neg_mul_stableLaw hθ (lam := 2 * lam) (mul_nonneg (by norm_num) hlam)
  rw [one_sub_exp_sq_eq, integral_add (f := fun x : ℝ => 1 - 2 * Real.exp (-lam * x))
    (g := fun x => Real.exp (-(2 * lam) * x))
    ((integrable_const (1 : ℝ)).sub (h1.const_mul 2)) h2,
    integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun x => 2 * Real.exp (-lam * x))
    (integrable_const (1 : ℝ)) (h1.const_mul 2), integral_const_mul,
    integral_exp_neg_mul_stableLaw hθ hlam,
    integral_exp_neg_mul_stableLaw hθ (lam := 2 * lam) (mul_nonneg (by norm_num) hlam)]
  simp
  ring

private theorem one_sub_exp_sq_le_min {lam x : ℝ} (hlam : 0 ≤ lam) (hx : 0 ≤ x) :
    (1 - Real.exp (-lam * x)) ^ 2 ≤ min ((lam * max x 0) ^ 2) 1 := by
  have hz : 0 ≤ lam * x := mul_nonneg hlam hx
  have hlow : 0 ≤ 1 - Real.exp (-lam * x) := by
    have he : Real.exp (-lam * x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hupp : 1 - Real.exp (-lam * x) ≤ lam * x := by
    have he := Real.add_one_le_exp (-lam * x)
    linarith
  have hone : 1 - Real.exp (-lam * x) ≤ 1 := by
    have := (Real.exp_pos (-lam * x)).le
    linarith
  rw [max_eq_left hx]
  exact le_min (by nlinarith) (by nlinarith)

private theorem sq_le_four_mul_exp {z : ℝ} (hz : 0 ≤ z) : z ^ 2 ≤ 4 * Real.exp z := by
  have h := Real.add_one_le_exp (z / 2)
  have h' : 1 + z / 2 ≤ Real.exp (z / 2) := by linarith
  have hs := sq_le_sq₀ (by positivity : (0 : ℝ) ≤ 1 + z / 2)
    (Real.exp_pos (z / 2)).le |>.mpr h'
  rw [← Real.exp_nat_mul] at hs
  norm_num at hs
  rw [show (2 : ℝ) * (z / 2) = z by ring] at hs
  nlinarith

private theorem one_sub_exp_sq_le_neg {lam x : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (hx : x < 0) :
    (1 - Real.exp (-lam * x)) ^ 2 ≤ 4 * lam ^ 2 * Real.exp (-3 * x) := by
  let y := -(lam * x)
  have hy : 0 ≤ y := by
    dsimp [y]
    exact neg_nonneg.mpr (mul_nonpos_of_nonneg_of_nonpos hlam hx.le)
  have he : Real.exp y - 1 ≤ y * Real.exp y := by
    have h := Real.add_one_le_exp (-y)
    have hmul := mul_le_mul_of_nonneg_left h (Real.exp_pos y).le
    rw [mul_add, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one] at hmul
    nlinarith
  have hsq : (1 - Real.exp y) ^ 2 ≤ y ^ 2 * Real.exp (2 * y) := by
    have hnonneg : 0 ≤ Real.exp y - 1 := by
      have := Real.add_one_le_exp y
      linarith
    rw [show (1 - Real.exp y) ^ 2 = (Real.exp y - 1) ^ 2 by ring]
    calc
      (Real.exp y - 1) ^ 2 ≤ (y * Real.exp y) ^ 2 := by nlinarith
      _ = y ^ 2 * Real.exp (2 * y) := by rw [mul_pow, ← Real.exp_nat_mul]; ring_nf
  have hx2 : x ^ 2 ≤ 4 * Real.exp (-x) := by
    simpa using sq_le_four_mul_exp (neg_nonneg.mpr hx.le)
  calc
    (1 - Real.exp (-lam * x)) ^ 2 = (1 - Real.exp y) ^ 2 := by
      rw [show -lam * x = -(lam * x) by ring]
    _ ≤ y ^ 2 * Real.exp (2 * y) := hsq
    _ = lam ^ 2 * x ^ 2 * Real.exp (2 * y) := by dsimp [y]; ring
    _ ≤ lam ^ 2 * (4 * Real.exp (-x)) * Real.exp (2 * y) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hx2 (sq_nonneg lam)) (Real.exp_nonneg _)
    _ = 4 * lam ^ 2 * Real.exp (-x + 2 * y) := by
      rw [Real.exp_add]
      ring
    _ ≤ 4 * lam ^ 2 * Real.exp (-3 * x) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Real.exp_le_exp.mpr
      dsimp [y]
      nlinarith [mul_nonneg (sub_nonneg.mpr hlam1) (neg_nonneg.mpr hx.le)]

private theorem one_sub_exp_sq_le_majorant {lam x : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam ≤ 1) :
    (1 - Real.exp (-lam * x)) ^ 2 ≤
      4 * lam ^ 2 * Real.exp (-3 * x) + min ((lam * max x 0) ^ 2) 1 := by
  by_cases hx : 0 ≤ x
  · exact (one_sub_exp_sq_le_min hlam hx).trans (le_add_of_nonneg_left (by positivity))
  · have hx' : x < 0 := lt_of_not_ge hx
    have hmin : min ((lam * max x 0) ^ 2) 1 = 0 := by
      rw [max_eq_right hx'.le]
      simp
    rw [hmin, add_zero]
    exact one_sub_exp_sq_le_neg hlam hlam1 hx'

private theorem laplace_second_lower {θ lam : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hlam : 0 < lam) (hlam1 : lam ≤ 1) :
    (2 ^ θ - 2) * lam ^ θ - 2 * (lam ^ θ) ^ 2 ≤
      Real.exp ((2 * lam) ^ θ) - 2 * Real.exp (lam ^ θ) + 1 := by
  have hθ0 : 0 < θ := by linarith [hθ.1]
  have hB : lam ^ θ ≤ 1 := by
    rw [← Real.one_rpow θ]
    exact Real.rpow_le_rpow hlam.le hlam1 hθ0.le
  have hE := Real.abs_exp_sub_one_sub_id_le (x := lam ^ θ) (by
    rw [abs_of_nonneg (Real.rpow_nonneg hlam.le _)]
    exact hB)
  have hA := Real.add_one_le_exp ((2 * lam) ^ θ)
  have hpow : (2 * lam) ^ θ = 2 ^ θ * lam ^ θ :=
    Real.mul_rpow (by norm_num) hlam.le
  rw [hpow] at hA ⊢
  have hb : Real.exp (lam ^ θ) ≤ 1 + lam ^ θ + (lam ^ θ) ^ 2 := by
    have hpos := le_abs_self (Real.exp (lam ^ θ) - 1 - lam ^ θ)
    have := hpos.trans hE
    linarith
  nlinarith

private theorem layer_set_eq {lam t : ℝ} (hlam : 0 < lam) (ht : 0 < t) :
    {x : ℝ | t < (lam * max x 0) ^ 2} = Set.Ioi (Real.sqrt t / lam) := by
  ext x
  simp only [Set.mem_ofPred_eq, Set.mem_Ioi]
  have hs : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have harg : 0 ≤ lam * max x 0 := mul_nonneg hlam.le (le_max_right _ _)
  have hiff : t < (lam * max x 0) ^ 2 ↔ Real.sqrt t < lam * max x 0 := by
    rw [← sq_lt_sq₀ (Real.sqrt_nonneg _) harg, hs]
  rw [hiff]
  constructor
  · intro h
    have hx : 0 < x := by
      by_contra hx
      have : max x 0 = 0 := max_eq_right (le_of_not_gt hx)
      rw [this, mul_zero] at h
      exact (not_lt_of_ge (Real.sqrt_nonneg _) h)
    rw [max_eq_left hx.le] at h
    exact (div_lt_iff₀ hlam).mpr (by simpa [mul_comm] using h)
  · intro h
    have hx : 0 < x := (div_pos (Real.sqrt_pos.mpr ht) hlam).trans h
    rw [max_eq_left hx.le]
    have := (div_lt_iff₀ hlam).mp h
    nlinarith

private theorem intervalIntegrable_of_bounded {F : ℝ → ℝ} (hF : Measurable F)
    (hF0 : ∀ t, 0 ≤ F t) (hF1 : ∀ t, F t ≤ 1) (a b : ℝ) :
    IntervalIntegrable F volume a b := by
  constructor <;>
    apply IntegrableOn.of_bound measure_Ioc_lt_top hF.aestronglyMeasurable.restrict 1 <;>
    filter_upwards [] with t
  all_goals
    rw [Real.norm_of_nonneg (hF0 t)]
    exact hF1 t

private theorem capped_integral_le {θ c x₀ lam : ℝ} (hθ2 : θ < 2) (hc : 0 < c) (hx₀ : 0 < x₀)
    (hlam : 0 < lam) (hsmall : lam * x₀ ≤ 1)
    (htail : ∀ x ≥ x₀, x ^ θ * (stableLaw θ : Measure ℝ).real (Set.Ioi x) ≤ c) :
    (∫ x, min ((lam * max x 0) ^ 2) 1 ∂(stableLaw θ : Measure ℝ)) ≤
      (lam * x₀) ^ 2 + (2 * c / (2 - θ)) * lam ^ θ := by
  let μ : Measure ℝ := stableLaw θ
  let F : ℝ → ℝ := fun t => μ.real {x : ℝ | t < (lam * max x 0) ^ 2}
  have hFanti : Antitone F := by
    intro s t hst
    exact measureReal_mono (fun _ hx => hst.trans_lt hx)
  have hF0 : ∀ t, 0 ≤ F t := fun _ => measureReal_nonneg
  have hF1 : ∀ t, F t ≤ 1 := fun _ => measureReal_le_one
  have hFint (a b : ℝ) : IntervalIntegrable F volume a b :=
    intervalIntegrable_of_bounded hFanti.measurable hF0 hF1 a b
  rw [Attraction.DomainCriterion.integral_min_sq_eq_integrated_tail μ
    (fun x => lam * max x 0) (by fun_prop) zero_le_one]
  change (∫ t in (0 : ℝ)..1, F t) ≤ _
  let u : ℝ := (lam * x₀) ^ 2
  have hu0 : 0 ≤ u := sq_nonneg _
  have hu1 : u ≤ 1 := by
    have hnonneg : 0 ≤ lam * x₀ := mul_nonneg hlam.le hx₀.le
    simpa [u] using (sq_le_sq₀ hnonneg zero_le_one).mpr hsmall
  have hsub0 : Set.uIcc (0 : ℝ) u ⊆ Set.uIcc 0 1 := by
    apply Set.uIcc_subset_uIcc <;> simp [hu0, hu1]
  have hsub1 : Set.uIcc u 1 ⊆ Set.uIcc (0 : ℝ) 1 := by
    apply Set.uIcc_subset_uIcc <;> simp [hu0, hu1]
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hFint 0 1 |>.mono_set hsub0) (hFint 0 1 |>.mono_set hsub1)]
  have hfirst : (∫ t in (0 : ℝ)..u, F t) ≤ u := by
    calc
      (∫ t in (0 : ℝ)..u, F t) ≤ ∫ _t in (0 : ℝ)..u, (1 : ℝ) :=
        intervalIntegral.integral_mono_on_of_le_Ioo hu0 (hFint 0 u) intervalIntegrable_const
          (fun t _ => hF1 t)
      _ = u := by simp
  have hsecond : (∫ t in u..1, F t) ≤
      ∫ t in u..1, c * lam ^ θ * t ^ (-θ / 2) := by
    apply intervalIntegral.integral_mono_on_of_le_Ioo hu1
    · exact hFint u 1
    · exact IntervalIntegrable.const_mul
        (intervalIntegral.intervalIntegrable_rpow' (r := -θ / 2) (by linarith [hθ2])) _
    · intro t ht
      have ht0 : 0 < t := hu0.trans_lt ht.1
      let q : ℝ := Real.sqrt t / lam
      have hq0 : 0 < q := div_pos (Real.sqrt_pos.mpr ht0) hlam
      have hqx : x₀ ≤ q := by
        have hsqrt : lam * x₀ < Real.sqrt t := by
          rw [← Real.sqrt_sq (mul_nonneg hlam.le hx₀.le)]
          exact Real.sqrt_lt_sqrt (sq_nonneg _) (by simpa [u] using ht.1)
        change x₀ ≤ Real.sqrt t / lam
        exact (le_div_iff₀ hlam).mpr (by simpa [mul_comm] using hsqrt.le)
      have hqpow : q ^ θ = t ^ (θ / 2) / lam ^ θ := by
        calc
          q ^ θ = (Real.sqrt t) ^ θ / lam ^ θ :=
            Real.div_rpow (Real.sqrt_nonneg _) hlam.le θ
          _ = (t ^ (1 / 2 : ℝ)) ^ θ / lam ^ θ := by rw [Real.sqrt_eq_rpow]
          _ = t ^ (θ / 2) / lam ^ θ := by
            rw [← Real.rpow_mul ht0.le]
            congr 2
            ring
      rw [show F t = μ.real (Set.Ioi q) from congrArg μ.real (layer_set_eq hlam ht0)]
      have htq : q ^ θ * μ.real (Set.Ioi q) ≤ c := htail q hqx
      calc
        μ.real (Set.Ioi q) ≤ c / q ^ θ :=
          (le_div_iff₀ (Real.rpow_pos_of_pos hq0 θ)).mpr (by simpa [mul_comm] using htq)
        _ = c * lam ^ θ * t ^ (-θ / 2) := by
          rw [hqpow, show -θ / 2 = -(θ / 2) by ring, Real.rpow_neg ht0.le]
          have hlamPow : lam ^ θ ≠ 0 := (Real.rpow_pos_of_pos hlam θ).ne'
          have htθ : t ^ (θ / 2) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
          field_simp
  have hg0 : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) 1)]
      fun t => c * lam ^ θ * t ^ (-θ / 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    exact mul_nonneg (mul_nonneg hc.le (Real.rpow_nonneg hlam.le _))
      (Real.rpow_nonneg ht.1.le _)
  have hgint : IntervalIntegrable (fun t => c * lam ^ θ * t ^ (-θ / 2)) volume 0 1 :=
    IntervalIntegrable.const_mul
      (intervalIntegral.intervalIntegrable_rpow' (r := -θ / 2) (by linarith [hθ2])) _
  have hsecond' : (∫ t in u..1, c * lam ^ θ * t ^ (-θ / 2)) ≤
      ∫ t in (0 : ℝ)..1, c * lam ^ θ * t ^ (-θ / 2) :=
    intervalIntegral.integral_mono_interval hu0 hu1 le_rfl hg0 hgint
  have heval : (∫ t in (0 : ℝ)..1, c * lam ^ θ * t ^ (-θ / 2)) =
      (2 * c / (2 - θ)) * lam ^ θ := by
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (Or.inl (show -1 < -θ / 2 by linarith [hθ2]))]
    rw [Real.zero_rpow (by linarith [hθ2] : -θ / 2 + 1 ≠ 0), Real.one_rpow]
    simp only [sub_zero]
    field_simp [show 2 - θ ≠ 0 by linarith]
    rw [show -θ + 2 = 2 - θ by ring, div_self (by linarith)]
  dsimp [u] at hfirst
  linarith

private theorem integrable_one_sub_exp_sq {θ lam : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hlam : 0 ≤ lam) :
    Integrable (fun x => (1 - Real.exp (-lam * x)) ^ 2) (stableLaw θ : Measure ℝ) := by
  have h1 := integrable_exp_neg_mul_stableLaw hθ hlam
  have h2 := integrable_exp_neg_mul_stableLaw hθ (lam := 2 * lam)
    (mul_nonneg (by norm_num) hlam)
  rw [one_sub_exp_sq_eq]
  exact ((integrable_const (1 : ℝ)).sub (h1.const_mul 2)).add h2

private theorem integral_majorant_bound {θ c x₀ lam : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (hθ2 : θ < 2) (hc : 0 < c) (hx₀ : 0 < x₀) (hlam : 0 < lam)
    (hlam1 : lam ≤ 1) (hsmall : lam * x₀ ≤ 1)
    (htail : ∀ x ≥ x₀, x ^ θ * (stableLaw θ : Measure ℝ).real (Set.Ioi x) ≤ c) :
    (∫ x, (1 - Real.exp (-lam * x)) ^ 2 ∂(stableLaw θ : Measure ℝ)) ≤
      (2 * c / (2 - θ)) * lam ^ θ +
        (4 * Real.exp (3 ^ θ) + x₀ ^ 2) * lam ^ 2 := by
  let μ : Measure ℝ := stableLaw θ
  have hcapInt : Integrable (fun x => min ((lam * max x 0) ^ 2) 1) μ := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (le_min (sq_nonneg _) zero_le_one)]
    exact min_le_right _ _
  have hnegInt : Integrable (fun x => 4 * lam ^ 2 * Real.exp (-3 * x)) μ :=
    (integrable_exp_neg_mul_stableLaw hθ (lam := 3) (by norm_num)).const_mul _
  have hbound : (∫ x, (1 - Real.exp (-lam * x)) ^ 2 ∂μ) ≤
      ∫ x, 4 * lam ^ 2 * Real.exp (-3 * x) + min ((lam * max x 0) ^ 2) 1 ∂μ := by
    apply integral_mono (integrable_one_sub_exp_sq hθ hlam.le) (hnegInt.add hcapInt)
    intro x
    exact one_sub_exp_sq_le_majorant hlam.le hlam1
  have hcap := capped_integral_le hθ2 hc hx₀ hlam hsmall htail
  rw [integral_add hnegInt hcapInt, integral_const_mul,
    integral_exp_neg_mul_stableLaw hθ (lam := 3) (by norm_num)] at hbound
  calc
    (∫ x, (1 - Real.exp (-lam * x)) ^ 2 ∂μ) ≤
        4 * lam ^ 2 * Real.exp (3 ^ θ) +
          ∫ x, min ((lam * max x 0) ^ 2) 1 ∂μ := hbound
    _ ≤ 4 * lam ^ 2 * Real.exp (3 ^ θ) +
        ((lam * x₀) ^ 2 + (2 * c / (2 - θ)) * lam ^ θ) := by linarith
    _ = (2 * c / (2 - θ)) * lam ^ θ +
        (4 * Real.exp (3 ^ θ) + x₀ ^ 2) * lam ^ 2 := by ring

/-- **Tail lower bound** for `1 < θ < 2`: `limsup_{x→∞} x^θ P(X_1 > x) > 0`. -/
theorem frequently_le_rpow_mul_stableLaw_Ioi {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) :
    ∃ c : ℝ, 0 < c ∧
      ∃ᶠ x in atTop, c ≤ x ^ θ * (stableLaw θ : Measure ℝ).real (Set.Ioi x) := by
  let C : ℝ := 2 ^ θ - 2
  have hC : 0 < C := by
    have hpow := (Real.rpow_lt_rpow_left_iff (x := (2 : ℝ)) (y := 1) (z := θ)
      (by norm_num)).mpr hθ.1
    dsimp [C]
    simpa using sub_pos.mpr hpow
  let c : ℝ := (2 - θ) * C / 4
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  by_contra hfreq
  rw [not_frequently] at hfreq
  have hev : ∀ᶠ x in atTop,
      x ^ θ * (stableLaw θ : Measure ℝ).real (Set.Ioi x) < c ∧ 0 < x := by
    filter_upwards [hfreq, eventually_gt_atTop (0 : ℝ)] with x hx hx0
    exact ⟨not_le.mp hx, hx0⟩
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.mp hev
  have hx₀0 : 0 < x₀ := (hx₀ x₀ le_rfl).2
  have htail : ∀ x ≥ x₀, x ^ θ * (stableLaw θ : Measure ℝ).real (Set.Ioi x) ≤ c :=
    fun x hx => (hx₀ x hx).1.le
  have hcc : 2 * c / (2 - θ) = C / 2 := by
    dsimp [c]
    field_simp [show 2 - θ ≠ 0 by linarith]
    ring
  have hsmall : Set.Iio (min 1 (1 / x₀)) ∈ 𝓝 (0 : ℝ) :=
    Iio_mem_nhds (lt_min zero_lt_one (by positivity))
  have hevlam : ∀ᶠ lam in 𝓝[>] (0 : ℝ), lam ≤ min 1 (1 / x₀) :=
    mem_of_superset (mem_nhdsWithin_of_mem_nhds hsmall) (fun _ hx => (Set.mem_Iio.mp hx).le)
  have hnorm : ∀ᶠ lam in 𝓝[>] (0 : ℝ),
      C - 2 * lam ^ θ ≤ C / 2 +
        (4 * Real.exp (3 ^ θ) + x₀ ^ 2) * lam ^ (2 - θ) := by
    filter_upwards [self_mem_nhdsWithin, hevlam] with lam hlam hle
    have hlam1 : lam ≤ 1 := hle.trans (min_le_left _ _)
    have hxlam : lam ≤ 1 / x₀ := hle.trans (min_le_right _ _)
    have hxsmall : lam * x₀ ≤ 1 := (le_div_iff₀ hx₀0).mp hxlam

    have hlow := laplace_second_lower hθ hlam hlam1
    have hu := integral_majorant_bound hθ hθ2 hc hx₀0 hlam hlam1 hxsmall htail
    rw [hcc] at hu
    rw [integral_one_sub_exp_sq_stableLaw hθ hlam.le] at hu
    have hdiv := div_le_div_of_nonneg_right (hlow.trans hu)
      (Real.rpow_pos_of_pos hlam θ).le
    have hpow : lam ^ (2 - θ) = lam ^ (2 : ℝ) / lam ^ θ := Real.rpow_sub hlam 2 θ
    have hpow0 : lam ^ θ ≠ 0 := (Real.rpow_pos_of_pos hlam θ).ne'
    rw [hpow, Real.rpow_two]
    convert hdiv using 1
    · field_simp [hpow0]
      ring
    · field_simp [hpow0]
  have hzero : Tendsto (fun lam : ℝ => lam) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hlimθ : Tendsto (fun lam : ℝ => lam ^ θ) (𝓝[>] 0) (𝓝 0) :=
    hzero.rpow_const_nhds_zero (by linarith [hθ.1])
  have hlim2 : Tendsto (fun lam : ℝ => lam ^ (2 - θ)) (𝓝[>] 0) (𝓝 0) :=
    hzero.rpow_const_nhds_zero (by linarith)
  have hlimL : Tendsto (fun lam : ℝ => C - 2 * lam ^ θ) (𝓝[>] 0) (𝓝 (C - 2 * 0)) :=
    tendsto_const_nhds.sub (tendsto_const_nhds.mul hlimθ)
  have hlimU : Tendsto (fun lam : ℝ => C / 2 +
      (4 * Real.exp (3 ^ θ) + x₀ ^ 2) * lam ^ (2 - θ)) (𝓝[>] 0)
      (𝓝 (C / 2 + (4 * Real.exp (3 ^ θ) + x₀ ^ 2) * 0)) :=
    tendsto_const_nhds.add (tendsto_const_nhds.mul hlim2)
  simp only [mul_zero, add_zero, sub_zero] at hlimL hlimU
  have hCle : C ≤ C / 2 := le_of_tendsto_of_tendsto hlimL hlimU hnorm
  linarith

end BGW.StableTrees
