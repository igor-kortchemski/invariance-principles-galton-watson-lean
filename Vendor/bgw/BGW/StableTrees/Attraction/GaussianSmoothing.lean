/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.TransformConvergence
public import BGW.StableTrees.Attraction.Defs
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.Analysis.Calculus.DSlope
public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.TaylorExpansion

/-!
# Gaussian smoothing of an attracted step law

The characteristic-function defect is obtained at moving frequencies. The centering
phase disappears on taking moduli. The exponent of the squared stable modulus is
`2 * cos (π * θ / 2) * |t| ^ θ`, which is negative for nonzero `t`.
Ported from `BGWLeaves/StableAnalysis/GaussianSmoothing.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology ComplexConjugate

namespace BGW.StableTrees.Attraction.GaussianSmoothing

open BGW.StableTrees.Attraction
open BGW.StableTrees.Attraction.TransformConvergence
open BGW.StableTrees.Scalar

/-- Removing the deterministic centering phase from the squared modulus. -/
theorem norm_sq_centeredScaledWalk_charFun (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m a : ℝ) (n : ℕ) (t : ℝ) :
    ‖charFun (centeredScaledWalk ν m a n) t‖ ^ 2 =
      (‖stepCharFun ν (t / a)‖ ^ 2) ^ n := by
  rw [centeredScaledWalk_charFun, norm_mul, norm_pow]
  have hp : ‖cexp (-((t * (n : ℝ) * m / a : ℝ) : ℂ) * I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hp, one_mul, ← pow_mul, ← pow_mul, Nat.mul_comm n 2]

/-- The squared stable modulus, with its (negative) exponent explicit. -/
theorem norm_sq_stableCF {θ : ℝ} (hθ : θ ≠ 0) (t : ℝ) :
    ‖stableCF θ t‖ ^ 2 = Real.exp (2 * Real.cos (Real.pi * θ / 2) * |t| ^ θ) := by
  rw [norm_stableCF hθ, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- A power limit gives the first-order defect once the bases tend to one.
The derivative is extended at one, so the bases are allowed to equal one. -/
theorem tendsto_nat_mul_one_sub_of_pow {x : ℕ → ℝ} {k : ℕ → ℕ} {L : ℝ}
    (hx : Tendsto x atTop (𝓝 1))
    (hp : Tendsto (fun (n : ℕ) => x n ^ k n) atTop (𝓝 (Real.exp L))) :
    Tendsto (fun (n : ℕ) => (k n : ℝ) * (1 - x n)) atTop (𝓝 (-L)) := by
  have hl : Tendsto (fun (n : ℕ) => (k n : ℝ) * Real.log (x n)) atTop (𝓝 L) := by
    simpa only [Function.comp_def, Real.log_pow, Real.log_exp] using
      (Real.continuousAt_log (Real.exp_ne_zero L)).tendsto.comp hp
  have hd : Tendsto (fun (n : ℕ) => dslope Real.log 1 (x n)) atTop (𝓝 1) := by
    have hc : ContinuousAt (dslope Real.log 1) 1 :=
      continuousAt_dslope_same.mpr (Real.differentiableAt_log one_ne_zero)
    simpa only [Function.comp_def, dslope_same, Real.deriv_log, inv_one] using hc.tendsto.comp hx
  have hquot := hl.div hd one_ne_zero
  have hne : ∀ᶠ (n : ℕ) in atTop, dslope Real.log 1 (x n) ≠ 0 :=
    hd.eventually_ne one_ne_zero
  have heq : ∀ᶠ (n : ℕ) in atTop,
      (k n : ℝ) * (1 - x n) = -((k n : ℝ) * Real.log (x n) / dslope Real.log 1 (x n)) := by
    filter_upwards [hne] with n hn
    have hid := sub_smul_dslope Real.log 1 (x n)
    simp only [smul_eq_mul, Real.log_one, sub_zero] at hid
    rw [← neg_div]
    apply (eq_div_iff hn).2
    nlinarith
  simpa using hquot.neg.congr' (heq.mono fun _ h => h.symm)

/-- Attraction controls the squared one-step CF powers at moving frequencies. -/
theorem tendsto_stepCharFun_norm_sq_pow_moving
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) {t : ℕ → ℝ} {u : ℝ}
    (ht : Tendsto t atTop (𝓝 u)) :
    Tendsto (fun (n : ℕ) => (‖stepCharFun ν (t n / b n)‖ ^ 2) ^ n) atTop
      (𝓝 (Real.exp (2 * Real.cos (Real.pi * θ / 2) * |u| ^ θ))) := by
  have h := (hb.tendsto_centeredScaledWalk_charFun_moving ht).norm.pow 2
  rw [norm_sq_stableCF (by linarith [hb.alpha_mem.1])] at h
  simpa only [norm_sq_centeredScaledWalk_charFun] using h

/-- The symmetrized characteristic-function defect, including moving frequencies.
No step lower bound or first-moment hypothesis is needed for this implication. -/
theorem tendsto_nat_mul_stepCharFun_defect_moving
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) {t : ℕ → ℝ} {u : ℝ}
    (ht : Tendsto t atTop (𝓝 u)) :
    Tendsto (fun (n : ℕ) => (n : ℝ) * (1 - ‖stepCharFun ν (t n / b n)‖ ^ 2)) atTop
      (𝓝 (-2 * Real.cos (Real.pi * θ / 2) * |u| ^ θ)) := by
  have harg : Tendsto (fun (n : ℕ) => t n / b n) atTop (𝓝 0) :=
    ht.div_atTop (TransformConvergence.tendsto_atTop ν hb)
  have hbase : Tendsto (fun (n : ℕ) => ‖stepCharFun ν (t n / b n)‖ ^ 2) atTop (𝓝 1) := by
    have hcf :=
      (continuous_charFun (μ := ν.map (fun z : ℤ => (z : ℝ)))).continuousAt.tendsto.comp harg
    simpa [stepCharFun, Function.comp_def] using hcf.norm.pow 2
  simpa only [neg_mul] using tendsto_nat_mul_one_sub_of_pow hbase
    (tendsto_stepCharFun_norm_sq_pow_moving hb ht)

/-- The fixed-frequency specialization used in Gaussian smoothing. -/
theorem tendsto_nat_mul_stepCharFun_defect
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) (t : ℝ) :
    Tendsto (fun (n : ℕ) => (n : ℝ) * (1 - ‖stepCharFun ν (t / b n)‖ ^ 2)) atTop
      (𝓝 (-2 * Real.cos (Real.pi * θ / 2) * |t| ^ θ)) :=
  tendsto_nat_mul_stepCharFun_defect_moving hb tendsto_const_nhds

/-- The defect limit also holds along arbitrary diverging time changes. -/
theorem tendsto_nat_mul_stepCharFun_defect_subseq
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) {j : ℕ → ℕ}
    (hj : Tendsto j atTop atTop) {t : ℕ → ℝ} {u : ℝ}
    (ht : Tendsto t atTop (𝓝 u)) :
    Tendsto (fun (n : ℕ) => (j n : ℝ) * (1 - ‖stepCharFun ν (t n / b (j n))‖ ^ 2)) atTop
      (𝓝 (-2 * Real.cos (Real.pi * θ / 2) * |u| ^ θ)) := by
  obtain ⟨Q, hL, hQ⟩ := hb.tendsto_centeredScaledWalkProb
  have hcf := tendsto_charFun_moving (hQ.comp hj) ht
  rw [charFun_eq_stableCF (by linarith [hb.alpha_mem.1] : 0 < θ) hL] at hcf
  have hp := hcf.norm.pow 2
  rw [norm_sq_stableCF (by linarith [hb.alpha_mem.1])] at hp
  change Tendsto (fun n => ‖charFun (centeredScaledWalk ν m (b (j n)) (j n)) (t n)‖ ^ 2)
    atTop (𝓝 _) at hp
  simp only [norm_sq_centeredScaledWalk_charFun] at hp
  have harg : Tendsto (fun n => t n / b (j n)) atTop (𝓝 0) :=
    ht.div_atTop ((TransformConvergence.tendsto_atTop ν hb).comp hj)
  have hbase : Tendsto (fun n => ‖stepCharFun ν (t n / b (j n))‖ ^ 2) atTop (𝓝 1) := by
    have hc :=
      (continuous_charFun (μ := ν.map (fun z : ℤ => (z : ℝ)))).continuousAt.tendsto.comp harg
    simpa [stepCharFun, Function.comp_def] using hc.norm.pow 2
  simpa only [neg_mul] using tendsto_nat_mul_one_sub_of_pow hbase hp

/-- Compact-frequency boundedness, obtained from the moving-frequency defect limit. -/
theorem eventually_stepCharFun_defect_le_on_Icc
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) (R : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t ∈ Icc (-R) R,
      (n : ℝ) * (1 - ‖stepCharFun ν (t / b n)‖ ^ 2) ≤ C := by
  classical
  by_contra h
  push Not at h
  have hbad (k : ℕ) := h (k + 1) (by positivity) k
  choose j hj t ht hgt using hbad
  have hjtop : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  obtain ⟨u, _, φ, hφ, htu⟩ := isCompact_Icc.tendsto_subseq ht
  have hlim := tendsto_nat_mul_stepCharFun_defect_subseq hb
    (hjtop.comp hφ.tendsto_atTop) htu
  have hdiv : Tendsto (fun k : ℕ => (φ k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_mono (fun k => le_add_of_nonneg_right zero_le_one)
      (tendsto_natCast_atTop_atTop.comp hφ.tendsto_atTop)
  have hbound : ∀ᶠ k in atTop, (φ k : ℝ) + 1 ≤
      (j (φ k) : ℝ) * (1 - ‖stepCharFun ν (t (φ k) / b (j (φ k)))‖ ^ 2) :=
    Eventually.of_forall fun k => (hgt (φ k)).le
  exact not_tendsto_nhds_of_tendsto_atTop (tendsto_atTop_mono' _ hbound hdiv) _ hlim

/-- The law of the difference of two independent copies of the step. -/
noncomputable def symmetrizedLaw (ν : Measure ℤ) : Measure ℝ :=
  (ν.map (fun z : ℤ => (z : ℝ))) ∗
    ((ν.map (fun z : ℤ => (z : ℝ))).map (fun x : ℝ => -x))

instance symmetrizedLaw_isProbabilityMeasure (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    IsProbabilityMeasure (symmetrizedLaw ν) := by
  unfold symmetrizedLaw
  infer_instance

/-- The symmetrized CF is the squared modulus of the original CF. -/
theorem charFun_symmetrizedLaw (ν : Measure ℤ) [IsProbabilityMeasure ν] (t : ℝ) :
    charFun (symmetrizedLaw ν) t = (‖stepCharFun ν t‖ ^ 2 : ℝ) := by
  unfold symmetrizedLaw
  rw [charFun_conv]
  have href : charFun ((ν.map (fun z : ℤ => (z : ℝ))).map (fun x : ℝ => -x)) t =
      conj (stepCharFun ν t) := by
    simpa [stepCharFun] using
      (charFun_map_mul (μ := ν.map (fun z : ℤ => (z : ℝ))) (-1) t)
  rw [href]
  change stepCharFun ν t * conj (stepCharFun ν t) = _
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- Product-law realization of the independent difference. -/
theorem symmetrizedLaw_eq_map (ν : Measure ℤ) :
    symmetrizedLaw ν = (ν.prod ν).map (fun p : ℤ × ℤ => (p.1 : ℝ) - (p.2 : ℝ)) := by
  have href : (ν.map (fun z : ℤ => (z : ℝ))).map (fun x : ℝ => -x) =
      ν.map (fun z : ℤ => -(z : ℝ)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [symmetrizedLaw, href, Measure.conv,
    Measure.map_prod_map ν ν (by fun_prop) (by fun_prop),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1

/-- Gaussian-smoothed squared-step defect. -/
noncomputable def smoothing (ν : Measure ℤ) (s : ℝ) : ℝ :=
  ∫ x, 1 - Real.exp (-s * x ^ 2) ∂(symmetrizedLaw ν)

private theorem smoothing_integrand_bounds {s x : ℝ} (hs : 0 ≤ s) :
    0 ≤ 1 - Real.exp (-s * x ^ 2) ∧ 1 - Real.exp (-s * x ^ 2) ≤ 1 := by
  have he :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs) (sq_nonneg x))
  have hp := Real.exp_pos (-s * x ^ 2)
  constructor <;> linarith

/-- The smoothing integrand is bounded and integrable for every nonnegative parameter. -/
theorem integrable_smoothing (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 ≤ s) :
    Integrable (fun x : ℝ => 1 - Real.exp (-s * x ^ 2)) (symmetrizedLaw ν) := by
  refine Integrable.of_bound (by fun_prop) 1 ?_
  exact ae_of_all _ fun x => by
    rw [Real.norm_of_nonneg (smoothing_integrand_bounds (x := x) hs).1]
    exact (smoothing_integrand_bounds hs).2

/-- The smoothing takes values in the unit interval. -/
theorem smoothing_bounds (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 ≤ s) : 0 ≤ smoothing ν s ∧ smoothing ν s ≤ 1 := by
  constructor
  · exact integral_nonneg fun x => (smoothing_integrand_bounds hs).1
  · have h := integral_mono (integrable_smoothing ν hs)
      (integrable_const (1 : ℝ)) (fun x => (smoothing_integrand_bounds hs).2)
    simpa [smoothing] using h

/-- Smoothing is monotone, the property needed to interpolate between adjacent scales. -/
theorem smoothing_mono (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {s r : ℝ} (hs : 0 ≤ s) (hsr : s ≤ r) : smoothing ν s ≤ smoothing ν r := by
  apply integral_mono (integrable_smoothing ν hs) (integrable_smoothing ν (hs.trans hsr))
  intro x
  have h := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hsr) (sq_nonneg x))
  linarith

@[simp] theorem smoothing_zero (ν : Measure ℤ) : smoothing ν 0 = 0 := by
  simp [smoothing]

/-- Elementary telescoping bound on powers in the closed complex unit disk. -/
theorem norm_pow_sub_one_le {z : ℂ} (hz : ‖z‖ ≤ 1) (k : ℕ) :
    ‖z ^ k - 1‖ ≤ (k : ℝ) * ‖z - 1‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hid : z ^ (k + 1) - 1 = z * (z ^ k - 1) + (z - 1) := by ring
    rw [hid]
    calc
      ‖z * (z ^ k - 1) + (z - 1)‖ ≤ ‖z * (z ^ k - 1)‖ + ‖z - 1‖ := norm_add_le _ _
      _ ≤ (k : ℝ) * ‖z - 1‖ + ‖z - 1‖ := by
        rw [norm_mul]
        have h := (mul_le_of_le_one_left (norm_nonneg (z ^ k - 1)) hz).trans ih
        linarith
      _ = ((k + 1 : ℕ) : ℝ) * ‖z - 1‖ := by push_cast; ring

/-- The pointwise quadratic integer-multiple bound behind CF domination. -/
theorem one_sub_re_pow_le {z : ℂ} (hz : ‖z‖ = 1) (k : ℕ) :
    1 - (z ^ k).re ≤ (k : ℝ) ^ 2 * (1 - z.re) := by
  have hn := norm_pow_sub_one_le hz.le k
  have hs := sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg k) (norm_nonneg _)) |>.mpr hn
  have hid (w : ℂ) (hw : ‖w‖ = 1) : ‖w - 1‖ ^ 2 = 2 * (1 - w.re) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp [Complex.normSq_eq_norm_sq, hw]
    ring
  rw [mul_pow, hid z hz, hid (z ^ k) (by simp [norm_pow, hz])] at hs
  nlinarith

private theorem integrable_phase (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ => cexp ((t * x : ℝ) * I)) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  simp [Complex.norm_exp]

private theorem defect_eq_integral (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    1 - (charFun μ t).re = ∫ x : ℝ, 1 - (cexp ((t * x : ℝ) * I)).re ∂μ := by
  change 1 - RCLike.re (charFun μ t) = ∫ x : ℝ, 1 - RCLike.re (cexp ((t * x : ℝ) * I)) ∂μ
  rw [integral_sub (integrable_const _) (integrable_phase μ t).re,
    integral_re (integrable_phase μ t)]
  simp [charFun_apply_real]

/-- Quadratic control of the real CF defect at integer multiples. -/
theorem one_sub_re_charFun_nat_mul_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℝ) (k : ℕ) :
    1 - (charFun μ ((k : ℝ) * t)).re ≤ (k : ℝ) ^ 2 * (1 - (charFun μ t).re) := by
  rw [defect_eq_integral, defect_eq_integral, ← integral_const_mul]
  apply integral_mono ((integrable_const _).sub (integrable_phase μ _).re)
    (((integrable_const _).sub (integrable_phase μ _).re).const_mul _)
  intro x
  have heq : cexp ((((k : ℝ) * t) * x : ℝ) * I) = cexp ((t * x : ℝ) * I) ^ k := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  change 1 - (cexp ((((k : ℝ) * t) * x : ℝ) * I)).re ≤
    (k : ℝ) ^ 2 * (1 - (cexp ((t * x : ℝ) * I)).re)
  rw [heq]
  exact one_sub_re_pow_le (by simp [Complex.norm_exp]) k

/-- Integer-multiple control specialized to the symmetrized step law. -/
theorem stepCharFun_defect_nat_mul_le (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (t : ℝ) (k : ℕ) :
    1 - ‖stepCharFun ν ((k : ℝ) * t)‖ ^ 2 ≤
      (k : ℝ) ^ 2 * (1 - ‖stepCharFun ν t‖ ^ 2) := by
  simpa only [charFun_symmetrizedLaw, Complex.ofReal_re] using
    one_sub_re_charFun_nat_mul_le (symmetrizedLaw ν) t k

/-- A global quadratic bound, uniform in the walk length after a fixed threshold. -/
theorem eventually_stepCharFun_defect_le_quadratic
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ t : ℝ,
      (n : ℝ) * (1 - ‖stepCharFun ν (t / b n)‖ ^ 2) ≤ C * (1 + t ^ 2) := by
  obtain ⟨C, hC, N, hN⟩ := eventually_stepCharFun_defect_le_on_Icc hb 1
  refine ⟨8 * C, by positivity, N, fun n hn t => ?_⟩
  let k : ℕ := ⌈|t|⌉₊ + 1
  have hkpos : 0 < (k : ℝ) := by dsimp [k]; positivity
  have hkle : (k : ℝ) ≤ |t| + 2 := by
    have h := Nat.ceil_lt_add_one (abs_nonneg t)
    dsimp [k]
    push_cast
    linarith
  have htlt : |t| ≤ (k : ℝ) := by
    have h := Nat.le_ceil |t|
    dsimp [k]
    push_cast
    linarith
  have hmem : t / (k : ℝ) ∈ Icc (-1 : ℝ) 1 := by
    have habs : |t / (k : ℝ)| ≤ 1 := by
      rw [abs_div, abs_of_pos hkpos, div_le_one hkpos]
      exact htlt
    exact abs_le.mp habs
  have hlocal := hN n hn (t / k) hmem
  have hmul := stepCharFun_defect_nat_mul_le ν ((t / k) / b n) k
  have heq : (k : ℝ) * ((t / k) / b n) = t / b n := by
    field_simp
  rw [heq] at hmul
  have h1 := mul_le_mul_of_nonneg_left hmul (Nat.cast_nonneg n)
  have h2 := mul_le_mul_of_nonneg_left hlocal (sq_nonneg (k : ℝ))
  have hksq : (k : ℝ) ^ 2 ≤ 8 * (1 + t ^ 2) := by
    have hsq : (k : ℝ) ^ 2 ≤ (|t| + 2) ^ 2 := sq_le_sq₀ hkpos.le (by positivity) |>.mpr hkle
    have habs := sq_abs t
    nlinarith [sq_nonneg (|t| - 2)]
  have h3 := mul_le_mul_of_nonneg_right hksq hC.le
  nlinarith

private theorem integrable_cos (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    Integrable (fun x : ℝ => Real.cos (t * x)) μ := by
  refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
  simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (t * x)

private theorem re_charFun_eq_integral_cos (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    (charFun μ t).re = ∫ x : ℝ, Real.cos (t * x) ∂μ := by
  have h := integral_re (integrable_phase μ t)
  change (∫ x : ℝ, (cexp ((t * x : ℝ) * I)).re ∂μ) =
    (∫ x : ℝ, cexp ((t * x : ℝ) * I) ∂μ).re at h
  simp only [Complex.exp_ofReal_mul_I_re] at h
  simpa only [charFun_apply_real, ← Complex.ofReal_mul] using h.symm

private theorem integral_cos_gaussian (t : ℝ) :
    (∫ x : ℝ, Real.cos (t * x) ∂(gaussianReal 0 2)) = Real.exp (-t ^ 2) := by
  rw [← re_charFun_eq_integral_cos, charFun_gaussianReal]
  have heq : (t : ℂ) * (0 : ℂ) * I - (2 : ℂ) * (t : ℂ) ^ 2 / 2 = ((-t ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  norm_num only [NNReal.coe_zero, NNReal.coe_ofNat, Complex.ofReal_zero, Complex.ofReal_ofNat] at *
  rw [heq, Complex.exp_ofReal_re]

/-- Gaussian Fourier smoothing, expressed against the probability law `N(0,2)`. -/
theorem smoothing_eq_gaussian_integral (ν : Measure ℤ) [IsProbabilityMeasure ν] (a : ℝ) :
    smoothing ν (a ^ 2) =
      ∫ t : ℝ, 1 - ‖stepCharFun ν (a * t)‖ ^ 2 ∂(gaussianReal 0 2) := by
  have hprod : Integrable (fun p : ℝ × ℝ => Real.cos (a * p.1 * p.2))
      ((gaussianReal 0 2).prod (symmetrizedLaw ν)) := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun p => ?_)
    simpa only [Real.norm_eq_abs] using Real.abs_cos_le_one (a * p.1 * p.2)
  have hswap := integral_integral_swap (f := fun t x : ℝ => Real.cos (a * t * x)) hprod
  have hinner (x : ℝ) : (∫ t : ℝ, Real.cos (a * t * x) ∂(gaussianReal 0 2)) =
      Real.exp (-(a ^ 2 * x ^ 2)) := by
    have heq : (fun t : ℝ => Real.cos (a * t * x)) = fun t => Real.cos ((a * x) * t) := by
      funext t
      congr 1
      ring
    rw [heq, integral_cos_gaussian]
    congr 1
    ring
  have hcf (t : ℝ) : ‖stepCharFun ν (a * t)‖ ^ 2 =
      ∫ x : ℝ, Real.cos (a * t * x) ∂(symmetrizedLaw ν) := by
    rw [← re_charFun_eq_integral_cos, charFun_symmetrizedLaw, Complex.ofReal_re]
  have hi : Integrable (fun t : ℝ => ‖stepCharFun ν (a * t)‖ ^ 2) (gaussianReal 0 2) := by
    refine Integrable.of_bound ?_ 1 (ae_of_all _ fun t => ?_)
    · exact ((continuous_charFun (μ := ν.map (fun z : ℤ => (z : ℝ)))).comp
        (continuous_const.mul continuous_id)).norm.pow 2 |>.aestronglyMeasurable
    · rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)
  have hexp : Integrable (fun x : ℝ => Real.exp (-(a ^ 2 * x ^ 2))) (symmetrizedLaw ν) := by
    refine Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun x => ?_)
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sq_nonneg a) (sq_nonneg x)))
  unfold smoothing
  simp_rw [neg_mul]
  rw [integral_sub (integrable_const _) hexp, integral_sub (integrable_const _) hi]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  congr 1
  simpa only [hcf, hinner] using hswap.symm

/-- Integrating the scaled CF defects gives the Gaussian integral limit. -/
theorem tendsto_nat_mul_smoothing
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) (a : ℝ) :
    Tendsto (fun (n : ℕ) => (n : ℝ) * smoothing ν ((a / b n) ^ 2)) atTop
      (𝓝 (∫ t : ℝ, -2 * Real.cos (Real.pi * θ / 2) * |a * t| ^ θ
        ∂(gaussianReal 0 2))) := by
  obtain ⟨C, hC, N, hN⟩ := eventually_stepCharFun_defect_le_quadratic hb
  have hmoment : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 2) := by
    simpa only [Real.norm_eq_abs, sq_abs, id_eq] using
      (memLp_id_gaussianReal (μ := 0) (v := 2) 2).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hdom : Integrable (fun t : ℝ => C * (1 + (a * t) ^ 2)) (gaussianReal 0 2) := by
    have h := ((integrable_const (1 : ℝ)).add (hmoment.const_mul (a ^ 2))).const_mul C
    simpa only [mul_pow, Pi.add_apply] using h
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := gaussianReal 0 2) (F := fun (n : ℕ) (t : ℝ) =>
      (n : ℝ) * (1 - ‖stepCharFun ν ((a * t) / b n)‖ ^ 2))
    (fun t : ℝ => C * (1 + (a * t) ^ 2))
    (Eventually.of_forall fun n => by
      apply Continuous.aestronglyMeasurable
      unfold stepCharFun
      fun_prop)
    ((eventually_ge_atTop N).mono fun n hn => ae_of_all _ fun t => by
      rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg n) ?_)]
      · exact hN n hn (a * t)
      · exact sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)))
    hdom (ae_of_all _ fun t => tendsto_nat_mul_stepCharFun_defect hb (a * t))
  convert hlim using 1
  funext n
  rw [smoothing_eq_gaussian_integral, ← integral_const_mul]
  congr 1
  funext t
  have heq : a / b n * t = a * t / b n := by ring
  rw [heq]

/-- The positive finite smoothing constant; no Gamma evaluation is needed. -/
noncomputable def smoothingConstant (θ : ℝ) : ℝ :=
  -2 * Real.cos (Real.pi * θ / 2) *
    ∫ t : ℝ, |t| ^ θ ∂(gaussianReal 0 2)

private theorem integrable_gaussian_abs_rpow {θ : ℝ} (hθ : 0 ≤ θ) :
    Integrable (fun t : ℝ => |t| ^ θ) (gaussianReal 0 2) := by
  simpa only [id_eq, Real.norm_eq_abs, ENNReal.toReal_ofReal hθ] using
    (memLp_id_gaussianReal' (μ := 0) (v := 2) (ENNReal.ofReal θ) (by simp)).integrable_norm_rpow'

/-- Strict positivity of the Gaussian moment gives strict positivity of the constant. -/
theorem smoothingConstant_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    0 < smoothingConstant θ := by
  have : NullSingletonClass (gaussianReal 0 2) := nullSingletonClass_gaussianReal (by norm_num)
  have hi := integrable_gaussian_abs_rpow (by linarith [hθ.1] : 0 ≤ θ)
  have hmoment : 0 < ∫ t : ℝ, |t| ^ θ ∂(gaussianReal 0 2) := by
    apply (integral_pos_iff_support_of_nonneg (fun t => Real.rpow_nonneg (abs_nonneg t) θ) hi).mpr
    have hs : Function.support (fun t : ℝ => |t| ^ θ) = {0}ᶜ := by
      ext t
      simp only [Function.mem_support, mem_compl_iff, mem_singleton_iff]
      rw [Real.rpow_ne_zero (abs_nonneg t) (by linarith [hθ.1] : θ ≠ 0), abs_ne_zero]
    rw [hs, measure_compl (measurableSet_singleton 0) (by simp)]
    simp
  exact mul_pos (by linarith [cos_pi_mul_div_two_neg hθ]) hmoment

/-- The Gaussian integral limit with its homogeneous constant factored out. -/
theorem tendsto_nat_mul_smoothing_rpow
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) (a : ℝ) :
    Tendsto (fun (n : ℕ) => (n : ℝ) * smoothing ν ((a / b n) ^ 2)) atTop
      (𝓝 (smoothingConstant θ * |a| ^ θ)) := by
  have h := tendsto_nat_mul_smoothing hb a
  have heq : (∫ t : ℝ, -2 * Real.cos (Real.pi * θ / 2) * |a * t| ^ θ
      ∂(gaussianReal 0 2)) = smoothingConstant θ * |a| ^ θ := by
    simp_rw [abs_mul, Real.mul_rpow (abs_nonneg a) (abs_nonneg _)]
    simp_rw [← mul_assoc]
    rw [integral_const_mul]
    unfold smoothingConstant
    ring
  rwa [heq] at h

/-- The scale form consumed by the domain-of-attraction converse. -/
theorem tendsto_nat_mul_smoothing_div_sq
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) {r : ℝ} (hr : 0 < r) :
    Tendsto (fun (n : ℕ) => (n : ℝ) * smoothing ν (r / b n ^ 2)) atTop
      (𝓝 (smoothingConstant θ * r ^ (θ / 2))) := by
  have h := tendsto_nat_mul_smoothing_rpow hb (Real.sqrt r)
  simp_rw [div_pow, Real.sq_sqrt hr.le] at h
  rw [abs_of_nonneg (Real.sqrt_nonneg r)] at h
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hr.le] at h
  have he : (1 / 2 : ℝ) * θ = θ / 2 := by ring
  rwa [he] at h

/-- Gaussian smoothing limits remain valid under moving scales and time changes. -/
theorem tendsto_nat_mul_smoothing_moving
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) {j : ℕ → ℕ} (hj : Tendsto j atTop atTop)
    {a : ℕ → ℝ} {u : ℝ} (ha : Tendsto a atTop (𝓝 u)) :
    Tendsto (fun (n : ℕ) => (j n : ℝ) * smoothing ν ((a n / b (j n)) ^ 2)) atTop
      (𝓝 (smoothingConstant θ * |u| ^ θ)) := by
  obtain ⟨C, hC, N, hN⟩ := eventually_stepCharFun_defect_le_quadratic hb
  have haB : ∀ᶠ n in atTop, |a n| ≤ |u| + 1 :=
    (ha.norm.eventually (gt_mem_nhds (lt_add_one ‖u‖))).mono fun n hn => hn.le
  have hmoment : Integrable (fun t : ℝ => t ^ 2) (gaussianReal 0 2) := by
    simpa only [Real.norm_eq_abs, sq_abs, id_eq] using
      (memLp_id_gaussianReal (μ := 0) (v := 2) 2).integrable_norm_pow (by norm_num : 2 ≠ 0)
  have hdom : Integrable (fun t : ℝ => C * (1 + (|u| + 1) ^ 2 * t ^ 2)) (gaussianReal 0 2) := by
    simpa only [Pi.add_apply] using
      ((integrable_const (1 : ℝ)).add (hmoment.const_mul ((|u| + 1) ^ 2))).const_mul C
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := gaussianReal 0 2) (F := fun (n : ℕ) (t : ℝ) =>
      (j n : ℝ) * (1 - ‖stepCharFun ν ((a n * t) / b (j n))‖ ^ 2))
    (fun t : ℝ => C * (1 + (|u| + 1) ^ 2 * t ^ 2))
    (Eventually.of_forall fun n => by
      apply Continuous.aestronglyMeasurable
      unfold stepCharFun
      fun_prop)
    (by
      filter_upwards [hj.eventually_ge_atTop N, haB] with n hn han
      exact ae_of_all _ fun t => by
        rw [Real.norm_of_nonneg (mul_nonneg (Nat.cast_nonneg _) ?_)]
        · apply (hN (j n) hn (a n * t)).trans
          apply mul_le_mul_of_nonneg_left _ hC.le
          have hs : (a n) ^ 2 ≤ (|u| + 1) ^ 2 := by
            have h := (sq_le_sq₀ (abs_nonneg (a n)) (by positivity)).mpr han
            simpa only [sq_abs] using h
          have h := mul_le_mul_of_nonneg_right hs (sq_nonneg t)
          nlinarith
        · exact sub_nonneg.mpr (pow_le_one₀ (norm_nonneg _) (norm_charFun_le_one _)))
    hdom (ae_of_all _ fun t => tendsto_nat_mul_stepCharFun_defect_subseq hb hj (ha.mul_const t))
  have heq : (∫ t : ℝ, -2 * Real.cos (Real.pi * θ / 2) * |u * t| ^ θ
      ∂(gaussianReal 0 2)) = smoothingConstant θ * |u| ^ θ := by
    simp_rw [abs_mul, Real.mul_rpow (abs_nonneg u) (abs_nonneg _), ← mul_assoc]
    rw [integral_const_mul]
    unfold smoothingConstant
    ring
  rw [heq] at hlim
  convert hlim using 1
  funext n
  rw [smoothing_eq_gaussian_integral, ← integral_const_mul]
  congr 1
  funext t
  have heq : a n / b (j n) * t = a n * t / b (j n) := by ring
  rw [heq]

/-- A sequence with asymptotically unit adjacent ratios has asymptotically exact
first crossings, even if it is not monotone. -/
theorem exists_scale_indices {b : ℕ → ℝ}
    (hb : Tendsto b atTop atTop) (hpos : ∀ᶠ n in atTop, 0 < b n)
    (hsucc : Tendsto (fun n => b (n + 1) / b n) atTop (𝓝 1))
    {x : ℕ → ℝ} (hx : Tendsto x atTop atTop) :
    ∃ j : ℕ → ℕ, Tendsto j atTop atTop ∧
      Tendsto (fun n => b (j n) / x n) atTop (𝓝 1) := by
  classical
  have hex (n : ℕ) : ∃ k, x n ≤ b k := (hb.eventually_ge_atTop (x n)).exists
  let j : ℕ → ℕ := fun n => Nat.find (hex n)
  have hjbound (n : ℕ) : x n ≤ b (j n) := Nat.find_spec (hex n)
  have hjtop : Tendsto j atTop atTop := by
    apply tendsto_atTop.2
    intro K
    let M := (Finset.range (K + 1)).sup' (by simp) b
    filter_upwards [hx.eventually_gt_atTop M] with n hn
    by_contra h
    have hjK : j n ∈ Finset.range (K + 1) := by simp; omega
    have hM : b (j n) ≤ M := Finset.le_sup' b hjK
    linarith [hjbound n]
  have hpredtop : Tendsto (fun n => j n - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [hjtop.eventually_ge_atTop (K + 1)] with n hn
    omega
  have hratio : Tendsto (fun n => b (j n) / b (j n - 1)) atTop (𝓝 1) := by
    refine (hsucc.comp hpredtop).congr' ?_
    filter_upwards [hjtop.eventually_ge_atTop 1] with n hn
    dsimp only [Function.comp_def]
    rw [Nat.sub_add_cancel hn]
  refine ⟨j, hjtop, tendsto_const_nhds.squeeze' hratio ?_ ?_⟩
  · filter_upwards [hx.eventually_gt_atTop 0] with n hn
    exact (one_le_div hn).mpr (hjbound n)
  · filter_upwards [hx.eventually_gt_atTop 0, hjtop.eventually_ge_atTop 1,
      hpredtop.eventually hpos] with n hxn hjn hpn
    have hprev : b (j n - 1) < x n := by
      exact lt_of_not_ge (Nat.find_min (hex n) (by change j n - 1 < j n; omega))
    exact div_le_div_of_nonneg_left (hxn.le.trans (hjbound n)) hpn hprev.le

/-- Continuum scale ratios, first stated at infinity in the inverse scale variable. -/
theorem tendsto_smoothing_ratio_inv_sq
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℝ => smoothing ν (c / x ^ 2) / smoothing ν (1 / x ^ 2)) atTop
      (𝓝 (c ^ (θ / 2))) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro x hx
  have hbpos : ∀ᶠ n in atTop, 0 < b n := by
    obtain ⟨N, hN⟩ := hb.pos
    exact (eventually_ge_atTop N).mono hN
  obtain ⟨j, hj, hscale⟩ := exists_scale_indices
    (TransformConvergence.tendsto_atTop ν hb) hbpos
    (TransformConvergence.tendsto_succ_div ν hb) hx
  have hlim (r : ℝ) (hr : 0 < r) :
      Tendsto (fun n : ℕ => (j n : ℝ) * smoothing ν (r / x n ^ 2)) atTop
        (𝓝 (smoothingConstant θ * r ^ (θ / 2))) := by
    have h := tendsto_nat_mul_smoothing_moving hb hj (hscale.const_mul (Real.sqrt r))
    have he : |Real.sqrt r * 1| ^ θ = r ^ (θ / 2) := by
      rw [mul_one, abs_of_nonneg (Real.sqrt_nonneg r), Real.sqrt_eq_rpow,
        ← Real.rpow_mul hr.le]
      congr 1
      ring
    rw [he] at h
    refine h.congr' ?_
    filter_upwards [hj.eventually hbpos, hx.eventually_gt_atTop 0] with n hn hxn
    congr 2
    field_simp
    nlinarith [Real.sq_sqrt hr.le]
  have hden := hlim 1 one_pos
  simp only [Real.one_rpow, mul_one] at hden
  have hquot := (hlim c hc).div hden (smoothingConstant_pos hb.alpha_mem).ne'
  have hvalue : smoothingConstant θ * c ^ (θ / 2) / smoothingConstant θ = c ^ (θ / 2) :=
    mul_div_cancel_left₀ _ (smoothingConstant_pos hb.alpha_mem).ne'
  rw [hvalue] at hquot
  refine hquot.congr' ?_
  filter_upwards [hj.eventually_ge_atTop 1] with n hn
  dsimp only [Function.comp_def, Pi.div_apply]
  exact mul_div_mul_left _ _ (by exact_mod_cast (show j n ≠ 0 by omega))

/-- Gaussian-smoothed converse: the smoothed symmetrized squared-step defect is
regularly varying at zero from the right, with index `θ / 2`.
This conclusion holds for arbitrary eventually positive attracting normings. -/
theorem smoothing_regularlyVarying_zero
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ m b) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun s : ℝ => smoothing ν (c * s) / smoothing ν s) (𝓝[>] 0)
      (𝓝 (c ^ (θ / 2))) := by
  have hx : Tendsto (fun s : ℝ => Real.sqrt (s⁻¹)) (𝓝[>] 0) atTop :=
    Real.tendsto_sqrt_atTop.comp tendsto_inv_nhdsGT_zero
  refine ((tendsto_smoothing_ratio_inv_sq hb hc).comp hx).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with s hs
  have hspos : 0 < s := hs
  dsimp only [Function.comp_def]
  rw [Real.sq_sqrt (inv_nonneg.mpr hspos.le), div_inv_eq_mul, div_inv_eq_mul, one_mul]

end BGW.StableTrees.Attraction.GaussianSmoothing
