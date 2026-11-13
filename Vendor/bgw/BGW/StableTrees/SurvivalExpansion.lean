/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SurvivalBasic
public import BGW.StableTrees.Attraction.DomainCriterion
public import BGW.StableTrees.Attraction.CanonicalAttraction
import BGW.StableTrees.Attraction.StableDomainTail
import BGW.StableTrees.Attraction.GaussianBranch
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# The offspring generating-function expansion at the stable scale

The stable Laplace asymptotic is transferred from the canonical norming to any attracting
norming, and then from the exponential generating function to its real argument `1 - λ / Bₙ`.
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology ENNReal

namespace BGW.StableTrees.Survival

open BGW.StableTrees.Attraction
open BGW.StableTrees.Attraction.LaplaceExpansion

private theorem realGF_eq_integral (μ : PMF ℕ) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    realGF μ s = ∫ k : ℕ, s ^ k ∂μ.toMeasure := by
  have hi : Integrable (fun k : ℕ => s ^ k) μ.toMeasure := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with k
    rw [Real.norm_of_nonneg (pow_nonneg hs0 k)]
    exact pow_le_one₀ hs0 hs1
  rw [PMF.integral_eq_tsum μ _ hi]
  rfl

private theorem centeredLaplace_stepLaw_eq (μ : PMF ℕ) (hc : IsCritical μ)
    {u : ℝ} (hu : 0 ≤ u) :
    centeredLaplace (stepLaw μ) u = Real.exp u * realGF μ (Real.exp (-u)) := by
  rw [centeredLaplace_eq, mean_stepLaw hc]
  simp only [mul_zero, Real.exp_zero, one_mul]
  rw [stepLaw, integral_map (measurable_of_countable _).aemeasurable (by fun_prop)]
  have hi : Integrable (fun k : ℕ => Real.exp (-u * (((k : ℤ) - 1 : ℤ) : ℝ)))
      μ.toMeasure := by
    apply Integrable.of_bound (by fun_prop) (Real.exp u)
    filter_upwards [] with k
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply Real.exp_le_exp.mpr
    simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg hu (by linarith : (0 : ℝ) ≤ (k : ℝ) + 1)]
  rw [PMF.integral_eq_tsum μ _ hi, realGF]
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  simp only [smul_eq_mul, Int.cast_sub, Int.cast_natCast, Int.cast_one]
  rw [← Real.exp_nat_mul]
  calc
    (μ k).toReal * Real.exp (-u * ((k : ℝ) - 1)) =
        (μ k).toReal * (Real.exp u * Real.exp ((k : ℝ) * -u)) := by
      congr 1
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp u * ((μ k).toReal * Real.exp ((k : ℝ) * -u)) := by ring

private theorem centeredLaplace_sub_one_monotoneOn (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hstep : ν {z : ℤ | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) :
    MonotoneOn (fun u => centeredLaplace ν u - 1) (Set.Ici 0) := by
  intro u hu v hv huv
  have hu0 : 0 ≤ u := hu
  have hv0 : 0 ≤ v := hv
  change centeredLaplace ν u - 1 ≤ centeredLaplace ν v - 1
  rw [centeredLaplace_sub_one_eq_integral hstep hint hu0,
    centeredLaplace_sub_one_eq_integral hstep hint hv0]
  apply integral_mono
  · exact ((centeredLaplace_integrable hstep hu0).sub (integrable_const 1)).add
      ((hint.sub (integrable_const _)).const_mul u)
  · exact ((centeredLaplace_integrable hstep hv0).sub (integrable_const 1)).add
      ((hint.sub (integrable_const _)).const_mul v)
  · intro z
    set a : ℝ := (z : ℝ) - mean ν
    have he : 1 + (-(v - u) * a) ≤ Real.exp (-(v - u) * a) := by
      simpa [add_comm] using Real.add_one_le_exp (-(v - u) * a)
    have he' := mul_le_mul_of_nonneg_left he (Real.exp_nonneg (-u * a))
    have hsign : 0 ≤ (v - u) * a * (1 - Real.exp (-u * a)) := by
      by_cases ha : 0 ≤ a
      · have hexp : Real.exp (-u * a) ≤ 1 := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by nlinarith)
        exact mul_nonneg (mul_nonneg (sub_nonneg.mpr huv) ha) (sub_nonneg.mpr hexp)
      · have ha' : a ≤ 0 := le_of_not_ge ha
        have hmul : (v - u) * a ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr huv) ha'
        have hexp : 1 ≤ Real.exp (-u * a) := by
          rw [← Real.exp_zero]
          exact Real.exp_le_exp.mpr (by nlinarith)
        exact mul_nonneg_of_nonpos_of_nonpos hmul (sub_nonpos.mpr hexp)
    rw [← Real.exp_add] at he'
    have hsum : -u * a + -(v - u) * a = -v * a := by ring
    rw [hsum] at he'
    dsimp only
    change Real.exp (-u * a) - 1 + u * a ≤ Real.exp (-v * a) - 1 + v * a
    ring_nf at he' hsign ⊢
    nlinarith

private theorem tendsto_centeredLaplace_of_norming_equivalent
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ} {A b : ℕ → ℝ}
    (hstep : ν {z : ℤ | z < -1} = 0) (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hA : ∀ c : ℝ, 0 < c → Tendsto (fun n : ℕ => (n : ℝ) *
      (centeredLaplace ν (c / A n) - 1)) atTop (𝓝 (c ^ θ)))
    (hr : Tendsto (fun n => A n / b n) atTop (𝓝 1))
    (hApos : ∀ᶠ n in atTop, 0 < A n) (hbpos : ∀ᶠ n in atTop, 0 < b n)
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) * (centeredLaplace ν (lam / b n) - 1)) atTop
      (𝓝 (lam ^ θ)) := by
  have hmono := centeredLaplace_sub_one_monotoneOn ν hstep hint
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  have hc : ContinuousAt (fun c : ℝ => (lam * c) ^ θ) 1 := by
    apply (Real.continuousAt_rpow_const (lam * 1) θ
      (Or.inl (mul_ne_zero hlam.ne' one_ne_zero))).comp
    exact continuousAt_const.mul continuousAt_id
  have hnh : {c : ℝ | dist ((lam * c) ^ θ) ((lam * 1) ^ θ) < ε / 2} ∈ 𝓝 1 :=
    hc (Metric.ball_mem_nhds _ (half_pos hε))
  obtain ⟨r, hr0, hball⟩ := Metric.mem_nhds_iff.mp hnh
  let d := min r 1
  have hd : 0 < d := lt_min hr0 one_pos
  let c₁ : ℝ := 1 - d / 2
  let c₂ : ℝ := 1 + d / 2
  have hc₁ : 0 < c₁ := by dsimp [c₁, d]; linarith [min_le_right r 1]
  have hc₂ : 0 < c₂ := by dsimp [c₂]; linarith
  have hdist₁ : dist c₁ 1 < r := by
    rw [Real.dist_eq]
    dsimp [c₁, d]
    have hmr : min r 1 ≤ r := min_le_left _ _
    have he : 1 - min r 1 / 2 - 1 = -(min r 1 / 2) := by ring
    rw [he, abs_neg, abs_of_pos (by positivity : 0 < min r 1 / 2)]
    linarith
  have hdist₂ : dist c₂ 1 < r := by
    rw [Real.dist_eq]
    dsimp [c₂, d]
    have hmr : min r 1 ≤ r := min_le_left _ _
    have he : 1 + min r 1 / 2 - 1 = min r 1 / 2 := by ring
    rw [he, abs_of_pos (by positivity : 0 < min r 1 / 2)]
    linarith
  have hclose₁ : dist ((lam * c₁) ^ θ) (lam ^ θ) < ε / 2 := by
    simpa using hball hdist₁
  have hclose₂ : dist ((lam * c₂) ^ θ) (lam ^ θ) < ε / 2 := by
    simpa using hball hdist₂
  have hl₁ := hA (lam * c₁) (mul_pos hlam hc₁)
  have hl₂ := hA (lam * c₂) (mul_pos hlam hc₂)
  have he₁ : ∀ᶠ n : ℕ in atTop, dist ((n : ℝ) *
      (centeredLaplace ν ((lam * c₁) / A n) - 1)) ((lam * c₁) ^ θ) < ε / 2 :=
    hl₁.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have he₂ : ∀ᶠ n : ℕ in atTop, dist ((n : ℝ) *
      (centeredLaplace ν ((lam * c₂) / A n) - 1)) ((lam * c₂) ^ θ) < ε / 2 :=
    hl₂.eventually (Metric.ball_mem_nhds _ (half_pos hε))
  have hre : ∀ᶠ n in atTop, A n / b n ∈ Set.Ioo c₁ c₂ := by
    apply hr.eventually
    exact Ioo_mem_nhds (by dsimp [c₁]; linarith) (by dsimp [c₂]; linarith)
  apply eventually_atTop.1
  filter_upwards [he₁, he₂, hre, hApos, hbpos] with n he₁n he₂n hrn hAn hbn
  have harg : lam / b n = lam * (A n / b n) / A n := by field_simp
  have hlo : (n : ℝ) * (centeredLaplace ν ((lam * c₁) / A n) - 1) ≤
      (n : ℝ) * (centeredLaplace ν (lam / b n) - 1) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    apply hmono
    · exact div_nonneg (mul_nonneg hlam.le hc₁.le) hAn.le
    · rw [harg]
      exact div_nonneg (mul_nonneg hlam.le (div_nonneg hAn.le hbn.le)) hAn.le
    · rw [harg]
      apply div_le_div_of_nonneg_right _ hAn.le
      exact mul_le_mul_of_nonneg_left hrn.1.le hlam.le
  have hhi : (n : ℝ) * (centeredLaplace ν (lam / b n) - 1) ≤
      (n : ℝ) * (centeredLaplace ν ((lam * c₂) / A n) - 1) := by
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
    apply hmono
    · rw [harg]
      exact div_nonneg (mul_nonneg hlam.le (div_nonneg hAn.le hbn.le)) hAn.le
    · exact div_nonneg (mul_nonneg hlam.le hc₂.le) hAn.le
    · rw [harg]
      apply div_le_div_of_nonneg_right _ hAn.le
      exact mul_le_mul_of_nonneg_left hrn.2.le hlam.le
  rw [Real.dist_eq] at he₁n he₂n hclose₁ hclose₂ ⊢
  rw [abs_lt] at he₁n he₂n hclose₁ hclose₂ ⊢
  constructor <;> linarith

private theorem realGF_one_sub_exp_bounds (μ : PMF ℕ) (hc : IsCritical μ)
    {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ 1 - realGF μ (Real.exp (-u)) ∧ 1 - realGF μ (Real.exp (-u)) ≤ u := by
  have hexp0 : 0 ≤ Real.exp (-u) := (Real.exp_pos _).le
  have hexp1 : Real.exp (-u) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hi : Integrable (fun k : ℕ => Real.exp (-u) ^ k) μ.toMeasure := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with k
    rw [Real.norm_of_nonneg (pow_nonneg hexp0 k)]
    exact pow_le_one₀ hexp0 hexp1
  have heq : 1 - realGF μ (Real.exp (-u)) =
      ∫ k : ℕ, (1 - Real.exp (-u) ^ k) ∂μ.toMeasure := by
    rw [realGF_eq_integral μ hexp0 hexp1, integral_sub (integrable_const 1) hi]
    simp
  rw [heq]
  constructor
  · apply integral_nonneg
    intro k
    exact sub_nonneg.mpr (pow_le_one₀ hexp0 hexp1)
  · have hmean : ∫ k : ℕ, (k : ℝ) ∂μ.toMeasure = 1 := Scalar.offspring_integral_eq_one hc
    have hki : Integrable (fun k : ℕ => (k : ℝ) * u) μ.toMeasure :=
      (integrable_offspring hc).mul_const u
    have hle : (∫ k : ℕ, (1 - Real.exp (-u) ^ k) ∂μ.toMeasure) ≤
        ∫ k : ℕ, (k : ℝ) * u ∂μ.toMeasure := by
      apply integral_mono ((integrable_const 1).sub hi) hki
      intro k
      change 1 - Real.exp (-u) ^ k ≤ (k : ℝ) * u
      rw [← Real.exp_nat_mul]
      have he := Real.add_one_le_exp (-u * (k : ℝ))
      have he' : 1 - Real.exp (-u * (k : ℝ)) ≤ u * (k : ℝ) := by linarith
      convert he' using 1 <;> ring_nf
    rw [integral_mul_const, hmean, one_mul] at hle
    exact hle

private theorem realGF_exp_error_bounds (μ : PMF ℕ) (hc : IsCritical μ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    0 ≤ realGF μ (Real.exp (-u)) - realGF μ (1 - u) + (Real.exp u - 1 - u) ∧
      realGF μ (Real.exp (-u)) - realGF μ (1 - u) + (Real.exp u - 1 - u) ≤ 2 * u ^ 2 := by
  let a := Real.exp (-u)
  let b := 1 - u
  let r := Real.exp u - 1 - u
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have ha1 : a ≤ 1 := by
    dsimp [a]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by linarith)
  have hb0 : 0 ≤ b := sub_nonneg.mpr hu1
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hba : b ≤ a := by
    have he := Real.add_one_le_exp (-u)
    dsimp [a, b]
    linarith
  have hr0 : 0 ≤ r := by
    have he := Real.add_one_le_exp u
    dsimp [r]
    linarith
  have hr : r ≤ u ^ 2 := by
    have he := Real.norm_exp_sub_one_sub_id_le (x := u) (by simpa [abs_of_nonneg hu0] using hu1)
    rw [Real.norm_eq_abs, abs_of_nonneg hr0] at he
    simpa [Real.norm_of_nonneg hu0] using he
  have hab : a - b ≤ u ^ 2 := by
    have he := Real.norm_exp_sub_one_sub_id_le (x := -u)
      (by simpa [abs_neg, abs_of_nonneg hu0] using hu1)
    have he_abs : |a - b| ≤ ‖-u‖ ^ 2 := by
      convert he using 1
      congr 1
      dsimp [a, b]
      ring
    rw [abs_of_nonneg (sub_nonneg.mpr hba)] at he_abs
    simpa [Real.norm_of_nonneg hu0] using he_abs
  have hi (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
      Integrable (fun k : ℕ => s ^ k) μ.toMeasure := by
    apply Integrable.of_bound (by fun_prop) 1
    filter_upwards [] with k
    rw [Real.norm_of_nonneg (pow_nonneg hs0 k)]
    exact pow_le_one₀ hs0 hs1
  have hmean : ∫ k : ℕ, (k : ℝ) ∂μ.toMeasure = 1 := Scalar.offspring_integral_eq_one hc
  have hkr : Integrable (fun k : ℕ => (k : ℝ) * r) μ.toMeasure :=
    (integrable_offspring hc).mul_const r
  have heq : realGF μ a - realGF μ b + r =
      ∫ k : ℕ, (a ^ k - b ^ k + (k : ℝ) * r) ∂μ.toMeasure := by
    rw [realGF_eq_integral μ ha0 ha1, realGF_eq_integral μ hb0 hb1]
    calc
      (∫ k : ℕ, a ^ k ∂μ.toMeasure) - (∫ k : ℕ, b ^ k ∂μ.toMeasure) + r =
          (∫ k : ℕ, a ^ k ∂μ.toMeasure) - (∫ k : ℕ, b ^ k ∂μ.toMeasure) +
            ∫ k : ℕ, (k : ℝ) * r ∂μ.toMeasure := by
              rw [integral_mul_const, hmean, one_mul]
      _ = (∫ k : ℕ, (a ^ k - b ^ k) ∂μ.toMeasure) +
            ∫ k : ℕ, (k : ℝ) * r ∂μ.toMeasure := by
              rw [integral_sub (hi a ha0 ha1) (hi b hb0 hb1)]
      _ = ∫ k : ℕ, (a ^ k - b ^ k + (k : ℝ) * r) ∂μ.toMeasure :=
        (integral_add ((hi a ha0 ha1).sub (hi b hb0 hb1)) hkr).symm
  rw [heq]
  constructor
  · apply integral_nonneg
    intro k
    exact add_nonneg (sub_nonneg.mpr (pow_le_pow_left₀ hb0 hba k))
      (mul_nonneg (Nat.cast_nonneg k) hr0)
  · have hbound : Integrable (fun k : ℕ => (k : ℝ) * (2 * u ^ 2)) μ.toMeasure :=
      (integrable_offspring hc).mul_const (2 * u ^ 2)
    have ht := integral_mono (((hi a ha0 ha1).sub (hi b hb0 hb1)).add hkr) hbound
      (fun k => ?_)
    · rw [integral_mul_const, hmean, one_mul] at ht
      exact ht
    · have hmax : max |a| |b| ≤ 1 := by
        refine max_le ?_ ?_
        · rwa [abs_of_nonneg ha0]
        · rwa [abs_of_nonneg hb0]
      have hp := abs_pow_sub_pow_le (n := k) (a := a) (b := b)
      have hpm : max |a| |b| ^ (k - 1) ≤ 1 :=
        pow_le_one₀ (by positivity) hmax
      have hp' : a ^ k - b ^ k ≤ (k : ℝ) * (a - b) := by
        calc
          a ^ k - b ^ k ≤ |a ^ k - b ^ k| := le_abs_self _
          _ ≤ |a - b| * k * max |a| |b| ^ (k - 1) := hp
          _ ≤ |a - b| * k * 1 := by gcongr
          _ = (k : ℝ) * (a - b) := by
            rw [mul_one, abs_of_nonneg (sub_nonneg.mpr hba)]
            ring
      have hk : a ^ k - b ^ k ≤ (k : ℝ) * u ^ 2 := by
        calc
          a ^ k - b ^ k ≤ (k : ℝ) * (a - b) := hp'
          _ ≤ (k : ℝ) * u ^ 2 := mul_le_mul_of_nonneg_left hab (Nat.cast_nonneg k)
      have hkr' : (k : ℝ) * r ≤ (k : ℝ) * u ^ 2 :=
        mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg k)
      change a ^ k - b ^ k + (k : ℝ) * r ≤ (k : ℝ) * (2 * u ^ 2)
      linarith

/-- An `O(u²)` comparison between the exponential and real generating functions. -/
theorem centeredLaplace_realGF_difference_bound (μ : PMF ℕ) (hc : IsCritical μ)
    {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) :
    |centeredLaplace (stepLaw μ) u - 1 - (realGF μ (1 - u) - (1 - u))| ≤ 4 * u ^ 2 := by
  let G := realGF μ (Real.exp (-u))
  let E := G - realGF μ (1 - u) + (Real.exp u - 1 - u)
  have hE := realGF_exp_error_bounds μ hc hu0 hu1
  have hG := realGF_one_sub_exp_bounds μ hc hu0
  have hr0 : 0 ≤ Real.exp u - 1 - u := by
    have he := Real.add_one_le_exp u
    linarith
  have hr : Real.exp u - 1 - u ≤ u ^ 2 := by
    have he := Real.norm_exp_sub_one_sub_id_le (x := u)
      (by simpa [abs_of_nonneg hu0] using hu1)
    rw [Real.norm_eq_abs, abs_of_nonneg hr0] at he
    simpa [Real.norm_of_nonneg hu0] using he
  have hu2 : u ^ 2 ≤ u := by nlinarith
  have hdecomp : centeredLaplace (stepLaw μ) u - 1 - (realGF μ (1 - u) - (1 - u)) =
      (Real.exp u - 1) * (G - 1) + E := by
    rw [centeredLaplace_stepLaw_eq μ hc hu0]
    dsimp [G, E]
    ring
  rw [hdecomp]
  calc
    |(Real.exp u - 1) * (G - 1) + E| ≤ |(Real.exp u - 1) * (G - 1)| + |E| :=
      abs_add_le _ _
    _ = (Real.exp u - 1) * (1 - G) + E := by
      rw [abs_mul, abs_of_nonneg (by linarith : 0 ≤ Real.exp u - 1),
        abs_of_nonpos (by linarith [hG.1] : G - 1 ≤ 0), abs_of_nonneg hE.1]
      ring
    _ ≤ 4 * u ^ 2 := by
      have hfirst : (Real.exp u - 1) * (1 - G) ≤ 2 * u ^ 2 := by
        calc
          (Real.exp u - 1) * (1 - G) ≤ (2 * u) * u := by
            apply mul_le_mul (by linarith) hG.2 hG.1 (by linarith)
          _ = 2 * u ^ 2 := by ring
      linarith [hE.2]

private theorem tendsto_exp_remainder_div_sq {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 0))
    (hu0 : ∀ᶠ n in atTop, u n ≠ 0) (a : ℝ) :
    Tendsto (fun n : ℕ => (Real.exp (-u n * a) - 1 + u n * a) / (u n) ^ 2) atTop
      (𝓝 (a ^ 2 / 2)) := by
  have hcomp : Tendsto (fun n : ℕ => -u n * a) atTop (𝓝 0) := by
    simpa using (hu.neg).mul_const a
  by_cases ha : a = 0
  · subst a
    simp
  have ht := ((Real.exp_sub_sum_range_succ_isLittleO_pow 2).comp_tendsto
    hcomp).tendsto_div_nhds_zero
  have ht2 := ht.const_mul (a ^ 2)
  rw [mul_zero] at ht2
  have ht' : Tendsto (fun n : ℕ =>
      (Real.exp (-u n * a) - 1 + u n * a) / (u n) ^ 2 - a ^ 2 / 2) atTop (𝓝 0) := by
    apply ht2.congr'
    filter_upwards [hu0] with n hn
    simp only [Function.comp_def, Finset.sum_range_succ, Finset.sum_range_zero,
      Nat.factorial_zero, Nat.cast_one, pow_zero, div_one, Nat.factorial_one,
      Nat.factorial_two, Nat.cast_ofNat]
    field_simp [hn, ha]
    ring
  convert ht'.add_const (a ^ 2 / 2) using 1
  · funext n
    ring
  · ring_nf

private theorem norming_centeredLaplace_limit_finiteVariance
    {μ : PMF ℕ} {B : ℕ → ℝ} (h : StableDomain μ 2 B)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (centeredLaplace (stepLaw μ) (lam / norming (stepLaw μ) 2 n) - 1)) atTop
      (𝓝 (lam ^ (2 : ℝ))) := by
  let ν := stepLaw μ
  let A := norming ν 2
  have hstep : ν {z : ℤ | z < -1} = 0 := stepLaw_lt_neg_one μ
  have hint : Integrable (fun z : ℤ => (z : ℝ)) ν := integrable_stepLaw h.critical
  have hmean : mean ν = 0 := mean_stepLaw h.critical
  have hatt : IsStableAttracted ν 2 (mean ν) B := by
    change IsStableAttracted (stepLaw μ) 2 (mean (stepLaw μ)) B
    rw [mean_stepLaw h.critical]
    exact stableDomain_isStableAttracted h
  have hcanon : IsStableAttracted ν 2 (mean ν) A :=
    Norming.locallimit_i ν hstep hint ⟨B, hatt⟩
  have hA : Tendsto A atTop atTop := TransformConvergence.tendsto_atTop ν hcanon
  let u : ℕ → ℝ := fun n => lam / A n
  have hu : Tendsto u atTop (𝓝 0) := tendsto_const_nhds.div_atTop hA
  have hu0 : ∀ᶠ n in atTop, u n ≠ 0 := by
    filter_upwards [hA.eventually_gt_atTop 0] with n hn
    exact div_ne_zero hlam.ne' hn.ne'
  have hbound : ∀ᶠ n in atTop, ∀ᵐ z : ℤ ∂ν,
      ‖(Real.exp (-u n * (z : ℝ)) - 1 + u n * (z : ℝ)) / (u n) ^ 2‖ ≤
        2 * (z : ℝ) ^ 2 := by
    filter_upwards [hu0, hu.eventually (Metric.ball_mem_nhds (0 : ℝ) one_pos),
      hA.eventually_gt_atTop 0] with n hn hu1 hAn
    have hun : 0 < u n := div_pos hlam hAn
    have hu1' : u n ≤ 1 := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hun] at hu1
      linarith
    have hnull : ∀ᵐ z : ℤ ∂ν, (-1 : ℝ) ≤ (z : ℝ) := by
      rw [ae_iff]
      have he : {z : ℤ | ¬(-1 : ℝ) ≤ (z : ℝ)} = {z : ℤ | z < -1} := by
        ext z
        norm_cast
        simp
      rwa [he]
    filter_upwards [hnull] with z hz
    by_cases hsmall : |u n * (z : ℝ)| ≤ 1
    · have he := Real.norm_exp_sub_one_sub_id_le (x := -u n * (z : ℝ))
        (by simpa [abs_neg] using hsmall)
      have hneg : -u n * (z : ℝ) = -(u n * (z : ℝ)) := by ring
      rw [hneg, norm_neg] at he
      rw [Real.norm_eq_abs] at he ⊢
      rw [abs_div, abs_of_pos (sq_pos_of_pos hun)]
      calc
        |Real.exp (-u n * (z : ℝ)) - 1 + u n * (z : ℝ)| / (u n) ^ 2 ≤
            |u n * (z : ℝ)| ^ 2 / (u n) ^ 2 := by
          apply div_le_div_of_nonneg_right _ (sq_nonneg (u n))
          convert he using 1
          · congr 1
            ring_nf
        _ = (z : ℝ) ^ 2 := by
          rw [abs_mul, abs_of_pos hun, mul_pow, sq_abs]
          field_simp
        _ ≤ 2 * (z : ℝ) ^ 2 := by nlinarith [sq_nonneg (z : ℝ)]
    · have hzz : 0 ≤ (z : ℝ) := by
        by_contra hzneg
        have hz' : (z : ℝ) ≤ 0 := le_of_not_ge hzneg
        have hzabs : |(z : ℝ)| ≤ 1 := by
          rw [abs_of_nonpos hz']
          linarith
        apply hsmall
        calc
          |u n * (z : ℝ)| = u n * |(z : ℝ)| := by rw [abs_mul, abs_of_pos hun]
          _ ≤ 1 * 1 := mul_le_mul hu1' hzabs (abs_nonneg _) zero_le_one
          _ = 1 := one_mul 1
      have hp : 0 ≤ u n * (z : ℝ) := mul_nonneg hun.le hzz
      have hlarge : 1 < u n * (z : ℝ) := by
        have : 1 < |u n * (z : ℝ)| := lt_of_not_ge hsmall
        rwa [abs_of_nonneg hp] at this
      have he0 : 0 ≤ Real.exp (-u n * (z : ℝ)) - 1 + u n * (z : ℝ) := by
        have he := Real.add_one_le_exp (-u n * (z : ℝ))
        linarith
      have he1 : Real.exp (-u n * (z : ℝ)) ≤ 1 := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
      rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hun), abs_of_nonneg he0]
      have hsquare : u n * (z : ℝ) ≤ (u n) ^ 2 * (z : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (u n * (z : ℝ))]
      calc
        (Real.exp (-u n * (z : ℝ)) - 1 + u n * (z : ℝ)) / (u n) ^ 2 ≤
            (u n * (z : ℝ)) / (u n) ^ 2 := by gcongr; linarith
        _ ≤ 2 * (z : ℝ) ^ 2 := by
          apply (div_le_iff₀ (sq_pos_of_pos hun)).mpr
          nlinarith [sq_nonneg (u n), sq_nonneg ((z : ℝ))]
  have hInt : Tendsto (fun n : ℕ => ∫ z : ℤ,
      (Real.exp (-u n * (z : ℝ)) - 1 + u n * (z : ℝ)) / (u n) ^ 2 ∂ν) atTop
      (𝓝 (∫ z : ℤ, (z : ℝ) ^ 2 / 2 ∂ν)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun z : ℤ => 2 * (z : ℝ) ^ 2)
    · exact Eventually.of_forall fun n => (by fun_prop)
    · exact hbound
    · exact hsq.const_mul 2
    · exact Eventually.of_forall fun z => tendsto_exp_remainder_div_sq hu hu0 (z : ℝ)
  have hvar : 0 < Attraction.variance ν :=
    DomainCriterion.variance_pos_of_integrable_sq hatt hint hsq
  have heq : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (centeredLaplace ν (u n) - 1) =
      (2 * lam ^ 2 / Attraction.variance ν) * ∫ z : ℤ,
        (Real.exp (-u n * (z : ℝ)) - 1 + u n * (z : ℝ)) / (u n) ^ 2 ∂ν := by
    filter_upwards [hu0, eventually_ge_atTop 1, hA.eventually_gt_atTop 0] with n hn hn1 hAn
    have hn0 : n ≠ 0 := by omega
    have hnorm : A n = Real.sqrt (Attraction.variance ν) * Real.sqrt ((n : ℝ) / 2) :=
      norming_of_integrable_sq hsq 2 n
    have hsqrtv : (Real.sqrt (Attraction.variance ν)) ^ 2 = Attraction.variance ν :=
      Real.sq_sqrt hvar.le
    have hsqrtn : (Real.sqrt ((n : ℝ) / 2)) ^ 2 = (n : ℝ) / 2 :=
      Real.sq_sqrt (by positivity)
    have hun : 0 < u n := div_pos hlam hAn
    have hscale : (n : ℝ) * (u n) ^ 2 = 2 * lam ^ 2 / Attraction.variance ν := by
      rw [show u n = lam / A n from rfl, hnorm, div_pow, mul_pow, hsqrtv, hsqrtn]
      field_simp
    rw [centeredLaplace_sub_one_eq_integral hstep hint hun.le, hmean]
    simp only [sub_zero]
    calc
      (n : ℝ) * ∫ z : ℤ, (Real.exp (-u n * (z : ℝ)) - 1 + u n * (z : ℝ)) ∂ν =
          (n : ℝ) * ((u n) ^ 2 * ∫ z : ℤ,
            (Real.exp (-u n * (z : ℝ)) - 1 + u n * (z : ℝ)) / (u n) ^ 2 ∂ν) := by
        congr 1
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall fun z => by field_simp
      _ = (2 * lam ^ 2 / Attraction.variance ν) * ∫ z : ℤ,
          (Real.exp (-u n * (z : ℝ)) - 1 + u n * (z : ℝ)) / (u n) ^ 2 ∂ν := by
        rw [← mul_assoc, hscale]
  have hvar_eq : Attraction.variance ν = ∫ z : ℤ, (z : ℝ) ^ 2 ∂ν := by
    simp [Attraction.variance, hmean]
  have ht := hInt.const_mul (2 * lam ^ 2 / Attraction.variance ν)
  rw [integral_div, ← hvar_eq] at ht
  have ht' := ht.congr' (heq.mono fun n hn => hn.symm)
  change Tendsto (fun n : ℕ => (n : ℝ) * (centeredLaplace ν (u n) - 1)) atTop
    (𝓝 (lam ^ (2 : ℝ)))
  convert ht' using 1
  rw [Real.rpow_two]
  field_simp

/-- The centered step Laplace expansion along an arbitrary stable norming. -/
theorem tendsto_centeredLaplace_stableDomain {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (centeredLaplace (stepLaw μ) (lam / B n) - 1)) atTop (𝓝 (lam ^ θ)) := by
  let ν := stepLaw μ
  let A := norming ν θ
  have hstep : ν {z : ℤ | z < -1} = 0 := stepLaw_lt_neg_one μ
  have hint : Integrable (fun z : ℤ => (z : ℝ)) ν := integrable_stepLaw h.critical
  have hatt : IsStableAttracted ν θ (mean ν) B := by
    change IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) B
    rw [mean_stepLaw h.critical]
    exact stableDomain_isStableAttracted h
  have hcanon : IsStableAttracted ν θ (mean ν) A :=
    Norming.locallimit_i ν hstep hint ⟨B, hatt⟩
  have hApos : ∀ᶠ n in atTop, 0 < A n := by
    obtain ⟨N, hN⟩ := hcanon.pos
    exact eventually_atTop.2 ⟨N, hN⟩
  have hBpos : ∀ᶠ n in atTop, 0 < B n := by
    exact eventually_atTop.2 ⟨1, h.pos⟩
  have hr : Tendsto (fun n => A n / B n) atTop (𝓝 1) :=
    Norming.norming_isEquivalent ν hstep hint hatt
  apply tendsto_centeredLaplace_of_norming_equivalent ν hstep hint _ hr hApos hBpos hlam
  intro c hc
  by_cases hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν
  · have hθ : θ = 2 := DomainCriterion.index_eq_two_of_integrable_sq hatt hint hsq
    subst θ
    exact norming_centeredLaplace_limit_finiteVariance h hsq hc
  · rcases lt_or_eq_of_le h.alpha_mem.2 with hθ | hθ
    · have hT := DomainCriterion.rightTail_regularlyVarying hatt hstep hint hsq hθ
      exact norming_centeredLaplace_limit hstep hint h.alpha_mem.1 hθ hT hc
    · subst θ
      have hK := DomainCriterion.truncSecondMoment_slowlyVarying_unbounded hatt hint hsq
      exact CanonicalAttraction.gaussian_norming_centeredLaplace_limit
        hstep hint hK.1 hK.2 hc

private theorem sum_range_natCast_id (k : ℕ) :
    (∑ i ∈ Finset.range k, (i : ℝ)) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private theorem one_sub_pow_remainder_eq (u : ℝ) (k : ℕ) :
    (1 - u) ^ k - 1 + k * u = u * ∑ i ∈ Finset.range k, (1 - (1 - u) ^ i) := by
  have hg (m : ℕ) : 1 - (1 - u) ^ m = u * ∑ j ∈ Finset.range m, (1 - u) ^ j := by
    have h := geom_sum_mul_neg (1 - u) m
    have hu : 1 - (1 - u) = u := by ring
    rw [hu] at h
    linarith
  have hs : (∑ i ∈ Finset.range k, (1 - (1 - u) ^ i)) =
      (k : ℝ) - ∑ i ∈ Finset.range k, (1 - u) ^ i := by
    rw [Finset.sum_sub_distrib]
    simp
  rw [hs, mul_sub, ← hg k]
  ring

private theorem one_sub_pow_ratio (u : ℝ) (hu : u ≠ 0) (k : ℕ) :
    (1 - (1 - u) ^ k) / u = ∑ j ∈ Finset.range k, (1 - u) ^ j := by
  have h := geom_sum_mul_neg (1 - u) k
  have hu' : 1 - (1 - u) = u := by ring
  rw [hu'] at h
  field_simp
  linarith

private theorem tendsto_one_sub_pow_remainder_div_sq {u : ℕ → ℝ}
    (hu : Tendsto u atTop (𝓝 0)) (hu0 : ∀ᶠ n in atTop, u n ≠ 0) (k : ℕ) :
    Tendsto (fun n : ℕ => ((1 - u n) ^ k - 1 + k * u n) / (u n) ^ 2) atTop
      (𝓝 ((k : ℝ) * ((k : ℝ) - 1) / 2)) := by
  have hu' : Tendsto (fun n : ℕ => 1 - u n) atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub hu
  have heq : ∀ᶠ n in atTop, ((1 - u n) ^ k - 1 + k * u n) / (u n) ^ 2 =
      ∑ i ∈ Finset.range k, (1 - (1 - u n) ^ i) / (u n) := by
    filter_upwards [hu0] with n hn
    rw [one_sub_pow_remainder_eq, Finset.mul_sum, ← Finset.sum_div]
    field_simp
    rw [Finset.mul_sum]
  have hlim : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range k,
      ∑ j ∈ Finset.range i, (1 - u n) ^ j) atTop
      (𝓝 (∑ i ∈ Finset.range k, (i : ℝ))) := by
    apply tendsto_finsetSum
    intro i hi
    have ht : Tendsto (fun n : ℕ => ∑ j ∈ Finset.range i, (1 - u n) ^ j) atTop
        (𝓝 (∑ j ∈ Finset.range i, (1 : ℝ))) := by
      apply tendsto_finsetSum
      intro j hj
      simpa using hu'.pow j
    simpa using ht
  have ht : Tendsto (fun n : ℕ => ∑ i ∈ Finset.range k, (1 - (1 - u n) ^ i) / (u n)) atTop
      (𝓝 (∑ i ∈ Finset.range k, (i : ℝ))) := by
    apply hlim.congr'
    filter_upwards [hu0] with n hn
    apply Finset.sum_congr rfl
    intro i hi
    exact (one_sub_pow_ratio (u n) hn i).symm
  have ht' := ht.congr' (heq.mono fun n hn => hn.symm)
  convert ht' using 1
  rw [sum_range_natCast_id]

private theorem one_sub_pow_remainder_bounds {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (k : ℕ) :
    0 ≤ (1 - u) ^ k - 1 + k * u ∧ (1 - u) ^ k - 1 + k * u ≤ (k : ℝ) ^ 2 * u ^ 2 := by
  have ha0 : 0 ≤ 1 - u := sub_nonneg.mpr hu1
  have ha1 : 1 - u ≤ 1 := by linarith
  have hb : 1 - k * u ≤ (1 - u) ^ k := by
    have h := one_add_mul_sub_le_pow (a := 1 - u) (by linarith) k
    convert h using 1
    ring
  constructor
  · linarith
  · rw [one_sub_pow_remainder_eq]
    have hg : (∑ i ∈ Finset.range k, (1 - (1 - u) ^ i)) ≤ (k : ℝ) * (k * u) := by
      calc
        _ ≤ ∑ _i ∈ Finset.range k, (k * u) := by
          apply Finset.sum_le_sum
          intro i hi
          have hgeom : 1 - (1 - u) ^ i = u * ∑ j ∈ Finset.range i, (1 - u) ^ j := by
            have h := geom_sum_mul_neg (1 - u) i
            have hu : 1 - (1 - u) = u := by ring
            rw [hu] at h
            linarith
          rw [hgeom]
          have hs : (∑ j ∈ Finset.range i, (1 - u) ^ j) ≤ i := by
            calc
              _ ≤ ∑ _j ∈ Finset.range i, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro j hj
                exact pow_le_one₀ ha0 ha1
              _ = i := by simp
          have hik : (i : ℝ) ≤ k := by exact_mod_cast (Finset.mem_range.mp hi).le
          nlinarith [mul_nonneg hu0 (sub_nonneg.mpr hs)]
        _ = (k : ℝ) * (k * u) := by simp [mul_comm]
    have hnonneg : 0 ≤ u * ∑ i ∈ Finset.range k, (1 - (1 - u) ^ i) := by
      apply mul_nonneg hu0
      apply Finset.sum_nonneg
      intro i hi
      exact sub_nonneg.mpr (pow_le_one₀ ha0 ha1)
    calc
      u * ∑ i ∈ Finset.range k, (1 - (1 - u) ^ i) ≤ u * ((k : ℝ) * (k * u)) :=
        mul_le_mul_of_nonneg_left hg hu0
      _ = (k : ℝ) ^ 2 * u ^ 2 := by ring

private theorem exp_remainder_div_sq_le {u a : ℝ} (hu : 0 < u) (hu1 : u ≤ 1)
    (ha : -1 ≤ a) :
    ‖(Real.exp (-u * a) - 1 + u * a) / u ^ 2‖ ≤ 2 * a ^ 2 := by
  by_cases hsmall : |u * a| ≤ 1
  · have he := Real.norm_exp_sub_one_sub_id_le (x := -u * a) (by simpa [abs_neg] using hsmall)
    have hneg : -u * a = -(u * a) := by ring
    rw [hneg, norm_neg] at he
    rw [Real.norm_eq_abs] at he ⊢
    rw [abs_div, abs_of_pos (sq_pos_of_pos hu)]
    calc
      |Real.exp (-u * a) - 1 + u * a| / u ^ 2 ≤ |u * a| ^ 2 / u ^ 2 := by
        apply div_le_div_of_nonneg_right _ (sq_nonneg u)
        convert he using 1
        congr 1
        ring_nf
      _ = a ^ 2 := by
        rw [abs_mul, abs_of_pos hu, mul_pow, sq_abs]
        field_simp
      _ ≤ 2 * a ^ 2 := by nlinarith [sq_nonneg a]
  · have ha0 : 0 ≤ a := by
      by_contra han
      have ha' : a ≤ 0 := le_of_not_ge han
      have haabs : |a| ≤ 1 := by rw [abs_of_nonpos ha']; linarith
      apply hsmall
      calc
        |u * a| = u * |a| := by rw [abs_mul, abs_of_pos hu]
        _ ≤ 1 * 1 := mul_le_mul hu1 haabs (abs_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    have hp : 0 ≤ u * a := mul_nonneg hu.le ha0
    have hlarge : 1 < u * a := by
      have : 1 < |u * a| := lt_of_not_ge hsmall
      rwa [abs_of_nonneg hp] at this
    have he0 : 0 ≤ Real.exp (-u * a) - 1 + u * a := by
      have he := Real.add_one_le_exp (-u * a)
      linarith
    have he1 : Real.exp (-u * a) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    rw [Real.norm_eq_abs, abs_div, abs_of_pos (sq_pos_of_pos hu), abs_of_nonneg he0]
    have hsquare : u * a ≤ u ^ 2 * a ^ 2 := by nlinarith [sq_nonneg (u * a)]
    calc
      (Real.exp (-u * a) - 1 + u * a) / u ^ 2 ≤ (u * a) / u ^ 2 := by gcongr; linarith
      _ ≤ 2 * a ^ 2 := by
        apply (div_le_iff₀ (sq_pos_of_pos hu)).mpr
        nlinarith [sq_nonneg u, sq_nonneg a]

/-- In finite variance, the real and exponential generating-function expansions have the same
second-order term. -/
theorem tendsto_realGF_difference_zero_finiteVariance
    {μ : PMF ℕ} {B : ℕ → ℝ} (h : StableDomain μ 2 B)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (fun n : ℕ => (n : ℝ) *
      (centeredLaplace (stepLaw μ) (lam / B n) - 1 -
        (realGF μ (1 - lam / B n) - (1 - lam / B n)))) atTop (𝓝 0) := by
  let ν := stepLaw μ
  let A := norming ν 2
  let u : ℕ → ℝ := fun n => lam / B n
  have hstep : ν {z : ℤ | z < -1} = 0 := stepLaw_lt_neg_one μ
  have hint : Integrable (fun z : ℤ => (z : ℝ)) ν := integrable_stepLaw h.critical
  have hatt : IsStableAttracted ν 2 (mean ν) B := by
    change IsStableAttracted (stepLaw μ) 2 (mean (stepLaw μ)) B
    rw [mean_stepLaw h.critical]
    exact stableDomain_isStableAttracted h
  have hcanon : IsStableAttracted ν 2 (mean ν) A :=
    Norming.locallimit_i ν hstep hint ⟨B, hatt⟩
  have hA : Tendsto A atTop atTop := TransformConvergence.tendsto_atTop ν hcanon
  have hu : Tendsto u atTop (𝓝 0) := tendsto_const_nhds.div_atTop (tendsto_B_atTop h)
  have hu0 : ∀ᶠ n in atTop, u n ≠ 0 := by
    filter_upwards [(tendsto_B_atTop h).eventually_gt_atTop 0] with n hn
    exact div_ne_zero hlam.ne' hn.ne'
  have hu1 : ∀ᶠ n in atTop, u n ≤ 1 := hu.eventually_le_const (by norm_num)
  have hRlim : ∀ k : ℕ, Tendsto (fun n : ℕ =>
      (Real.exp (-u n * ((k : ℝ) - 1)) - (1 - u n) ^ k - u n) / (u n) ^ 2) atTop
      (𝓝 ((1 - (k : ℝ)) / 2)) := by
    intro k
    have he := tendsto_exp_remainder_div_sq hu hu0 ((k : ℝ) - 1)
    have hp := tendsto_one_sub_pow_remainder_div_sq hu hu0 k
    have ht := he.sub hp
    have ht' : Tendsto (fun n : ℕ =>
        (Real.exp (-u n * ((k : ℝ) - 1)) - (1 - u n) ^ k - u n) / (u n) ^ 2) atTop
        (𝓝 (((k : ℝ) - 1) ^ 2 / 2 - (k : ℝ) * ((k : ℝ) - 1) / 2)) := by
      apply ht.congr'
      filter_upwards [hu0] with n hn
      field_simp
      ring
    convert ht' using 1
    ring_nf
  have hbound : ∀ᶠ n in atTop, ∀ k : ℕ,
      ‖(Real.exp (-u n * ((k : ℝ) - 1)) - (1 - u n) ^ k - u n) / (u n) ^ 2‖ ≤
        4 * (k : ℝ) ^ 2 + 2 := by
    filter_upwards [hu0, hu1, (tendsto_B_atTop h).eventually_gt_atTop 0] with n hn hu1n hBn
    intro k
    have hun : 0 < u n := div_pos hlam hBn
    have he := exp_remainder_div_sq_le (a := (k : ℝ) - 1) hun hu1n
      (by have : (0 : ℝ) ≤ k := Nat.cast_nonneg k; linarith)
    have hp := one_sub_pow_remainder_bounds (le_of_lt hun) hu1n k
    have hdecomp : (Real.exp (-u n * ((k : ℝ) - 1)) - (1 - u n) ^ k - u n) / (u n) ^ 2 =
        (Real.exp (-u n * ((k : ℝ) - 1)) - 1 + u n * ((k : ℝ) - 1)) / (u n) ^ 2 -
          ((1 - u n) ^ k - 1 + u n * k) / (u n) ^ 2 := by
      field_simp
      ring
    rw [hdecomp]
    calc
      ‖(Real.exp (-u n * ((k : ℝ) - 1)) - 1 + u n * ((k : ℝ) - 1)) / (u n) ^ 2 -
          ((1 - u n) ^ k - 1 + u n * k) / (u n) ^ 2‖ ≤
          ‖(Real.exp (-u n * ((k : ℝ) - 1)) - 1 + u n * ((k : ℝ) - 1)) / (u n) ^ 2‖ +
          ‖((1 - u n) ^ k - 1 + u n * k) / (u n) ^ 2‖ := norm_sub_le _ _
      _ ≤ 2 * ((k : ℝ) - 1) ^ 2 + (k : ℝ) ^ 2 := by
        apply add_le_add he
        have hm : u n * (k : ℝ) = (k : ℝ) * u n := mul_comm _ _
        rw [hm]
        rw [Real.norm_of_nonneg (div_nonneg hp.1 (sq_nonneg (u n)))]
        convert div_le_div_of_nonneg_right hp.2 (sq_nonneg (u n)) using 1
        field_simp
      _ ≤ 4 * (k : ℝ) ^ 2 + 2 := by nlinarith [sq_nonneg ((k : ℝ) - 1)]
  have hInt : Tendsto (fun n : ℕ => ∫ k : ℕ,
      (Real.exp (-u n * ((k : ℝ) - 1)) - (1 - u n) ^ k - u n) / (u n) ^ 2 ∂μ.toMeasure) atTop
      (𝓝 (∫ k : ℕ, (1 - (k : ℝ)) / 2 ∂μ.toMeasure)) := by
    have hksq : Integrable (fun k : ℕ => (k : ℝ) ^ 2) μ.toMeasure := by
      have hfin := Attraction.memLp_offspring_of_integrable_sq hsq
      exact (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).1 hfin
    apply tendsto_integral_filter_of_dominated_convergence
      (fun k : ℕ => 4 * (k : ℝ) ^ 2 + 2)
    · exact Eventually.of_forall fun n => (by fun_prop)
    · apply hbound.mono
      intro n hn
      filter_upwards [] with k
      exact hn k
    · exact (hksq.const_mul 4).add (integrable_const 2)
    · exact Eventually.of_forall hRlim
  have hmean : ∫ k : ℕ, (k : ℝ) ∂μ.toMeasure = 1 := Scalar.offspring_integral_eq_one h.critical
  have hInt0 : (∫ k : ℕ, (1 - (k : ℝ)) / 2 ∂μ.toMeasure) = 0 := by
    rw [integral_div, integral_sub (integrable_const _) (integrable_offspring h.critical),
      integral_const, hmean]
    simp
  rw [hInt0] at hInt
  have hvar : 0 < Attraction.variance ν :=
    DomainCriterion.variance_pos_of_integrable_sq hatt hint hsq
  have hbase : Tendsto (fun n : ℕ => (n : ℝ) * (lam / A n) ^ 2) atTop
      (𝓝 (2 * lam ^ 2 / Attraction.variance ν)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnorm : A n = Real.sqrt (Attraction.variance ν) * Real.sqrt ((n : ℝ) / 2) :=
      norming_of_integrable_sq hsq 2 n
    have hsqrtv : (Real.sqrt (Attraction.variance ν)) ^ 2 = Attraction.variance ν :=
      Real.sq_sqrt hvar.le
    have hsqrtn : (Real.sqrt ((n : ℝ) / 2)) ^ 2 = (n : ℝ) / 2 :=
      Real.sq_sqrt (by positivity)
    rw [hnorm, div_pow, mul_pow, hsqrtv, hsqrtn]
    field_simp
  have hr : Tendsto (fun n => A n / B n) atTop (𝓝 1) :=
    Norming.norming_isEquivalent ν hstep hint hatt
  have hscale : Tendsto (fun n : ℕ => (n : ℝ) * (u n) ^ 2) atTop
      (𝓝 (2 * lam ^ 2 / Attraction.variance ν)) := by
    have ht := hbase.mul (hr.mul hr)
    simp only [mul_one] at ht
    apply ht.congr'
    filter_upwards [hA.eventually_gt_atTop 0, (tendsto_B_atTop h).eventually_gt_atTop 0]
      with n hAn hBn
    dsimp only [u]
    field_simp
  have ht := hscale.mul hInt
  rw [mul_zero] at ht
  apply ht.congr'
  filter_upwards [hu0, hu1, (tendsto_B_atTop h).eventually_gt_atTop 0] with n hn hu1n hBn
  have hun : 0 < u n := div_pos hlam hBn
  have hmean0 : mean ν = 0 := mean_stepLaw h.critical
  have hD : centeredLaplace ν (u n) - 1 - (realGF μ (1 - u n) - (1 - u n)) =
      (u n) ^ 2 * ∫ k : ℕ,
        (Real.exp (-u n * ((k : ℝ) - 1)) - (1 - u n) ^ k - u n) / (u n) ^ 2 ∂μ.toMeasure := by
    rw [← integral_const_mul]
    have heq : ∀ k : ℕ, (u n) ^ 2 *
        ((Real.exp (-u n * ((k : ℝ) - 1)) - (1 - u n) ^ k - u n) / (u n) ^ 2) =
        Real.exp (-u n * ((k : ℝ) - 1)) - (1 - u n) ^ k - u n := by
      intro k
      field_simp
    simp_rw [heq]
    have hexp0 : 0 ≤ Real.exp (-u n) := (Real.exp_pos _).le
    have hexp1 : Real.exp (-u n) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    have hiE : Integrable (fun k : ℕ => Real.exp (-u n) ^ k) μ.toMeasure := by
      apply Integrable.of_bound (by fun_prop) 1
      filter_upwards [] with k
      rw [Real.norm_of_nonneg (pow_nonneg hexp0 k)]
      exact pow_le_one₀ hexp0 hexp1
    have hiP : Integrable (fun k : ℕ => (1 - u n) ^ k) μ.toMeasure := by
      apply Integrable.of_bound (by fun_prop) 1
      filter_upwards [] with k
      rw [Real.norm_of_nonneg (pow_nonneg (sub_nonneg.mpr hu1n) k)]
      exact pow_le_one₀ (sub_nonneg.mpr hu1n) (by linarith)
    rw [centeredLaplace_stepLaw_eq μ h.critical hun.le,
      realGF_eq_integral μ hexp0 hexp1,
      realGF_eq_integral μ (sub_nonneg.mpr hu1n) (by linarith), ← integral_const_mul]
    have heq' : ∀ k : ℕ, Real.exp (-u n * ((k : ℝ) - 1)) - (1 - u n) ^ k - u n =
        Real.exp (u n) * Real.exp (-u n) ^ k - (1 - u n) ^ k + (-u n) := by
      intro k
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 1
      · congr 1
        ring_nf
    simp_rw [heq']
    have hadd := integral_add ((hiE.const_mul (Real.exp (u n))).sub hiP)
      (integrable_const (-u n) (μ := μ.toMeasure))
    have hsub := integral_sub (hiE.const_mul (Real.exp (u n))) hiP
    calc
      (∫ a : ℕ, Real.exp (u n) * Real.exp (-u n) ^ a ∂μ.toMeasure) - 1 -
          ((∫ k : ℕ, (1 - u n) ^ k ∂μ.toMeasure) - (1 - u n)) =
          (∫ a : ℕ, (Real.exp (u n) * Real.exp (-u n) ^ a - (1 - u n) ^ a) ∂μ.toMeasure) +
            ∫ _a : ℕ, -u n ∂μ.toMeasure := by rw [hsub]; simp; ring
      _ = ∫ a : ℕ, (Real.exp (u n) * Real.exp (-u n) ^ a - (1 - u n) ^ a + -u n) ∂μ.toMeasure :=
        hadd.symm

  rw [hD]
  dsimp only [u] at *
  ring

end BGW.StableTrees.Survival
