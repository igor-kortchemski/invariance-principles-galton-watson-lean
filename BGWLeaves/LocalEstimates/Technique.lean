module

public import BGWLeaves.LocalEstimates.Defs
import BGWLeaves.LocalEstimates.NormRatios
import BGWLeaves.LeafMass.YLaw
import BGWLeaves.LeafMass.Arithmetic
import BGWLeaves.LeafConcentration.OeLemmas
import BGWLeaves.StableAnalysis.TransformConvergence
import BGW.StableTrees.RegularVariation.Consequences
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# M7 provider `Technique`

Analytic estimates for Lemma 5.13 and the Lemma 5.4(ii) chain: `aN_*`, `aTilde_eq`, `eq_psi`, `eq_retenir`, `bN_*`, `Kn_tendsto_*`, `eq_cvmoche`, `eq_lemtechnique0/1/2`, `eq_cvdd`. Includes the exact discretization `eq_retenir` and the final assembly `lem_technical_ii`. The exported theorems fill registered holes of
`BGWLeaves.LocalEstimates`; they are exported in namespace `BGWLeaves.LocalEstimates.Technique` with exactly the types of the
statements file.
-/

@[expose] public section

namespace BGWLeaves.LocalEstimates.Technique

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW BGW.StableTrees
open BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

private noncomputable def bernLaw (p : Set.Icc (0 : ℝ) 1) : Measure ℤ := bernoulliMeasure 1 0 p

private instance bernLaw_probability (p : Set.Icc (0 : ℝ) 1) : IsProbabilityMeasure (bernLaw p) := by
  unfold bernLaw
  infer_instance

private instance intWalk_probability (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using
      (inferInstance : IsProbabilityMeasure ((intWalk ν n).conv ν))

private theorem bernLaw_sq_integrable (p : Set.Icc (0 : ℝ) 1) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (bernLaw p) :=
  integrable_bernoulliMeasure _ _ _ _

private theorem bernLaw_mean (p : Set.Icc (0 : ℝ) 1) : mean (bernLaw p) = p := by
  simp [mean, bernLaw, integral_bernoulliMeasure, smul_eq_mul]

private theorem bernLaw_variance (p : Set.Icc (0 : ℝ) 1) : variance (bernLaw p) = (p : ℝ) * (1 - p) := by
  rw [StableAnalysis.variance, bernLaw_mean]
  simp only [bernLaw, integral_bernoulliMeasure, smul_eq_mul, Int.cast_one, Int.cast_zero]
  ring

private theorem bernLaw_nonLattice (p : Set.Icc (0 : ℝ) 1) (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ¬ IsLatticeLaw (bernLaw p) := by
  have h1 : (bernLaw p).real {(1 : ℤ)} = p := by
    simp [bernLaw]
  have h0 : (bernLaw p).real {(0 : ℤ)} = 1 - (p : ℝ) := by
    simp [bernLaw]
  have hn1 : bernLaw p {(1 : ℤ)} ≠ 0 := by
    intro he
    rw [measureReal_def, he, ENNReal.toReal_zero] at h1
    linarith
  have hn0 : bernLaw p {(0 : ℤ)} ≠ 0 := by
    intro he
    rw [measureReal_def, he, ENNReal.toReal_zero] at h0
    linarith
  rintro ⟨b, d, hd, hae⟩
  rw [ae_iff_of_countable] at hae
  have hdiv := dvd_sub (hae 1 hn1) (hae 0 hn0)
  have hd1 : (d : ℤ) ∣ 1 := by convert hdiv using 1 ; ring
  have := Int.eq_one_of_dvd_one (by positivity) hd1
  omega

private theorem bern_conv_real (p : Set.Icc (0 : ℝ) 1) (ν : Measure ℤ) [IsFiniteMeasure ν] (k : ℤ) :
    (ν.conv (bernLaw p)).real {k} = (p : ℝ) * ν.real {k - 1} + (1 - p) * ν.real {k} := by
  have hpre : (fun z : ℤ => z + 1) ⁻¹' {k} = {k - 1} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    omega
  simp only [bernLaw, bernoulliMeasure_def, ← Measure.coe_nnreal_smul]
  rw [Measure.conv_add, Measure.conv_smul_right, Measure.conv_smul_right,
    Measure.conv_dirac, Measure.conv_dirac_zero,
    measureReal_add_apply
      (by simp only [Measure.smul_apply, smul_eq_mul];
          exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _))
      (by simp only [Measure.smul_apply, smul_eq_mul];
          exact ENNReal.mul_ne_top ENNReal.coe_ne_top (measure_ne_top _ _)),
    measureReal_ennreal_smul_apply, measureReal_ennreal_smul_apply,
    map_measureReal_apply (measurable_of_countable _) (measurableSet_singleton _), hpre]
  simp [unitInterval.coe_symm_eq]

private theorem bern_walk_rec (p : Set.Icc (0 : ℝ) 1) (n : ℕ) (k : ℤ) :
    intWalkProb (bernLaw p) (n + 1) k =
      (p : ℝ) * intWalkProb (bernLaw p) n (k - 1) + (1 - p) * intWalkProb (bernLaw p) n k := by
  exact bern_conv_real p (intWalk (bernLaw p) n) k

private theorem bern_walk_neg (p : Set.Icc (0 : ℝ) 1) (n : ℕ) {k : ℤ} (hk : k < 0) :
    intWalkProb (bernLaw p) n k = 0 := by
  induction n generalizing k with
  | zero => simp [intWalkProb, intWalk, measureReal_def, ne_of_gt hk]
  | succ n ih => rw [bern_walk_rec, ih (by omega), ih hk]; ring

private theorem binom_succ (m : ℝ) (n k : ℕ) :
    m * binomProb m n k + (1 - m) * binomProb m n (k + 1) = binomProb m (n + 1) (k + 1) := by
  rcases lt_trichotomy k n with hkn | rfl | hnk
  · have he : n - k = n - (k + 1) + 1 := by omega
    simp only [binomProb, Nat.choose_succ_succ', Nat.cast_add, Nat.add_sub_add_right, pow_succ, he]
    ring
  · simp [binomProb, pow_succ]
    ring
  · simp [binomProb, Nat.choose_eq_zero_of_lt hnk,
      Nat.choose_eq_zero_of_lt (show n < k + 1 by omega),
      Nat.choose_eq_zero_of_lt (show n + 1 < k + 1 by omega)]

private theorem bern_walk_binom (p : Set.Icc (0 : ℝ) 1) (n k : ℕ) :
    intWalkProb (bernLaw p) n k = binomProb p n k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => simp [intWalkProb, intWalk, measureReal_def, binomProb]
    | succ k =>
      have hk : (0 : ℤ) ≠ (k : ℤ) + 1 := by omega
      simp [intWalkProb, intWalk, measureReal_def, binomProb, hk]
  | succ n ih =>
    cases k with
    | zero =>
      rw [bern_walk_rec, bern_walk_neg p n (by norm_num), ih]
      simp [binomProb, pow_succ]
      ring
    | succ k =>
      have hk : ((k + 1 : ℕ) : ℤ) - 1 = k := by push_cast; ring
      rw [bern_walk_rec, hk, ih, ih]
      exact binom_succ p n k

private theorem sqrt_nat_div_self :
    Tendsto (fun n : ℕ => Real.sqrt n / n) atTop (𝓝 (0 : ℝ)) := by
  have ht := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sq_sqrt hnR.le
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  change (Real.sqrt (n : ℝ))⁻¹ = Real.sqrt (n : ℝ) / n
  field_simp
  nlinarith

private theorem floor_index_ratio {u : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hu : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (⌊u n⌋₊ : ℝ) / n) atTop (𝓝 l) := by
  have hlow : Tendsto (fun n : ℕ => u n / n - 1 / (n : ℝ)) atTop (𝓝 l) := by
    simpa only [sub_zero] using hu.sub tendsto_one_div_atTop_nhds_zero_nat
  have hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ u n ∧ 0 < (n : ℝ) := by
    filter_upwards [hu.eventually (Ioi_mem_nhds hl), eventually_ge_atTop 1] with n hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [lt_div_iff₀ hnR, zero_mul] at hn
    exact ⟨hn.le, hnR⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hu
  · filter_upwards [hpos] with n hn
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith [Nat.lt_floor_add_one (u n)]) hn.2.le
  · filter_upwards [hpos] with n hn
    exact div_le_div_of_nonneg_right (Nat.floor_le hn.1) hn.2.le

private theorem rN_ratio {μ : PMF ℕ} (hm : 0 < (μ 0).toReal) (u : ℝ) :
    Tendsto (fun n : ℕ => (rN μ n u : ℝ) / n) atTop (𝓝 (1 / (μ 0).toReal)) := by
  apply floor_index_ratio (one_div_pos.mpr hm)
  have ht' : Tendsto (fun n : ℕ => 1 / (μ 0).toReal + u * (Real.sqrt n / n)) atTop
      (𝓝 (1 / (μ 0).toReal)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 / (μ 0).toReal) atTop
        (𝓝 (1 / (μ 0).toReal))).add (sqrt_nat_div_self.const_mul u)
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

private theorem rN_atTop {μ : PMF ℕ} (hm : 0 < (μ 0).toReal) (u : ℝ) :
    Tendsto (rN μ · u) atTop atTop := by
  have ht := (rN_ratio hm u).pos_mul_atTop (one_div_pos.mpr hm) tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => (rN μ n u : ℝ)) atTop atTop := ht.congr' (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp)
  exact tendsto_natCast_atTop_iff.mp ht'


private theorem rN_centered {μ : PMF ℕ} (hm : 0 < (μ 0).toReal) (u : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) - (μ 0).toReal * rN μ n u) / Real.sqrt n)
      atTop (𝓝 (-(μ 0).toReal * u)) := by
  let v : ℕ → ℝ := fun n => (n : ℝ) / (μ 0).toReal + u * Real.sqrt n
  have hvpos : ∀ᶠ n : ℕ in atTop, 0 ≤ v n := by
    filter_upwards [(rN_atTop hm u).eventually (eventually_ge_atTop 1)] with n hn
    have hv : 1 ≤ v n := Nat.floor_pos.mp (show 0 < ⌊v n⌋₊ from hn)
    linarith
  have hl : Tendsto (fun n : ℕ => (-1 : ℝ) / Real.sqrt n) atTop (𝓝 0) :=
    (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).const_div_atTop (-1)
  have he : Tendsto (fun n : ℕ => ((rN μ n u : ℝ) - v n) / Real.sqrt n) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds
    · filter_upwards [hvpos] with n hn
      apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
      have hh := Nat.lt_floor_add_one (v n)
      change v n < (rN μ n u : ℝ) + 1 at hh
      linarith
    · filter_upwards [hvpos] with n hn
      apply div_nonpos_of_nonpos_of_nonneg _ (Real.sqrt_nonneg _)
      have hh : (rN μ n u : ℝ) ≤ v n := Nat.floor_le hn
      linarith
  have ht := (he.const_mul (-(μ 0).toReal)).const_add (-(μ 0).toReal * u)
  simp only [mul_zero, add_zero] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  dsimp only [v]
  field_simp [hm.ne']
  ring

private theorem bernoulli_llt_tendsto (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1)
    {r k : ℕ → ℕ} (hr : Tendsto r atTop atTop) :
    Tendsto (fun n : ℕ =>
      Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r n : ℝ) / 2) * binomProb p (r n) (k n) -
        gaussDensity (((k n : ℝ) - (r n : ℝ) * p) /
          (Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r n : ℝ) / 2)))) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := strongLLT (bernLaw p) (bernLaw_nonLattice p hp0 hp1)
    (bernLaw_sq_integrable p) (half_pos hε)
  obtain ⟨Nr, hNr⟩ := eventually_atTop.mp (hr.eventually (eventually_ge_atTop N))
  refine ⟨Nr, fun n hn => ?_⟩
  have hh := hN (r n) (hNr n hn) (k n)
  rw [bernLaw_mean, bernLaw_variance, bern_walk_binom] at hh
  rw [Real.dist_eq, sub_zero]
  exact lt_of_le_of_lt ((le_mul_of_one_le_left (abs_nonneg _) (le_max_left _ _)).trans hh) (by linarith)

private theorem rN_sqrt_scale {μ : PMF ℕ} (hm : 0 < (μ 0).toReal) (u σ : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt n / (σ * Real.sqrt ((rN μ n u : ℝ) / 2)))
      atTop (𝓝 (Real.sqrt (2 * (μ 0).toReal) / σ)) := by
  have ht := (((rN_ratio hm u).inv₀ (one_div_ne_zero hm.ne')).const_mul (2 : ℝ)).sqrt.div_const σ
  simp only [one_div, inv_inv] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1, (rN_atTop hm u).eventually (eventually_ge_atTop 1)] with n hn hr
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hrR : (rN μ n u : ℝ) ≠ 0 := by exact_mod_cast (show rN μ n u ≠ 0 by omega)
  have heq : 2 * ((rN μ n u : ℝ) / n)⁻¹ = (n : ℝ) / ((rN μ n u : ℝ) / 2) := by
    field_simp
  rw [heq, Real.sqrt_div (Nat.cast_nonneg _)]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem gaussian_F0 {m : ℝ} (hm : 0 < m) (hm1 : m < 1) (u : ℝ) :
    (Real.sqrt (2 * m) / Real.sqrt (m * (1 - m))) *
      gaussDensity ((-m * u) * (Real.sqrt (2 * m) / Real.sqrt (m * (1 - m)))) = F0 m u := by
  have hq : 0 < 1 - m := by linarith
  have hs : Real.sqrt (m * (1 - m)) ≠ 0 := (Real.sqrt_pos.mpr (mul_pos hm hq)).ne'
  have hc : Real.sqrt (2 * m) / Real.sqrt (m * (1 - m)) =
      Real.sqrt 2 / Real.sqrt (1 - m) := by
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_mul hm.le]
    have hsm : Real.sqrt m ≠ 0 := (Real.sqrt_pos.mpr hm).ne'
    field_simp
  rw [hc]
  have hc2 : (Real.sqrt 2 / Real.sqrt (1 - m)) ^ 2 = 2 / (1 - m) := by
    rw [div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sq_sqrt hq.le]
  have he : -((-m * u) * (Real.sqrt 2 / Real.sqrt (1 - m))) ^ 2 / 4 =
      -(m ^ 2 * u ^ 2) / (2 * (1 - m)) := by
    rw [mul_pow, mul_pow, hc2, neg_sq]
    field_simp
    ring
  have hd1 : Real.sqrt (4 * Real.pi) = Real.sqrt 2 * Real.sqrt (2 * Real.pi) := by
    rw [show 4 * Real.pi = 2 * (2 * Real.pi) by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  have hd2 : Real.sqrt (2 * Real.pi * (1 - m)) = Real.sqrt (2 * Real.pi) * Real.sqrt (1 - m) :=
    Real.sqrt_mul (by positivity) _
  unfold gaussDensity F0
  rw [he, hd1, hd2]
  have h2 : Real.sqrt (2 : ℝ) ≠ 0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  field_simp

private theorem weighted_gauss_bound {v : ℝ} (hv : 0 ≤ v) (y : ℝ) :
    max 1 (v * y ^ 2) * gaussDensity y ≤ (1 + 4 * v) / Real.sqrt (4 * Real.pi) := by
  have hg0 : 0 ≤ gaussDensity y := by unfold gaussDensity; positivity
  have he1 : Real.exp (-y ^ 2 / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg y])
  have he2 : y ^ 2 * Real.exp (-y ^ 2 / 4) ≤ 4 := by
    have hh := Real.mul_exp_neg_le_exp_neg_one (y ^ 2 / 4)
    have h1 : Real.exp (-1 : ℝ) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
    rw [← neg_div] at hh
    nlinarith
  have hmax : max 1 (v * y ^ 2) ≤ 1 + v * y ^ 2 := by
    apply max_le <;> nlinarith [mul_nonneg hv (sq_nonneg y)]
  calc
    _ ≤ (1 + v * y ^ 2) * gaussDensity y := mul_le_mul_of_nonneg_right hmax hg0
    _ = (Real.exp (-y ^ 2 / 4) + v * (y ^ 2 * Real.exp (-y ^ 2 / 4))) /
        Real.sqrt (4 * Real.pi) := by unfold gaussDensity; ring
    _ ≤ (1 + 4 * v) / Real.sqrt (4 * Real.pi) :=
      div_le_div_of_nonneg_right (by nlinarith [mul_le_mul_of_nonneg_left he2 hv]) (Real.sqrt_nonneg _)

private theorem bernoulli_weighted_bound (p : Set.Icc (0 : ℝ) 1)
    (hp0 : 0 < (p : ℝ)) (hp1 : (p : ℝ) < 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ r : ℕ, N ≤ r → 1 ≤ r → ∀ k : ℕ,
      max 1 (((k : ℝ) - r * p) ^ 2 / r) *
        (Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r : ℝ) / 2)) * binomProb p r k ≤ C := by
  let v : ℝ := (p : ℝ) * (1 - p) / 2
  let C : ℝ := 1 + (1 + 4 * v) / Real.sqrt (4 * Real.pi)
  obtain ⟨N, hN⟩ := strongLLT (bernLaw p) (bernLaw_nonLattice p hp0 hp1)
    (bernLaw_sq_integrable p) (by norm_num : (0 : ℝ) < 1)
  refine ⟨C, by dsimp [C, v]; positivity, N, fun r hr hr1 k => ?_⟩
  have hh := hN r hr (k : ℤ)
  rw [bernLaw_mean, bernLaw_variance, bern_walk_binom] at hh
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
  have hpq : 0 < (p : ℝ) * (1 - p) := mul_pos hp0 (by linarith)
  have hs : Real.sqrt ((p : ℝ) * (1 - p)) ≠ 0 := (Real.sqrt_pos.mpr hpq).ne'
  have hs2 : Real.sqrt ((r : ℝ) / 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
  have harg : v * (((k : ℝ) - r * p) /
        (Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r : ℝ) / 2))) ^ 2 =
      ((k : ℝ) - r * p) ^ 2 / r := by
    dsimp [v]
    rw [div_pow, mul_pow, Real.sq_sqrt hpq.le, Real.sq_sqrt (by positivity : 0 ≤ (r : ℝ) / 2)]
    field_simp
  have hg := weighted_gauss_bound (by dsimp [v]; positivity : 0 ≤ v)
    (((k : ℝ) - r * p) / (Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r : ℝ) / 2)))
  rw [harg] at hg
  have hW : 0 ≤ max 1 (((k : ℝ) - r * p) ^ 2 / r) := (by norm_num : (0 : ℝ) ≤ 1).trans (le_max_left _ _)
  calc
    _ = max 1 (((k : ℝ) - r * p) ^ 2 / r) *
        ((Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r : ℝ) / 2) * binomProb p r k) -
          gaussDensity (((k : ℝ) - r * p) /
            (Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r : ℝ) / 2)))) +
        max 1 (((k : ℝ) - r * p) ^ 2 / r) *
          gaussDensity (((k : ℝ) - r * p) /
            (Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r : ℝ) / 2))) := by ring
    _ ≤ max 1 (((k : ℝ) - r * p) ^ 2 / r) *
        |(Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r : ℝ) / 2) * binomProb p r k) -
          gaussDensity (((k : ℝ) - r * p) /
            (Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r : ℝ) / 2)))| +
        max 1 (((k : ℝ) - r * p) ^ 2 / r) *
          gaussDensity (((k : ℝ) - r * p) /
            (Real.sqrt ((p : ℝ) * (1 - p)) * Real.sqrt ((r : ℝ) / 2))) := by
      exact add_le_add (mul_le_mul_of_nonneg_left (le_abs_self _) hW) le_rfl
    _ ≤ C := add_le_add hh hg

private theorem rN_window_bounds {μ : PMF ℕ} (hm : 0 < (μ 0).toReal)
    (hm1 : (μ 0).toReal < 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal))
    {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : |u| ≤ ε * Real.sqrt n) :
    n ≤ rN μ n u ∧ (rN μ n u : ℝ) ≤ (1 / (μ 0).toReal + ε) * n ∧
      |(rN μ n u : ℝ) - ((n : ℝ) / (μ 0).toReal + u * Real.sqrt n)| ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hεm : ε * (μ 0).toReal < 1 - (μ 0).toReal := by
    rw [lt_div_iff₀ (by positivity)] at hε1
    nlinarith
  have hcoef : 1 < 1 / (μ 0).toReal - ε := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hm]
    nlinarith
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  have hulo : -ε * (n : ℝ) ≤ u * Real.sqrt n := by
    have hh := mul_le_mul_of_nonneg_right (neg_le_of_abs_le hu) (Real.sqrt_nonneg (n : ℝ))
    nlinarith
  have huhi : u * Real.sqrt n ≤ ε * (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (le_of_abs_le hu) (Real.sqrt_nonneg (n : ℝ))
    nlinarith
  have hlo : (n : ℝ) ≤ (n : ℝ) / (μ 0).toReal + u * Real.sqrt n := by
    have hh := mul_le_mul_of_nonneg_right hcoef.le (Nat.cast_nonneg n)
    rw [one_mul] at hh
    have heq : (1 / (μ 0).toReal - ε) * (n : ℝ) = (n : ℝ) / (μ 0).toReal - ε * n := by ring
    rw [heq] at hh
    linarith
  have hv0 : 0 ≤ (n : ℝ) / (μ 0).toReal + u * Real.sqrt n := (by positivity : (0 : ℝ) ≤ n).trans hlo
  have hfloor : (rN μ n u : ℝ) ≤ (n : ℝ) / (μ 0).toReal + u * Real.sqrt n := Nat.floor_le hv0
  refine ⟨Nat.le_floor hlo, ?_, ?_⟩
  · have heq : (1 / (μ 0).toReal + ε) * (n : ℝ) = (n : ℝ) / (μ 0).toReal + ε * n := by ring
    rw [heq]
    linarith
  · have hh := Nat.lt_floor_add_one ((n : ℝ) / (μ 0).toReal + u * Real.sqrt n)
    change (n : ℝ) / (μ 0).toReal + u * Real.sqrt n < (rN μ n u : ℝ) + 1 at hh
    rw [abs_le]
    constructor <;> linarith

private theorem window_weight_compare {m n r R u : ℝ}
    (hm : 0 < m) (hn : 1 ≤ n) (hnr : n ≤ r) (hr : r ≤ R * n)
    (he : |r - (n / m + u * Real.sqrt n)| ≤ 1) :
    max 1 (u ^ 2) ≤ (2 * R / m ^ 2 + 3) * max 1 ((n - m * r) ^ 2 / r) := by
  let d : ℝ := n - m * r
  let e : ℝ := r - (n / m + u * Real.sqrt n)
  let W : ℝ := max 1 (d ^ 2 / r)
  have hn0 : 0 < n := lt_of_lt_of_le zero_lt_one hn
  have hr0 : 0 < r := hn0.trans_le hnr
  have hR : 1 ≤ R := by nlinarith
  have hW1 : 1 ≤ W := le_max_left _ _
  have hW0 : 0 ≤ W := le_trans zero_le_one hW1
  have he2 : e ^ 2 ≤ 1 := by
    have hh := abs_le.mp he
    dsimp [e]
    nlinarith [hh.1, hh.2]
  have hid : m * u * Real.sqrt n = -d - m * e := by
    dsimp [d, e]
    field_simp
    ring
  have hsq : m ^ 2 * u ^ 2 * n ≤ 2 * d ^ 2 + 2 * m ^ 2 := by
    have hh : (m * u * Real.sqrt n) ^ 2 ≤ 2 * d ^ 2 + 2 * m ^ 2 := by
      rw [hid]
      nlinarith [sq_nonneg (d - m * e), mul_le_mul_of_nonneg_left he2 (sq_nonneg m)]
    simpa only [mul_pow, Real.sq_sqrt hn0.le] using hh
  have hd : d ^ 2 ≤ W * R * n := by
    have hh : d ^ 2 ≤ W * r := (div_le_iff₀ hr0).mp (le_max_right _ _)
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hr hW0])
  have hWn : 1 ≤ W * n := one_le_mul_of_one_le_of_one_le hW1 hn
  have hrest : 2 * m ^ 2 ≤ 3 * m ^ 2 * W * n := by
    nlinarith [mul_le_mul_of_nonneg_left hWn (sq_nonneg m), sq_nonneg m]
  have hu2 : u ^ 2 ≤ (2 * R / m ^ 2 + 3) * W := by
    apply (mul_le_mul_iff_right₀ (mul_pos (sq_pos_of_pos hm) hn0)).mp
    calc m ^ 2 * n * u ^ 2 ≤ 2 * d ^ 2 + 2 * m ^ 2 := by nlinarith [hsq]
      _ ≤ 2 * W * R * n + 3 * m ^ 2 * W * n := by nlinarith [hd, hrest]
      _ = m ^ 2 * n * ((2 * R / m ^ 2 + 3) * W) := by field_simp
  have hB : 1 ≤ 2 * R / m ^ 2 + 3 := by
    have hnon : 0 ≤ 2 * R / m ^ 2 := by positivity
    linarith
  exact max_le (one_le_mul_of_one_le_of_one_le hB hW1) hu2

section Mu0
variable {μ : PMF ℕ} (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1)
include h0 h1

theorem aN_tendsto (u : ℝ) :
    Tendsto (fun n : ℕ => aN μ n u) atTop (𝓝 (F0 (μ 0).toReal u)) := by
  let m : ℝ := (μ 0).toReal
  have hm : 0 < m := ENNReal.toReal_pos h0 (μ.apply_ne_top 0)
  have hm1 : m < 1 := by
    have hlt : μ 0 < 1 := lt_of_le_of_ne (PMF.coe_le_one μ 0) h1
    exact (ENNReal.toReal_lt_toReal (μ.apply_ne_top 0) ENNReal.one_ne_top).mpr hlt
  let p : Set.Icc (0 : ℝ) 1 := ⟨m, hm.le, hm1.le⟩
  let σ : ℝ := Real.sqrt (m * (1 - m))
  let A : ℕ → ℝ := fun n => σ * Real.sqrt ((rN μ n u : ℝ) / 2)
  let c : ℝ := Real.sqrt (2 * m) / σ
  have hσ : 0 < σ := Real.sqrt_pos.mpr (mul_pos hm (by linarith))
  have hscale : Tendsto (fun n : ℕ => Real.sqrt n / A n) atTop (𝓝 c) := rN_sqrt_scale hm u σ
  have harg : Tendsto (fun n : ℕ => ((n : ℝ) - (rN μ n u : ℝ) * m) / A n)
      atTop (𝓝 ((-m * u) * c)) := by
    have ht := (rN_centered hm u).mul hscale
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
    field_simp
    ring
  have hg : Continuous gaussDensity := by unfold gaussDensity; fun_prop
  have herr := bernoulli_llt_tendsto p hm hm1 (rN_atTop hm u) (k := fun n => n)
  change Tendsto (fun n : ℕ => A n * binomProb m (rN μ n u) n -
    gaussDensity (((n : ℝ) - (rN μ n u : ℝ) * m) / A n)) atTop (𝓝 0) at herr
  have hpoint : Tendsto (fun n : ℕ => A n * binomProb m (rN μ n u) n) atTop
      (𝓝 (gaussDensity ((-m * u) * c))) := by
    have ht := herr.add (hg.tendsto _ |>.comp harg)
    simpa only [Function.comp_apply, zero_add, sub_add_cancel] using ht
  have ht := hscale.mul hpoint
  have hlim : c * gaussDensity ((-m * u) * c) = F0 m u := gaussian_F0 hm hm1 u
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [(rN_atTop hm u).eventually (eventually_ge_atTop 1)] with n hn
  have hA : A n ≠ 0 := mul_ne_zero hσ.ne' (Real.sqrt_pos.mpr (by exact_mod_cast (show 0 < (rN μ n u : ℝ) / 2 by positivity))).ne'
  dsimp only [aN, m]
  field_simp

theorem aN_majorant {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ u : ℝ, |u| ≤ ε * Real.sqrt n →
      aN μ n u ≤ C / max 1 (u ^ 2) := by
  let m : ℝ := (μ 0).toReal
  have hm : 0 < m := ENNReal.toReal_pos h0 (μ.apply_ne_top 0)
  have hm1 : m < 1 := by
    exact (ENNReal.toReal_lt_toReal (μ.apply_ne_top 0) ENNReal.one_ne_top).mpr
      (lt_of_le_of_ne (PMF.coe_le_one μ 0) h1)
  have hq : 0 < 1 - m := by linarith
  let p : Set.Icc (0 : ℝ) 1 := ⟨m, hm.le, hm1.le⟩
  let σ : ℝ := Real.sqrt (m * (1 - m))
  let R : ℝ := 1 / m + ε
  let B : ℝ := 2 * R / m ^ 2 + 3
  have hσ : 0 < σ := Real.sqrt_pos.mpr (mul_pos hm hq)
  have hR : 0 < R := by dsimp [R]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  obtain ⟨C, hC, N, hb⟩ := bernoulli_weighted_bound p hm hm1
  refine ⟨B * (Real.sqrt 2 / σ) * C, max N 1, fun n hn u hu => ?_⟩
  have hnN : N ≤ n := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨hnr, hr, he⟩ := rN_window_bounds hm hm1 hε0 hε1 hn1 hu
  let r := rN μ n u
  let A : ℝ := σ * Real.sqrt ((r : ℝ) / 2)
  let W : ℝ := max 1 (((n : ℝ) - (r : ℝ) * m) ^ 2 / r)
  have hr1 : 1 ≤ r := hn1.trans hnr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr1
  have hA : 0 < A := mul_pos hσ (Real.sqrt_pos.mpr (by positivity))
  have hbin : 0 ≤ binomProb m r n := by unfold binomProb; positivity
  have hW : 0 ≤ W := le_trans zero_le_one (le_max_left _ _)
  have hprod : 0 ≤ W * A * binomProb m r n := mul_nonneg (mul_nonneg hW hA.le) hbin
  have hw := hb r (hnN.trans hnr) hr1 n
  change W * A * binomProb m r n ≤ C at hw
  have hcompare : max 1 (u ^ 2) ≤ B * W := by
    have hh := window_weight_compare hm (by exact_mod_cast hn1) (by exact_mod_cast hnr) hr he
    simpa only [B, R, W, r, m, mul_comm] using hh
  have hscale : Real.sqrt n / A ≤ Real.sqrt 2 / σ := by
    rw [div_le_div_iff₀ hA hσ]
    have hh : Real.sqrt (n : ℝ) ≤ Real.sqrt (r : ℝ) := Real.sqrt_le_sqrt (by exact_mod_cast hnr)
    have hs : Real.sqrt 2 * Real.sqrt ((r : ℝ) / 2) = Real.sqrt (r : ℝ) := by
      rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
      congr 1
      ring
    dsimp [A]
    nlinarith [mul_le_mul_of_nonneg_right hh hσ.le]
  have hAN : 0 ≤ aN μ n u := by unfold aN; exact mul_nonneg (Real.sqrt_nonneg _) hbin
  apply (le_div_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left (1 : ℝ) (u ^ 2)))).mpr
  calc aN μ n u * max 1 (u ^ 2) ≤ aN μ n u * (B * W) := mul_le_mul_of_nonneg_left hcompare hAN
    _ = B * (Real.sqrt n / A) * (W * A * binomProb m r n) := by
      dsimp [aN]
      field_simp
      ring
    _ ≤ B * (Real.sqrt 2 / σ) * (W * A * binomProb m r n) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hscale hB) hprod
    _ ≤ B * (Real.sqrt 2 / σ) * C := mul_le_mul_of_nonneg_left hw (by positivity)

theorem aTilde_eq {n : ℕ} (hn : 1 ≤ n) (u : ℝ) (hr : 1 ≤ rN μ n u) :
    Real.sqrt n * binomProb (μ 0).toReal (rN μ n u - 1) (n - 1) =
      (n : ℝ) / ((μ 0).toReal * rN μ n u) * aN μ n u := by
  let p := rN μ n u
  have hp : 1 ≤ p := hr
  have hm : (μ 0).toReal ≠ 0 := (ENNReal.toReal_pos h0 (μ.apply_ne_top 0)).ne'
  change Real.sqrt n * binomProb (μ 0).toReal (p - 1) (n - 1) =
    (n : ℝ) / ((μ 0).toReal * p) * (Real.sqrt n * binomProb (μ 0).toReal p n)
  by_cases hnp : n ≤ p
  · have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hcomb := Nat.add_one_mul_choose_eq (p - 1) (n - 1)
    simp only [Nat.sub_add_cancel hp, Nat.sub_add_cancel hn] at hcomb
    have hcombR : (p : ℝ) * ((p - 1).choose (n - 1) : ℝ) =
        (p.choose n : ℝ) * n := by exact_mod_cast hcomb
    have hchoose : ((p - 1).choose (n - 1) : ℝ) = (n : ℝ) / p * (p.choose n : ℝ) := by
      calc ((p - 1).choose (n - 1) : ℝ) = (p.choose n : ℝ) * n / p :=
          (eq_div_iff hpR).mpr (by nlinarith [hcombR])
        _ = (n : ℝ) / p * (p.choose n : ℝ) := by ring
    have hpow : (μ 0).toReal ^ n = (μ 0).toReal ^ (n - 1) * (μ 0).toReal := by
      conv_lhs => rw [show n = (n - 1) + 1 by omega]
      rw [pow_succ]
    unfold binomProb
    rw [show p - 1 - (n - 1) = p - n by omega, hchoose, hpow]
    field_simp
  · have hnp' : p < n := lt_of_not_ge hnp
    have hsub : p - 1 < n - 1 := by omega
    simp [binomProb, Nat.choose_eq_zero_of_lt hnp', Nat.choose_eq_zero_of_lt hsub]

end Mu0

private theorem qN_ratio {μ : PMF ℕ} (hm : 0 < (μ 0).toReal) (hm1 : (μ 0).toReal < 1) (u : ℝ) :
    Tendsto (fun n : ℕ => (qN μ n u : ℝ) / n) atTop (𝓝 ((1 - (μ 0).toReal) / (μ 0).toReal)) := by
  have hl : 1 < 1 / (μ 0).toReal := (lt_div_iff₀ hm).mpr (by simpa using hm1)
  have hle : ∀ᶠ n : ℕ in atTop, n ≤ rN μ n u := by
    filter_upwards [(rN_ratio hm u).eventually (Ioi_mem_nhds hl), eventually_ge_atTop 1] with n hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [lt_div_iff₀ hnR, one_mul] at hn
    exact_mod_cast hn.le
  have ht := (rN_ratio hm u).sub_const 1
  have heq : 1 / (μ 0).toReal - 1 = (1 - (μ 0).toReal) / (μ 0).toReal := by field_simp
  rw [heq] at ht
  apply ht.congr'
  filter_upwards [hle, eventually_ge_atTop 1] with n hn hn1
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [qN, Nat.cast_sub hn, sub_div, div_self hnR]

private theorem qN_atTop {μ : PMF ℕ} (hm : 0 < (μ 0).toReal) (hm1 : (μ 0).toReal < 1) (u : ℝ) :
    Tendsto (qN μ · u) atTop atTop := by
  have hl : 0 < (1 - (μ 0).toReal) / (μ 0).toReal := div_pos (by linarith) hm
  have ht := (qN_ratio hm hm1 u).pos_mul_atTop hl tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => (qN μ n u : ℝ)) atTop atTop := ht.congr' (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp)
  exact tendsto_natCast_atTop_iff.mp ht'

private theorem supJ_bounds {S : Finset ℕ} {f : ℕ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ j ∈ S, 0 ≤ f j ∧ f j ≤ C) :
    0 ≤ supJ S f ∧ supJ S f ≤ C ∧ ∀ j ∈ S, f j ≤ supJ S f := by
  classical
  have hi (j : ℕ) : (⨆ _ : j ∈ S, f j) = if j ∈ S then f j else 0 := by
    by_cases hj : j ∈ S <;> simp [hj]
  have hb (j : ℕ) : (⨆ _ : j ∈ S, f j) ≤ C := by
    rw [hi]
    split_ifs with hj
    · exact (hf j hj).2
    · exact hC
  have hB : BddAbove (Set.range (fun j : ℕ => ⨆ _ : j ∈ S, f j)) := by
    refine ⟨C, ?_⟩
    rintro x ⟨j, rfl⟩
    exact hb j
  have h0 : 0 ≤ (⨆ _ : (0 : ℕ) ∈ S, f 0) := by
    rw [hi]
    split_ifs with hj
    · exact (hf 0 hj).1
    · exact le_rfl
  refine ⟨h0.trans (le_ciSup hB 0), ciSup_le hb, ?_⟩
  intro j hj
  have hh := le_ciSup hB j
  simpa only [supJ, hi, ite_eq_left hj] using hh

private theorem supJ_measurable {S : Finset ℕ} {f : ℕ → ℝ → ℝ}
    (hf : ∀ j, Measurable (f j)) : Measurable (fun u => supJ S (fun j => f j u)) := by
  exact Measurable.iSup (fun j => Measurable.iSup (fun _ : j ∈ S => hf j))

private noncomputable def aWindow (μ : PMF ℕ) (ε : ℝ) (n : ℕ) : ℝ → ℝ :=
  (Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)).indicator (aN μ n)

private noncomputable def techniqueError (μ : PMF ℕ) (θ α ε : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  supJ (Finset.Icc 1 ⌊α * normB μ θ n⌋₊) fun j =>
    |aWindow μ ε n u * bN μ θ n u j -
      F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)|

private theorem aN_nonneg (μ : PMF ℕ) (n : ℕ) (u : ℝ) : 0 ≤ aN μ n u := by
  have hm : (μ 0).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
  have hq : 0 ≤ 1 - (μ 0).toReal := sub_nonneg.mpr hm
  unfold aN binomProb
  positivity

private theorem aN_measurable (μ : PMF ℕ) (n : ℕ) : Measurable (aN μ n) := by
  have hp : Measurable (rN μ n) :=
    Nat.measurable_floor.comp (measurable_const.add (measurable_id.mul_const _))
  exact ((measurable_of_countable (fun p : ℕ => binomProb (μ 0).toReal p n)).comp hp).const_mul _

private theorem bN_measurable (μ : PMF ℕ) (θ : ℝ) (n : ℕ) (j : ℤ) : Measurable (bN μ θ n · j) := by
  have hp : Measurable (rN μ n) :=
    Nat.measurable_floor.comp (measurable_const.add (measurable_id.mul_const _))
  exact ((measurable_of_countable (fun p : ℕ => intWalkProb (etaLaw μ) (p - n) ((n : ℤ) - j))).comp hp).const_mul _

private theorem G0_continuous {μ : PMF ℕ} {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    Continuous (fun u : ℝ => G0 μ θ u x) := by
  have hd := Scalar.continuous_stableDensity hθ
  unfold G0 finVarShift
  split_ifs <;> fun_prop

private theorem F0_integrable {m : ℝ} (hm : 0 < m) (hm1 : m < 1) : Integrable (F0 m) := by
  have ha : 0 < m ^ 2 / (2 * (1 - m)) := by positivity
  apply ((integrable_exp_neg_mul_sq ha).div_const (Real.sqrt (2 * Real.pi * (1 - m)))).congr
  exact Eventually.of_forall fun u => by
    exact congrArg (fun t : ℝ => Real.exp t / Real.sqrt (2 * Real.pi * (1 - m)))
      (by ring : -(m ^ 2 / (2 * (1 - m))) * u ^ 2 = -(m ^ 2 * u ^ 2) / (2 * (1 - m)))

private theorem window_weight_integrable : Integrable (fun u : ℝ => 1 / max 1 (u ^ 2)) := by
  have hm : Measurable (fun u : ℝ => 1 / max 1 (u ^ 2)) := by fun_prop
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / max 1 (u ^ 2))]
    rw [show 2 * (1 + u ^ 2)⁻¹ = 2 / (1 + u ^ 2) by rfl]
    apply (div_le_div_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (by positivity)).mpr
    nlinarith [le_max_left (1 : ℝ) (u ^ 2), le_max_right (1 : ℝ) (u ^ 2)]

private theorem techniqueError_measurable {μ : PMF ℕ} {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (α ε : ℝ) (n : ℕ) : Measurable (techniqueError μ θ α ε n) := by
  apply supJ_measurable
  intro j
  have ha : Measurable (aWindow μ ε n) := (aN_measurable μ n).indicator measurableSet_Icc
  have hf : Measurable (F0 (μ 0).toReal) := by unfold F0; fun_prop
  have hh := ((ha.mul (bN_measurable μ θ n j)).sub
    (hf.mul (G0_continuous (μ := μ) hθ ((j : ℝ) / norming (etaLaw μ) θ n)).measurable)).norm
  simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.mul_apply] using hh

section Htheta
variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b) (hnl : ¬ IsLatticeLaw (etaLaw μ))
include hc hne hap hDA hnl

private theorem bp_div_qN (u : ℝ) :
    Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / norming (etaLaw μ) θ (qN μ n u))
      atTop (𝓝 (cC μ ^ (1 / θ))) := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hl : 0 < (1 - (μ 0).toReal) / (μ 0).toReal := div_pos (by linarith) hm
  have ht := (NormRatios.normBp_ratio_tendsto hc hne hap hDA hl (qN_ratio hm hm1 u)).inv₀
    (Real.rpow_pos_of_pos hl _).ne'
  simpa only [normBp_natCast, inv_div, ← Real.inv_rpow hl.le, cC] using ht

theorem bN_bounded {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    ∃ C : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ u : ℝ, |u| ≤ ε * Real.sqrt n → ∀ j : ℤ,
      |bN μ θ n u j| ≤ C := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  have hm1 : (μ 0).toReal < 1 := by linarith
  let d : ℝ := (1 - (μ 0).toReal) / (4 * (μ 0).toReal)
  have hd : 0 < d := by dsimp [d]; positivity
  let a : ℕ → ℝ := norming (etaLaw μ) θ
  have hS := NormRatios.hS_of_nonLattice hc hne hnl
  obtain ⟨hattr, hmono, _⟩ := etaLaw_norming hc hne hS hDA
  obtain ⟨Np, hp⟩ := hattr.pos
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  obtain ⟨Nl, hl⟩ := llt_etaLaw_nonlattice hc hne hS hDA hnl (by norm_num : (0 : ℝ) < 1)
  have hr : Tendsto (fun n : ℕ => a n / a ⌊d * (n : ℝ)⌋₊) atTop (𝓝 ((d ^ (1 / θ))⁻¹)) := by
    have hu : Tendsto (fun n : ℕ => (d * (n : ℝ)) / n) atTop (𝓝 d) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
      field_simp
    have ht := (NormRatios.normBp_ratio_tendsto hc hne hap hDA hd hu).inv₀ (Real.rpow_pos_of_pos hd _).ne'
    simpa only [normBp, Nat.floor_natCast, inv_div] using ht
  let D : ℝ := |(d ^ (1 / θ))⁻¹| + 1
  have hD : 0 < D := by dsimp [D]; positivity
  obtain ⟨Nr, hNr⟩ := Metric.tendsto_atTop.mp hr 1 zero_lt_one
  have hfloorTop : Tendsto (fun n : ℕ => ⌊d * (n : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_mul_atTop d hd
  obtain ⟨Nf, hNf⟩ := eventually_atTop.mp (hfloorTop.eventually (eventually_ge_atTop (max Np Nl)))
  obtain ⟨Nd, hNd⟩ := exists_nat_ge (1 / d)
  refine ⟨D * (1 + M), max (max (max Nr Nf) Nd) (max Np 1), fun n hn u hu j => ?_⟩
  have hnr : Nr ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hn))
  have hnf : Nf ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans hn))
  have hnd : Nd ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnp : Np ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hn1 : 1 ≤ n := (le_max_right _ _).trans ((le_max_right _ _).trans hn)
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hdn : 1 ≤ d * n := by
    have hh := hNd.trans (by exact_mod_cast hnd : (Nd : ℝ) ≤ n)
    rw [div_le_iff₀ hd] at hh
    nlinarith
  obtain ⟨hnrN, _, he⟩ := rN_window_bounds hm hm1 hε0 hε1 hn1 hu
  have hulo : -ε * (n : ℝ) ≤ u * Real.sqrt n := by
    have hh := mul_le_mul_of_nonneg_right (neg_le_of_abs_le hu) (Real.sqrt_nonneg (n : ℝ))
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg n)]
  have hgap : 2 * d ≤ 1 / (μ 0).toReal - ε - 1 := by
    have heq : 1 / (μ 0).toReal - 1 = 4 * d := by dsimp [d]; field_simp
    have hεd : ε < 2 * d := by
      convert hε1 using 1; dsimp [d]; ring
    linarith
  have hqn : d * n ≤ (qN μ n u : ℝ) := by
    have hh := (abs_le.mp he).1
    have hg := mul_le_mul_of_nonneg_right hgap (Nat.cast_nonneg n)
    have hdiv : (n : ℝ) / (μ 0).toReal = (1 / (μ 0).toReal) * n := by ring
    rw [qN, Nat.cast_sub hnrN]
    rw [hdiv] at hh
    nlinarith
  have hfq : ⌊d * (n : ℝ)⌋₊ ≤ qN μ n u := Nat.floor_le_of_le hqn
  have hfp : Np ≤ ⌊d * (n : ℝ)⌋₊ := (le_max_left _ _).trans (hNf n hnf)
  have hfl : Nl ≤ ⌊d * (n : ℝ)⌋₊ := (le_max_right _ _).trans (hNf n hnf)
  have han : 0 < a n := hp n hnp
  have haf : 0 < a ⌊d * (n : ℝ)⌋₊ := hp _ hfp
  have haq : 0 < a (qN μ n u) := haf.trans_le (hmono hfq)
  have hrat : a n / a (qN μ n u) ≤ D := by
    have hh : |a n / a ⌊d * (n : ℝ)⌋₊ - (d ^ (1 / θ))⁻¹| ≤ 1 := by
      simpa only [Real.dist_eq] using (hNr n hnr).le
    have hh' := abs_le.mp hh
    calc
      _ ≤ a n / a ⌊d * (n : ℝ)⌋₊ :=
        div_le_div_of_nonneg_left han.le haf (hmono hfq)
      _ ≤ D := by dsimp [D]; linarith [le_abs_self ((d ^ (1 / θ))⁻¹)]
  have hll := hl (qN μ n u) (hfl.trans hfq) ((n : ℤ) - j)
  have hpoint : |a (qN μ n u) * intWalkProb (etaLaw μ) (qN μ n u) ((n : ℤ) - j)| ≤ 1 + M := by
    let z : ℝ := ((((n : ℤ) - j : ℤ) : ℝ) - (qN μ n u : ℝ) *
      ((μ 0).toReal / (1 - (μ 0).toReal))) / a (qN μ n u)
    change |a (qN μ n u) * intWalkProb (etaLaw μ) (qN μ n u) ((n : ℤ) - j) -
      Scalar.stableDensity θ z| ≤ 1 at hll
    have hh := abs_sub_le (a (qN μ n u) * intWalkProb (etaLaw μ) (qN μ n u) ((n : ℤ) - j))
      (Scalar.stableDensity θ z) 0
    simp only [sub_zero] at hh
    exact hh.trans (add_le_add hll (hbound z))
  have heq : bN μ θ n u j = (a n / a (qN μ n u)) *
      (a (qN μ n u) * intWalkProb (etaLaw μ) (qN μ n u) ((n : ℤ) - j)) := by
    change a n * intWalkProb (etaLaw μ) (qN μ n u) ((n : ℤ) - j) = _
    field_simp
  rw [heq, abs_mul, abs_of_pos (div_pos han haq)]
  exact mul_le_mul hrat hpoint (abs_nonneg _) hD.le

theorem bN_sub_Qn (u : ℝ) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |bN μ θ n u j - Qn μ θ n u j| ≤ ε' := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hcC : 0 < cC μ := div_pos hm (by linarith)
  let L : ℝ := cC μ ^ (1 / θ)
  have hL : 0 < L := Real.rpow_pos_of_pos hcC _
  let a : ℕ → ℝ := norming (etaLaw μ) θ
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  let δ₁ : ℝ := ε' / (2 * (L + 1))
  let δ₂ : ℝ := ε' / (2 * (M + 1))
  have hδ₁ : 0 < δ₁ := by dsimp [δ₁]; positivity
  have hδ₂ : 0 < δ₂ := by dsimp [δ₂]; positivity
  have hS := NormRatios.hS_of_nonLattice hc hne hnl
  obtain ⟨Nl, hl⟩ := llt_etaLaw_nonlattice hc hne hS hDA hnl hδ₁
  have hq := qN_atTop hm hm1 u
  obtain ⟨Nq, hNq⟩ := eventually_atTop.mp (hq.eventually (eventually_ge_atTop Nl))
  obtain ⟨Nr, hNr⟩ := Metric.tendsto_atTop.mp (bp_div_qN hc hne hap hDA hnl u)
    (min 1 δ₂) (lt_min zero_lt_one hδ₂)
  obtain ⟨Np, hp⟩ := (etaLaw_norming hc hne hS hDA).1.pos
  obtain ⟨Nqp, hNqp⟩ := eventually_atTop.mp (hq.eventually (eventually_ge_atTop Np))
  refine ⟨max (max Nq Nr) Nqp, fun n hn j => ?_⟩
  have hnq : Nq ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnr : Nr ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnp : Nqp ≤ n := (le_max_right _ _).trans hn
  have haq : a (qN μ n u) ≠ 0 := (hp _ (hNqp n hnp)).ne'
  have hrclose : |a n / a (qN μ n u) - L| ≤ min 1 δ₂ := by
    simpa only [Real.dist_eq] using (hNr n hnr).le
  have hrbound : |a n / a (qN μ n u)| ≤ L + 1 := by
    have hh := abs_add_le (a n / a (qN μ n u) - L) L
    rw [sub_add_cancel, abs_of_pos hL] at hh
    linarith [hrclose.trans (min_le_left 1 δ₂)]
  let z : ℝ := ((n : ℝ) - j - cC μ * qN μ n u) / a (qN μ n u)
  have hll : |a (qN μ n u) * intWalkProb (etaLaw μ) (qN μ n u) ((n : ℤ) - j) -
      Scalar.stableDensity θ z| ≤ δ₁ := by
    have hh := hl (qN μ n u) (hNq n hnq) ((n : ℤ) - j)
    simpa only [Int.cast_sub, Int.cast_natCast, cC, a, z, mul_comm (qN μ n u : ℝ)] using hh
  have heq : bN μ θ n u j - Qn μ θ n u j =
      (a n / a (qN μ n u)) *
        (a (qN μ n u) * intWalkProb (etaLaw μ) (qN μ n u) ((n : ℤ) - j) - Scalar.stableDensity θ z) +
      (a n / a (qN μ n u) - L) * Scalar.stableDensity θ z := by
    change a n * intWalkProb (etaLaw μ) (qN μ n u) ((n : ℤ) - j) - L * Scalar.stableDensity θ z = _
    field_simp
    ring
  rw [heq]
  calc
    _ ≤ |(a n / a (qN μ n u)) *
        (a (qN μ n u) * intWalkProb (etaLaw μ) (qN μ n u) ((n : ℤ) - j) - Scalar.stableDensity θ z)| +
      |(a n / a (qN μ n u) - L) * Scalar.stableDensity θ z| := abs_add_le _ _
    _ ≤ (L + 1) * δ₁ + δ₂ * (M + 1) := by
      rw [abs_mul, abs_mul]
      exact add_le_add (mul_le_mul hrbound hll (abs_nonneg _) (by positivity))
        (mul_le_mul (hrclose.trans (min_le_right _ _)) ((hbound z).trans (by linarith))
          (abs_nonneg _) hδ₂.le)
    _ = ε' := by dsimp [δ₁, δ₂]; field_simp; ring

private theorem step_bp_ratio : ∃ R : ℝ,
    Tendsto (fun n : ℕ => norming (stepLaw μ) θ n / norming (etaLaw μ) θ n) atTop (𝓝 R) := by
  by_cases hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)
  · let sp := Real.sqrt (StableAnalysis.variance (etaLaw μ))
    have hS := NormRatios.hS_of_nonLattice hc hne hnl
    have hsp : 0 < sp := Real.sqrt_pos.mpr (LeafMass.YLaw.variance_etaLaw_pos hc hne hS
      (integrable_sq_etaLaw hc hne hfin))
    refine ⟨Real.sqrt (StableAnalysis.variance (stepLaw μ)) / sp, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt ((n : ℝ) / 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    rw [norming_of_integrable_sq hfin, norming_etaLaw_finiteVariance hc hne hfin]
    dsimp only [sp]
    field_simp
  · refine ⟨((1 - (μ 0).toReal) ^ (-(1 / θ)))⁻¹, ?_⟩
    have hh := (lem_hhp hc hne hap hDA hfin).inv₀
      (Real.rpow_pos_of_pos (EtaTransfer.one_sub_apply_zero_pos hc hne) _).ne'
    simpa only [inv_div] using hh

private theorem centered_qN (u : ℝ) :
    Tendsto (fun n : ℕ => ((n : ℝ) - cC μ * qN μ n u) / Real.sqrt n)
      atTop (𝓝 (-cC μ * u)) := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  have hm1 : (μ 0).toReal < 1 := by linarith
  have ht := (rN_centered hm u).div_const (1 - (μ 0).toReal)
  have hlim : (-(μ 0).toReal * u) / (1 - (μ 0).toReal) = -cC μ * u := by dsimp [cC]; ring
  rw [hlim] at ht
  apply ht.congr'
  filter_upwards [(qN_atTop hm hm1 u).eventually (eventually_ge_atTop 1)] with n hn
  have hnr : n ≤ rN μ n u := by dsimp [qN] at hn; omega
  rw [qN, Nat.cast_sub hnr]
  dsimp [cC]
  field_simp
  ring

private theorem centered_div_bp_qN (u : ℝ) {l : ℝ}
    (hs : Tendsto (fun n : ℕ => Real.sqrt n / norming (etaLaw μ) θ (qN μ n u)) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => ((n : ℝ) - cC μ * qN μ n u) / norming (etaLaw μ) θ (qN μ n u))
      atTop (𝓝 ((-cC μ * u) * l)) := by
  have ht := (centered_qN hc hne hap hDA hnl u).mul hs
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  field_simp

private theorem sqrt_div_qN_of_sqrt_div_bp (u : ℝ) {l : ℝ}
    (hs : Tendsto (fun n : ℕ => Real.sqrt n / norming (etaLaw μ) θ n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => Real.sqrt n / norming (etaLaw μ) θ (qN μ n u))
      atTop (𝓝 (l * cC μ ^ (1 / θ))) := by
  have ht := hs.mul (bp_div_qN hc hne hap hDA hnl u)
  obtain ⟨Np, hp⟩ := (etaLaw_norming hc hne (NormRatios.hS_of_nonLattice hc hne hnl) hDA).1.pos
  apply ht.congr'
  filter_upwards [eventually_ge_atTop Np] with n hn
  have han := (hp n hn).ne'
  field_simp

private theorem sqrt_div_step_lt_two (hθ : θ < 2) :
    Tendsto (fun n : ℕ => Real.sqrt n / norming (stepLaw μ) θ n) atTop (𝓝 0) := by
  obtain ⟨b, hb⟩ := hDA
  have hDA' : ∃ b, IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b :=
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA'
  have hmono := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA').1
  rw [mean_stepLaw hc] at ha
  obtain ⟨a, heq, h⟩ := ha.exists_stableDomain hc hne hmono
  have hρ : (1 / 2 : ℝ) < 1 / θ := by
    rw [lt_div_iff₀ (by linarith [h.alpha_mem.1] : 0 < θ)]
    linarith
  let δ : ℝ := (1 / θ - 1 / 2) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have he := (Scalar.regularlyVaryingSeq h).eventually_rpow_le_le h.monotone h.pos
    (by linarith : 0 ≤ 1 / θ) hδ
  have hbnd : ∀ᶠ n : ℕ in atTop, 0 ≤ Real.sqrt n / a n ∧
      Real.sqrt n / a n ≤ (n : ℝ) ^ (-δ) := by
    filter_upwards [he, eventually_ge_atTop 1] with n hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    refine ⟨div_nonneg (Real.sqrt_nonneg _) (h.pos n hn1).le, ?_⟩
    calc
      _ ≤ Real.sqrt n / (n : ℝ) ^ (1 / θ - δ) :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) (Real.rpow_pos_of_pos hnR _) hn.1
      _ = (n : ℝ) ^ (-δ) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hnR]
        congr 1
        dsimp [δ]
        ring
  have ht : Tendsto (fun n : ℕ => Real.sqrt n / a n) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      ((tendsto_rpow_neg_atTop hδ).comp tendsto_natCast_atTop_atTop)
      (hbnd.mono fun _ hn => hn.1) (hbnd.mono fun _ hn => hn.2)
  exact ht.congr' (heq.mono fun n hn => by rw [hn])

private theorem bp_qN_sqrt_finite
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) (u : ℝ) :
    Tendsto (fun n : ℕ => Real.sqrt n / norming (etaLaw μ) θ (qN μ n u)) atTop
      (𝓝 (Real.sqrt (2 * cC μ) / Real.sqrt (StableAnalysis.variance (etaLaw μ)))) := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hl : 0 < (1 - (μ 0).toReal) / (μ 0).toReal := div_pos (by linarith) hm
  have ht := (((qN_ratio hm hm1 u).inv₀ hl.ne').const_mul (2 : ℝ)).sqrt.div_const
    (Real.sqrt (StableAnalysis.variance (etaLaw μ)))
  have hlim : ((1 - (μ 0).toReal) / (μ 0).toReal)⁻¹ = cC μ := by rw [inv_div]; rfl
  rw [hlim] at ht
  change Tendsto (fun n : ℕ => Real.sqrt (2 * (((qN μ n u : ℝ) / n)⁻¹)) /
    Real.sqrt (StableAnalysis.variance (etaLaw μ))) atTop
    (𝓝 (Real.sqrt (2 * cC μ) / Real.sqrt (StableAnalysis.variance (etaLaw μ)))) at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1, (qN_atTop hm hm1 u).eventually (eventually_ge_atTop 1)] with n hn hqn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hqR : (qN μ n u : ℝ) ≠ 0 := by exact_mod_cast (show qN μ n u ≠ 0 by omega)
  have heq : 2 * ((qN μ n u : ℝ) / n)⁻¹ = (n : ℝ) / ((qN μ n u : ℝ) / 2) := by field_simp
  rw [heq, Real.sqrt_div (Nat.cast_nonneg _), norming_etaLaw_finiteVariance hc hne hfin]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem Kn_uniform_of_center (u : ℝ)
    (hcenter : Tendsto (fun n : ℕ => ((n : ℝ) - cC μ * qN μ n u) /
        norming (etaLaw μ) θ (qN μ n u) + finVarShift μ u) atTop (𝓝 0))
    {α : ℝ} (hα : 0 < α) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n → Kn μ θ n u j ≤ ε' := by
  let a : ℕ → ℝ := norming (etaLaw μ) θ
  let L : ℝ := cC μ ^ (1 / θ)
  let z : ℕ → ℝ := fun n => ((n : ℝ) - cC μ * qN μ n u) / a (qN μ n u) + finVarShift μ u
  obtain ⟨R, hR⟩ := step_bp_ratio hc hne hap hDA hnl
  have hdiff : Tendsto (fun n : ℕ => |L - a n / a (qN μ n u)|) atTop (𝓝 0) := by
    have hh := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => L) atTop (𝓝 L)).sub
      (bp_div_qN hc hne hap hDA hnl u)).abs
    simpa only [L, a, sub_self, abs_zero] using hh
  have he : Tendsto (fun n : ℕ => |z n| + α * |norming (stepLaw μ) θ n / a n| *
      |L - a n / a (qN μ n u)|) atTop (𝓝 0) := by
    have ht := hcenter.abs.add ((hR.abs.const_mul α).mul hdiff)
    simpa only [sub_self, abs_zero, mul_zero, add_zero] using ht
  obtain ⟨Ne, hNe⟩ := Metric.tendsto_atTop.mp he ε' hε'
  have hS := NormRatios.hS_of_nonLattice hc hne hnl
  obtain ⟨Np, hp⟩ := (etaLaw_norming hc hne hS hDA).1.pos
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  obtain ⟨Nq, hNq⟩ := eventually_atTop.mp ((qN_atTop hm hm1 u).eventually (eventually_ge_atTop Np))
  refine ⟨max (max Ne Np) Nq, fun n hn j hj => ?_⟩
  have hne : Ne ≤ n := (le_max_left _ _).trans ((le_max_left _ _).trans hn)
  have hnp : Np ≤ n := (le_max_right _ _).trans ((le_max_left _ _).trans hn)
  have hnq : Nq ≤ n := (le_max_right _ _).trans hn
  have han : 0 < a n := hp n hnp
  have haq : 0 < a (qN μ n u) := hp _ (hNq n hnq)
  have hj' : |(j : ℝ) / a n| ≤ α * |norming (stepLaw μ) θ n / a n| := by
    rw [abs_div, abs_of_pos han]
    rw [normB_natCast] at hj
    calc
      _ ≤ (α * norming (stepLaw μ) θ n) / a n := div_le_div_of_nonneg_right hj han.le
      _ = α * (norming (stepLaw μ) θ n / a n) := by ring
      _ ≤ α * |norming (stepLaw μ) θ n / a n| := mul_le_mul_of_nonneg_left (le_abs_self _) hα.le
  have hid : ((n : ℝ) - j - cC μ * qN μ n u) / a (qN μ n u) +
      L * ((j : ℝ) / a n) + finVarShift μ u = z n + ((j : ℝ) / a n) * (L - a n / a (qN μ n u)) := by
    dsimp only [z]
    field_simp
    ring
  change |((n : ℝ) - j - cC μ * qN μ n u) / a (qN μ n u) +
      L * ((j : ℝ) / a n) + finVarShift μ u| ≤ ε'
  rw [hid]
  calc
    _ ≤ |z n| + |((j : ℝ) / a n) * (L - a n / a (qN μ n u))| := abs_add_le _ _
    _ ≤ |z n| + α * |norming (stepLaw μ) θ n / a n| * |L - a n / a (qN μ n u)| := by
      rw [abs_mul]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hj' (abs_nonneg _))
    _ ≤ ε' := (le_abs_self _).trans (by simpa only [Real.dist_eq, sub_zero] using (hNe n hne).le)

private theorem step_norming_pos : ∀ᶠ n : ℕ in atTop, 0 < norming (stepLaw μ) θ n := by
  obtain ⟨b, hb⟩ := hDA
  obtain ⟨N, hN⟩ := (locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩).pos
  exact eventually_atTop.mpr ⟨N, hN⟩

theorem Kn_tendsto_finiteVariance
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) (u : ℝ) {α : ℝ} (hα : 0 < α)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n → Kn μ θ n u j ≤ ε' := by
  have hcC : 0 < cC μ := div_pos
    (ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0))
    (EtaTransfer.one_sub_apply_zero_pos hc hne)
  have hs := bp_qN_sqrt_finite hc hne hap hDA hnl hfin u
  have ht := (centered_div_bp_qN hc hne hap hDA hnl u hs).add_const (finVarShift μ u)
  have h32 : cC μ ^ (3 / 2 : ℝ) = cC μ * Real.sqrt (cC μ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hcC, Real.rpow_one,
      ← Real.sqrt_eq_rpow]
  have hcancel : (-cC μ * u) *
      (Real.sqrt (2 * cC μ) / Real.sqrt (StableAnalysis.variance (etaLaw μ))) + finVarShift μ u = 0 := by
    rw [finVarShift, ite_eq_left hfin, h32, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  rw [hcancel] at ht
  exact Kn_uniform_of_center hc hne hap hDA hnl u ht hα hε'

theorem Kn_tendsto_infiniteVariance_lt_two (hθ : θ < 2)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) (u : ℝ) {α : ℝ} (hα : 0 < α)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n → Kn μ θ n u j ≤ ε' := by
  obtain ⟨R, hR⟩ := step_bp_ratio hc hne hap hDA hnl
  have ht := (sqrt_div_step_lt_two hc hne hap hDA hnl hθ).mul hR
  simp only [zero_mul] at ht
  have hs : Tendsto (fun n : ℕ => Real.sqrt n / norming (etaLaw μ) θ n) atTop (𝓝 0) := ht.congr' (by
    filter_upwards [step_norming_pos hc hne hap hDA hnl] with n hn
    have hB := hn.ne'
    field_simp)
  have hs' := sqrt_div_qN_of_sqrt_div_bp hc hne hap hDA hnl u hs
  simp only [zero_mul] at hs'
  have hh := (centered_div_bp_qN hc hne hap hDA hnl u hs').add_const (finVarShift μ u)
  simp only [mul_zero, finVarShift, ite_eq_right hinf, add_zero] at hh
  exact Kn_uniform_of_center hc hne hap hDA hnl u
    (by simpa only [finVarShift, ite_eq_right hinf, add_zero] using hh) hα hε'

theorem Kn_tendsto_theta_two_infiniteVariance (hθ : θ = 2)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) (u : ℝ) {α : ℝ} (hα : 0 < α)
    {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n → Kn μ θ n u j ≤ ε' := by
  subst θ
  have ht := (LeafMass.YLaw.etaLaw_gauss_hprime_tendsto hc hne hDA hinf).inv_tendsto_atTop
  have hs : Tendsto (fun n : ℕ => Real.sqrt n / norming (etaLaw μ) 2 n) atTop (𝓝 0) := by
    apply ht.congr'
    exact Eventually.of_forall fun n => by
      change (norming (etaLaw μ) 2 n / Real.sqrt n)⁻¹ = Real.sqrt n / norming (etaLaw μ) 2 n
      exact inv_div _ _
  have hs' := sqrt_div_qN_of_sqrt_div_bp hc hne hap hDA hnl u hs
  simp only [zero_mul] at hs'
  have hh := (centered_div_bp_qN hc hne hap hDA hnl u hs').add_const (finVarShift μ u)
  simp only [mul_zero, finVarShift, ite_eq_right hinf, add_zero] at hh
  exact Kn_uniform_of_center hc hne hap hDA hnl u
    (by simpa only [finVarShift, ite_eq_right hinf, add_zero] using hh) hα hε'

theorem eq_cvmoche (u : ℝ) {α : ℝ} (hα : 0 < α) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |Qn μ θ n u j - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ ε' := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  obtain ⟨K, hLip⟩ : ∃ K : ℝ≥0, LipschitzWith K (Scalar.stableDensity θ) :=
    ⟨_, Scalar.lipschitzWith_stableDensity hb.alpha_mem⟩
  let L : ℝ := cC μ ^ (1 / θ)
  have hcC : 0 < cC μ := div_pos
    (ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0))
    (EtaTransfer.one_sub_apply_zero_pos hc hne)
  have hL : 0 < L := Real.rpow_pos_of_pos hcC _
  let δ : ℝ := ε' / (L * (K : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hK : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ,
      |(j : ℝ)| ≤ α * normB μ θ n → Kn μ θ n u j ≤ δ := by
    by_cases hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)
    · exact Kn_tendsto_finiteVariance hc hne hap hDA hnl hfin u hα hδ
    · by_cases hθ : θ < 2
      · exact Kn_tendsto_infiniteVariance_lt_two hc hne hap hDA hnl hθ hfin u hα hδ
      · have hθ2 : θ = 2 := le_antisymm hb.alpha_mem.2 (le_of_not_gt hθ)
        exact Kn_tendsto_theta_two_infiniteVariance hc hne hap hDA hnl hθ2 hfin u hα hδ
  obtain ⟨N, hN⟩ := hK
  refine ⟨N, fun n hn j hj => ?_⟩
  let x₁ : ℝ := ((n : ℝ) - j - cC μ * qN μ n u) / norming (etaLaw μ) θ (qN μ n u)
  let x₂ : ℝ := -(L * ((j : ℝ) / norming (etaLaw μ) θ n)) - finVarShift μ u
  have harg : |x₁ - x₂| = Kn μ θ n u j := by
    dsimp [x₁, x₂, Kn, L]
    congr 1
    ring
  have hd : |Scalar.stableDensity θ x₁ - Scalar.stableDensity θ x₂| ≤ (K : ℝ) * Kn μ θ n u j := by
    have hh := hLip.dist_le_mul x₁ x₂
    rwa [Real.dist_eq, Real.dist_eq, harg] at hh
  change |L * Scalar.stableDensity θ x₁ - L * Scalar.stableDensity θ x₂| ≤ ε'
  rw [← mul_sub, abs_mul, abs_of_pos hL]
  calc
    _ ≤ L * ((K : ℝ) * Kn μ θ n u j) := mul_le_mul_of_nonneg_left hd hL.le
    _ ≤ L * ((K : ℝ) * δ) := by gcongr; exact hN n hn j hj
    _ ≤ (L * (K : ℝ) + 1) * δ := by nlinarith [hδ.le]
    _ = ε' := by dsimp [δ]; field_simp

theorem bN_tendsto_signed (u : ℝ) {α : ℝ} (hα : 0 < α) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |bN μ θ n u j - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ ε' := by
  obtain ⟨N₁, h₁⟩ := bN_sub_Qn hc hne hap hDA hnl u (half_pos hε')
  obtain ⟨N₂, h₂⟩ := eq_cvmoche hc hne hap hDA hnl u hα (half_pos hε')
  refine ⟨max N₁ N₂, fun n hn j hj => ?_⟩
  calc
    _ ≤ |bN μ θ n u j - Qn μ θ n u j| +
      |Qn μ θ n u j - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| := abs_sub_le _ _ _
    _ ≤ ε' / 2 + ε' / 2 := add_le_add (h₁ n (le_of_max_le_left hn) j) (h₂ n (le_of_max_le_right hn) j hj)
    _ = ε' := by ring

private theorem techniqueError_tendsto {α ε : ℝ} (hα : 0 < α) (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) (u : ℝ) :
    Tendsto (fun n : ℕ => techniqueError μ θ α ε n u) atTop (𝓝 0) := by
  have h0 := hc.apply_zero_ne_zero hne
  have h1 := NormRatios.mu0_ne_one hc hne
  obtain ⟨Cb, Nb, hb⟩ := bN_bounded hc hne hap hDA hnl hε0 hε1
  rw [Metric.tendsto_atTop]
  intro η hη
  let δa : ℝ := η / (4 * (|Cb| + 1))
  let δb : ℝ := η / (4 * (|F0 (μ 0).toReal u| + 1))
  have hδa : 0 < δa := by dsimp [δa]; positivity
  have hδb : 0 < δb := by dsimp [δb]; positivity
  obtain ⟨Na, ha⟩ := Metric.tendsto_atTop.mp (aN_tendsto h0 h1 u) δa hδa
  obtain ⟨Nbn, hbn⟩ := bN_tendsto_signed hc hne hap hDA hnl u hα hδb
  have hwindow : ∀ᶠ n : ℕ in atTop, |u| ≤ ε * Real.sqrt n :=
    (Filter.Tendsto.const_mul_atTop hε0 (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop |u|)
  obtain ⟨Nw, hw⟩ := eventually_atTop.mp hwindow
  obtain ⟨Np, hp⟩ := eventually_atTop.mp (step_norming_pos hc hne hap hDA hnl)
  refine ⟨max Na (max Nbn (max Nb (max Nw Np))), fun n hn => ?_⟩
  have hna : Na ≤ n := by omega
  have hnbn : Nbn ≤ n := by omega
  have hnb : Nb ≤ n := by omega
  have hnw : Nw ≤ n := by omega
  have hnp : Np ≤ n := by omega
  have hu := hw n hnw
  have hwin : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n) := abs_le.mp hu
  have hαB : 0 ≤ α * normB μ θ n := by rw [normB_natCast]; exact mul_nonneg hα.le (hp n hnp).le
  let f : ℕ → ℝ := fun j => |aWindow μ ε n u * bN μ θ n u j -
    F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)|
  have hf : ∀ j ∈ Finset.Icc 1 ⌊α * normB μ θ n⌋₊, 0 ≤ f j ∧ f j ≤ η / 2 := by
    intro j hj
    have hjcast : (j : ℝ) ≤ (⌊α * normB μ θ n⌋₊ : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hj).2
    have hjr := hjcast.trans (Nat.floor_le hαB)
    have hja : |((j : ℤ) : ℝ)| ≤ α * normB μ θ n := by
      simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg j : (0 : ℝ) ≤ j)] using hjr
    have haclose : |aN μ n u - F0 (μ 0).toReal u| ≤ δa := by
      simpa only [Real.dist_eq] using (ha n hna).le
    have hbclose : |bN μ θ n u j - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ δb := by
      simpa only [Int.cast_natCast] using hbn n hnbn (j : ℤ) hja
    have hbbound : |bN μ θ n u j| ≤ |Cb| := (hb n hnb u hu j).trans (le_abs_self Cb)
    refine ⟨abs_nonneg _, ?_⟩
    dsimp only [f]
    rw [aWindow, Set.indicator_of_mem hwin]
    calc
      _ = |(aN μ n u - F0 (μ 0).toReal u) * bN μ θ n u j +
        F0 (μ 0).toReal u * (bN μ θ n u j - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n))| := by congr 1; ring
      _ ≤ |(aN μ n u - F0 (μ 0).toReal u) * bN μ θ n u j| +
        |F0 (μ 0).toReal u * (bN μ θ n u j - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n))| := abs_add_le _ _
      _ ≤ δa * |Cb| + |F0 (μ 0).toReal u| * δb := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul haclose hbbound (abs_nonneg _) hδa.le)
          (mul_le_mul_of_nonneg_left hbclose (abs_nonneg _))
      _ ≤ δa * (|Cb| + 1) + (|F0 (μ 0).toReal u| + 1) * δb := by nlinarith [hδa.le, hδb.le]
      _ = η / 2 := by dsimp [δa, δb]; field_simp; ring
  have hs := supJ_bounds (by positivity : 0 ≤ η / 2) hf
  change dist (supJ (Finset.Icc 1 ⌊α * normB μ θ n⌋₊) f) 0 < η
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
  exact lt_of_le_of_lt hs.2.1 (by linarith)

private theorem techniqueError_domination {α ε : ℝ} (_hα : 0 < α) (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    ∃ g : ℝ → ℝ, Integrable g ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ u : ℝ,
      0 ≤ techniqueError μ θ α ε n u ∧ techniqueError μ θ α ε n u ≤ g u ∧
      ∀ j ∈ Finset.Icc 1 ⌊α * normB μ θ n⌋₊,
        |aWindow μ ε n u * bN μ θ n u j -
          F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ techniqueError μ θ α ε n u := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hcC : 0 < cC μ := div_pos hm (by linarith)
  let L : ℝ := cC μ ^ (1 / θ)
  have hL : 0 < L := Real.rpow_pos_of_pos hcC _
  obtain ⟨Ca, Na, ha⟩ := aN_majorant (hc.apply_zero_ne_zero hne) (NormRatios.mu0_ne_one hc hne) hε0 hε1
  obtain ⟨Cb, Nb, hb⟩ := bN_bounded hc hne hap hDA hnl hε0 hε1
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  let g : ℝ → ℝ := fun u => |Ca| * |Cb| / max 1 (u ^ 2) + (L * M) * |F0 (μ 0).toReal u|
  have hgi : Integrable g := by
    have hh := (window_weight_integrable.const_mul (|Ca| * |Cb|)).add
      ((F0_integrable hm hm1).abs.const_mul (L * M))
    convert hh using 1
    ext u
    simp only [g, Pi.add_apply, div_eq_mul_inv, one_mul]
  refine ⟨g, hgi, max Na Nb, fun n hn u => ?_⟩
  have hna : Na ≤ n := by omega
  have hnb : Nb ≤ n := by omega
  have hg0 : 0 ≤ g u := by dsimp [g]; positivity
  have hf (j : ℕ) : 0 ≤ |aWindow μ ε n u * bN μ θ n u j -
      F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ∧
      |aWindow μ ε n u * bN μ θ n u j -
      F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ g u := by
    refine ⟨abs_nonneg _, ?_⟩
    have hprod : |aWindow μ ε n u * bN μ θ n u j| ≤ |Ca| * |Cb| / max 1 (u ^ 2) := by
      by_cases hwin : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
      · have hu : |u| ≤ ε * Real.sqrt n := abs_le.mpr hwin
        have hCa : aN μ n u ≤ |Ca| / max 1 (u ^ 2) :=
          (ha n hna u hu).trans (div_le_div_of_nonneg_right (le_abs_self Ca) (by positivity))
        have hCb : |bN μ θ n u j| ≤ |Cb| := (hb n hnb u hu j).trans (le_abs_self Cb)
        rw [aWindow, Set.indicator_of_mem hwin, abs_mul, abs_of_nonneg (aN_nonneg μ n u)]
        calc
          _ ≤ (|Ca| / max 1 (u ^ 2)) * |Cb| := mul_le_mul hCa hCb (abs_nonneg _) (by positivity)
          _ = |Ca| * |Cb| / max 1 (u ^ 2) := by ring
      · rw [aWindow, Set.indicator_of_notMem hwin, zero_mul, abs_zero]
        positivity
    have hG : |G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ L * M := by
      change |L * Scalar.stableDensity θ _| ≤ L * M
      rw [abs_mul, abs_of_pos hL]
      exact mul_le_mul_of_nonneg_left (hbound _) hL.le
    have hh := abs_sub_le (aWindow μ ε n u * bN μ θ n u j) 0
      (F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    calc
      _ ≤ |aWindow μ ε n u * bN μ θ n u j| +
        |F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| := hh
      _ ≤ |Ca| * |Cb| / max 1 (u ^ 2) + |F0 (μ 0).toReal u| * (L * M) := by
        rw [abs_mul (F0 _ u)]
        exact add_le_add hprod (mul_le_mul_of_nonneg_left hG (abs_nonneg _))
      _ = g u := by dsimp [g]; ring
  exact supJ_bounds hg0 (fun j _ => hf j)

private theorem techniqueError_integral {α ε : ℝ} (hα : 0 < α) (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    Tendsto (fun n : ℕ => ∫ u, techniqueError μ θ α ε n u) atTop (𝓝 0) ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Integrable (techniqueError μ θ α ε n) ∧
        ∀ u : ℝ, 0 ≤ techniqueError μ θ α ε n u ∧
          ∀ j ∈ Finset.Icc 1 ⌊α * normB μ θ n⌋₊,
            |aWindow μ ε n u * bN μ θ n u j -
              F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ techniqueError μ θ α ε n u := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  obtain ⟨g, hgi, N, hbnd⟩ := techniqueError_domination hc hne hap hDA hnl hα hε0 hε1
  have hmeas n := (techniqueError_measurable hb.alpha_mem α ε n (μ := μ)).aestronglyMeasurable (μ := volume)
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ u : ℝ, ‖techniqueError μ θ α ε n u‖ ≤ g u := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbnd n hn u).1]
      exact (hbnd n hn u).2.1
  have ht := tendsto_integral_filter_of_dominated_convergence g (Eventually.of_forall hmeas)
    hbound hgi (Eventually.of_forall (fun u => techniqueError_tendsto hc hne hap hDA hnl hα hε0 hε1 u))
  refine ⟨by simpa only [integral_zero] using ht, N, fun n hn => ?_⟩
  refine ⟨hgi.mono' (hmeas n) (Eventually.of_forall fun u => ?_), fun u => ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hbnd n hn u).1]
    exact (hbnd n hn u).2.1
  · exact ⟨(hbnd n hn u).1, (hbnd n hn u).2.2⟩

theorem eq_lemtechnique2 {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    Tendsto (fun n : ℕ => ∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
        supJ (Finset.Icc 1 ⌊α * normB μ θ n⌋₊) fun j =>
          |aN μ n u * bN μ θ n u (j : ℤ) -
            F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)|)
      atTop (𝓝 0) := by
  obtain ⟨ht, N, hN⟩ := techniqueError_integral hc hne hap hDA hnl hα hε0 hε1
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · filter_upwards [eventually_ge_atTop N] with n hn
    apply intervalIntegral.integral_nonneg
      (by nlinarith [mul_nonneg hε0.le (Real.sqrt_nonneg (n : ℝ))])
    intro u hu
    have hh := (hN n hn).2 u |>.1
    simpa only [techniqueError, aWindow, Set.indicator_of_mem hu] using hh
  · filter_upwards [eventually_ge_atTop N] with n hn
    have hi := (hN n hn).1
    have hnonneg := fun u => (hN n hn).2 u |>.1
    have heq : (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
        supJ (Finset.Icc 1 ⌊α * normB μ θ n⌋₊) fun j =>
          |aN μ n u * bN μ θ n u j - F0 (μ 0).toReal u *
            G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)|) =
        ∫ u in Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n), techniqueError μ θ α ε n u := by
      rw [intervalIntegral.integral_of_le (by nlinarith [mul_nonneg hε0.le (Real.sqrt_nonneg (n : ℝ))]),
        ← integral_Icc_eq_integral_Ioc]
      apply setIntegral_congr_fun measurableSet_Icc
      intro u hu
      simp only [techniqueError, aWindow, Set.indicator_of_mem hu]
    rw [heq, ← integral_indicator measurableSet_Icc]
    exact integral_mono (hi.indicator measurableSet_Icc) hi fun u => by
      by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
      · rw [Set.indicator_of_mem hu]
      · rw [Set.indicator_of_notMem hu]; exact hnonneg u

private theorem G0_product_integrable (x : ℝ) :
    Integrable (fun u : ℝ => F0 (μ 0).toReal u * G0 μ θ u x) := by
  obtain ⟨b, hb⟩ := hDA
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hL : 0 ≤ cC μ ^ (1 / θ) := Real.rpow_nonneg (div_nonneg hm.le (by linarith)) _
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  apply (((F0_integrable hm hm1).abs).mul_const (cC μ ^ (1 / θ) * M)).mono'
    (((by unfold F0; fun_prop : Continuous (F0 (μ 0).toReal)).mul (G0_continuous (μ := μ) hb.alpha_mem x)).aestronglyMeasurable)
  exact Eventually.of_forall fun u => by
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    change |cC μ ^ (1 / θ) * Scalar.stableDensity θ _| ≤ cC μ ^ (1 / θ) * M
    rw [abs_mul, abs_of_nonneg hL]
    exact mul_le_mul_of_nonneg_left (hbound _) hL

theorem eq_lemtechnique1 {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
            aN μ n u * bN μ θ n u (j : ℤ)) -
        (μ 0).toReal * ∫ u : ℝ, F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ ε' := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  obtain ⟨ht, N, hN⟩ := techniqueError_integral hc hne hap hDA hnl hα hε0 hε1
  have hlim : Tendsto (fun n : ℕ => (μ 0).toReal * ∫ u, techniqueError μ θ α ε n u) atTop (𝓝 0) := by
    simpa using ht.const_mul (μ 0).toReal
  obtain ⟨N', hN'⟩ := Metric.tendsto_atTop.mp hlim ε' hε'
  refine ⟨max N N', fun n hn j hj hjup => ?_⟩
  have hnN : N ≤ n := by omega
  have hnN' : N' ≤ n := by omega
  have hjS : j ∈ Finset.Icc 1 ⌊α * normB μ θ n⌋₊ := Finset.mem_Icc.mpr ⟨hj, Nat.le_floor hjup⟩
  let D : ℝ → ℝ := fun u => aWindow μ ε n u * bN μ θ n u j -
      F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)
  have hdmeas : Measurable D := by
    have ha := (aN_measurable μ n).indicator (s := Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)) measurableSet_Icc
    simpa only [D, aWindow, Pi.mul_def, Pi.sub_def] using (ha.mul (bN_measurable μ θ n j)).sub
      ((by unfold F0; fun_prop : Continuous (F0 (μ 0).toReal)).measurable.mul
        (G0_continuous (μ := μ) hb.alpha_mem ((j : ℝ) / norming (etaLaw μ) θ n)).measurable)
  have hDi : Integrable D := (hN n hnN).1.mono' hdmeas.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact (hN n hnN).2 u |>.2 j hjS)
  have hFG := G0_product_integrable hc hne hap hDA hnl ((j : ℝ) / norming (etaLaw μ) θ n)
  have hprod : Integrable (fun u => aWindow μ ε n u * bN μ θ n u j) := by
    convert hDi.add hFG using 1
    ext u
    dsimp [D]
    ring
  have heq : (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u j) =
      ∫ u, aWindow μ ε n u * bN μ θ n u j := by
    rw [intervalIntegral.integral_of_le (by nlinarith [mul_nonneg hε0.le (Real.sqrt_nonneg (n : ℝ))]),
      ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
      · simp only [aWindow, Set.indicator_of_mem hu]
      · simp only [aWindow, Set.indicator_of_notMem hu, zero_mul]
  rw [heq, ← mul_sub, ← integral_sub hprod hFG, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    _ ≤ (μ 0).toReal * (∫ u, techniqueError μ θ α ε n u) := by
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      apply (abs_integral_le_integral_abs (f := D)).trans
      exact integral_mono hDi.abs (hN n hnN).1 fun u => (hN n hnN).2 u |>.2 j hjS
    _ ≤ ε' := by
      have hh := (hN' n hnN').le
      rw [Real.dist_eq, sub_zero] at hh
      exact (le_abs_self _).trans hh

private theorem normBp_eventually_pos : ∀ᶠ n : ℕ in atTop, 0 < norming (etaLaw μ) θ n := by
  let := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have ha := (etaLaw_norming hc hne (NormRatios.hS_of_nonLattice hc hne hnl) hDA).1
  exact (TransformConvergence.tendsto_atTop (etaLaw μ) ha).eventually (eventually_gt_atTop 0)

private theorem density_norm_compare {r : ℝ} (hr : 0 < r)
    (ht : Tendsto (fun n : ℕ => norming (etaLaw μ) θ n /
        normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 r))
    {α : ℝ} (hα : 0 < α) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, (j : ℝ) ≤ α * normB μ θ n →
      |r * Scalar.stableDensity θ (-(r * ((j : ℝ) / norming (etaLaw μ) θ n))) -
        r * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ η := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  obtain ⟨R, hR⟩ := step_bp_ratio hc hne hap hDA hnl
  obtain ⟨K, hLip⟩ : ∃ K : ℝ≥0, LipschitzWith K (Scalar.stableDensity θ) :=
    ⟨_, Scalar.lipschitzWith_stableDensity hb.alpha_mem⟩
  let A : ℝ := α * (|R| + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hnorm : ∀ᶠ n : ℕ in atTop, normB μ θ n / norming (etaLaw μ) θ n ≤ |R| + 1 := by
    filter_upwards [hR.eventually (Metric.ball_mem_nhds R zero_lt_one)] with n hn
    rw [Real.dist_eq] at hn
    have := le_abs_self (norming (stepLaw μ) θ n / norming (etaLaw μ) θ n - R)
    rw [normB_natCast]
    linarith [le_abs_self R]
  have hsmall : Tendsto (fun n : ℕ => (r * (K : ℝ) * A) *
      |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)|) atTop (𝓝 0) := by
    simpa using ((((tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).sub ht).abs).const_mul (r * (K : ℝ) * A))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hsmall.eventually (eventually_lt_nhds hη)).and (hnorm.and (normBp_eventually_pos hc hne hap hDA hnl)))
  refine ⟨N, fun n hn j hj => ?_⟩
  obtain ⟨hs, hnb, hpos⟩ := hN n hn
  have hjpos : 0 ≤ (j : ℝ) / norming (etaLaw μ) θ n := div_nonneg (Nat.cast_nonneg j) hpos.le
  have hjA : (j : ℝ) / norming (etaLaw μ) θ n ≤ A := by
    calc
      _ ≤ α * normB μ θ n / norming (etaLaw μ) θ n := div_le_div_of_nonneg_right hj hpos.le
      _ = α * (normB μ θ n / norming (etaLaw μ) θ n) := by ring
      _ ≤ A := mul_le_mul_of_nonneg_left hnb hα.le
  have heq : -(r * ((j : ℝ) / norming (etaLaw μ) θ n)) -
      (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))) =
      -((j : ℝ) / norming (etaLaw μ) θ n) *
        (r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) := by
    field_simp [hpos.ne']
    ring
  have hd := hLip.dist_le_mul (-(r * ((j : ℝ) / norming (etaLaw μ) θ n)))
    (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))
  rw [Real.dist_eq, Real.dist_eq, heq, abs_mul, abs_neg, abs_of_nonneg hjpos] at hd
  rw [← mul_sub, abs_mul, abs_of_pos hr]
  calc
    _ ≤ r * ((K : ℝ) * (((j : ℝ) / norming (etaLaw μ) θ n) *
      |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)|)) := mul_le_mul_of_nonneg_left hd hr.le
    _ ≤ (r * (K : ℝ) * A) * |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)| := by
      calc
        _ ≤ r * ((K : ℝ) * (A * |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)|)) := by
          apply mul_le_mul_of_nonneg_left _ hr.le
          apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
          exact mul_le_mul_of_nonneg_right hjA (abs_nonneg _)
        _ = _ := by ring
    _ ≤ η := hs.le

private theorem F0_mass {m : ℝ} (hm : 0 < m) (hm1 : m < 1) : m * ∫ u : ℝ, F0 m u = 1 := by
  have hq : 0 < 1 - m := by linarith
  have heq : F0 m = fun u : ℝ => Real.exp (-(m ^ 2 / (2 * (1 - m))) * u ^ 2) /
      Real.sqrt (2 * Real.pi * (1 - m)) := by
    ext u
    unfold F0
    congr 2
    ring
  rw [heq, integral_div, integral_gaussian]
  have ht : 0 ≤ Real.sqrt (Real.pi / (m ^ 2 / (2 * (1 - m)))) := Real.sqrt_nonneg _
  have hd : 0 < Real.sqrt (2 * Real.pi * (1 - m)) := by positivity
  have ht2 := Real.sq_sqrt (by positivity : 0 ≤ Real.pi / (m ^ 2 / (2 * (1 - m))))
  have hd2 := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi * (1 - m))
  have hid : m ^ 2 * (Real.pi / (m ^ 2 / (2 * (1 - m)))) = 2 * Real.pi * (1 - m) := by field_simp
  have hprod : m * Real.sqrt (Real.pi / (m ^ 2 / (2 * (1 - m)))) = Real.sqrt (2 * Real.pi * (1 - m)) := by
    apply (sq_eq_sq₀ (mul_nonneg hm.le ht) hd.le).mp
    rw [mul_pow, ht2, hd2, hid]
  rw [← mul_div_assoc, hprod, div_self hd.ne']

theorem eq_lemtechnique0_infVar
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
            aN μ n u * bN μ θ n u (j : ℤ)) -
        cC μ ^ (1 / θ) * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ ε' := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hL : 0 < cC μ ^ (1 / θ) := Real.rpow_pos_of_pos (div_pos hm (by linarith)) _
  obtain ⟨N₁, hN₁⟩ := eq_lemtechnique1 hc hne hap hDA hnl hα hε0 hε1 (half_pos hε')
  obtain ⟨N₂, hN₂⟩ := density_norm_compare hc hne hap hDA hnl hL
    (NormRatios.normBp_div_normB_infVar hc hne hap hDA hinf) hα (half_pos hε')
  refine ⟨max N₁ N₂, fun n hn j hj hju => ?_⟩
  have heq : (μ 0).toReal * (∫ u : ℝ, F0 (μ 0).toReal u *
      G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)) =
      cC μ ^ (1 / θ) * Scalar.stableDensity θ (-(cC μ ^ (1 / θ) * ((j : ℝ) / norming (etaLaw μ) θ n))) := by
    simp only [G0, finVarShift, ite_eq_right hinf, sub_zero]
    rw [integral_mul_const, ← mul_assoc, F0_mass hc hne hap hDA hnl hm hm1, one_mul]
  calc
    _ ≤ |(μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u j) -
      (μ 0).toReal * ∫ u : ℝ, F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| +
      |(μ 0).toReal * (∫ u : ℝ, F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)) -
        cC μ ^ (1 / θ) * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| := abs_sub_le _ _ _
    _ ≤ ε' / 2 + ε' / 2 := add_le_add (hN₁ n (le_of_max_le_left hn) j hj hju)
      (by rw [heq]; exact hN₂ n (le_of_max_le_right hn) j hju)
    _ = ε' := by ring

private theorem G0_finite (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    (hθ : θ = 2) (u x : ℝ) :
    G0 μ θ u x = G0fv (μ 0).toReal (Real.sqrt (variance (etaLaw μ))) x u := by
  have hle : (μ 0).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
    simpa using this
  have hc0 : 0 ≤ cC μ := div_nonneg ENNReal.toReal_nonneg (sub_nonneg.2 hle)
  subst hθ
  unfold G0 finVarShift G0fv
  simp only [hfin, ite_true]
  rw [stableDensity_two]
  have hs : cC μ ^ (1 / 2 : ℝ) = Real.sqrt (cC μ) := by rw [Real.sqrt_eq_rpow]
  have h32 : cC μ ^ (3 / 2 : ℝ) = cC μ * Real.sqrt (cC μ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hc0 (by norm_num), Real.rpow_one, hs]
  rw [hs, h32]
  unfold cC
  rfl

theorem eq_lemtechnique0_finVar_corrected
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
            aN μ n u * bN μ θ n u (j : ℤ)) -
        Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) / Real.sqrt (variance (stepLaw μ)) *
          Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ ε' := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  have hθ : θ = 2 := DomainCriterion.index_eq_two_of_integrable_sq
    (stableDomain_isStableAttracted hb) (integrable_stepLaw hc) hfin
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hs : 0 < Real.sqrt (variance (stepLaw μ)) := Real.sqrt_pos.mpr (DomainCriterion.variance_pos_of_integrable_sq (stableDomain_isStableAttracted hb) (integrable_stepLaw hc) hfin)
  have hsp : 0 < Real.sqrt (variance (etaLaw μ)) := Real.sqrt_pos.mpr
    (LeafMass.YLaw.variance_etaLaw_pos hc hne (NormRatios.hS_of_nonLattice hc hne hnl)
      (integrable_sq_etaLaw hc hne hfin))
  let r := Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) / Real.sqrt (variance (stepLaw μ))
  have hr : 0 < r := by dsimp [r]; positivity
  have hvar : (Real.sqrt (variance (etaLaw μ))) ^ 2 =
      (Real.sqrt (variance (stepLaw μ))) ^ 2 / (1 - (μ 0).toReal) -
        (μ 0).toReal / (1 - (μ 0).toReal) ^ 2 := by
    rw [Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mp hsp)), Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mp hs))]
    exact variance_etaLaw hc hne hfin
  obtain ⟨N₁, hN₁⟩ := eq_lemtechnique1 hc hne hap hDA hnl hα hε0 hε1 (half_pos hε')
  obtain ⟨N₂, hN₂⟩ := density_norm_compare hc hne hap hDA hnl hr
    (NormRatios.normBp_div_normB_finVar hc hne hap hDA hfin) hα (half_pos hε')
  refine ⟨max N₁ N₂, fun n hn j hj hju => ?_⟩
  have heq : (μ 0).toReal * (∫ u : ℝ, F0 (μ 0).toReal u *
      G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)) =
      r * Scalar.stableDensity θ (-(r * ((j : ℝ) / norming (etaLaw μ) θ n))) := by
    simp_rw [G0_finite hc hne hap hDA hnl hfin hθ]
    rw [gaussian_convolution_identity hm hm1 hs hsp hvar, hθ, stableDensity_two]
    change r * gaussDensity (r * _) = r * gaussDensity (-(r * _))
    unfold gaussDensity
    rw [neg_sq]
  calc
    _ ≤ |(μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u j) -
      (μ 0).toReal * ∫ u : ℝ, F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| +
      |(μ 0).toReal * (∫ u : ℝ, F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)) -
        r * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| := abs_sub_le _ _ _
    _ ≤ ε' / 2 + ε' / 2 := add_le_add (hN₁ n (le_of_max_le_left hn) j hj hju)
      (by rw [heq]; exact hN₂ n (le_of_max_le_right hn) j hju)
    _ = ε' := by ring

private noncomputable def timeError (μ : PMF ℕ) (ε : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)).indicator
    (fun u => |(n : ℝ) / (rN μ n u : ℝ) - (μ 0).toReal| / max 1 (u ^ 2)) u

private theorem timeError_integral {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    Tendsto (fun n : ℕ => ∫ u, timeError μ ε n u) atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → Integrable (timeError μ ε n) ∧ ∀ u, 0 ≤ timeError μ ε n u := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hmeas n : Measurable (timeError μ ε n) := by
    have hr : Measurable (fun u : ℝ => (rN μ n u : ℝ)) :=
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (Nat.measurable_floor.comp (measurable_const.add (measurable_id.mul_const _)))
    unfold timeError
    apply Measurable.indicator _ measurableSet_Icc
    have hratio : Measurable (fun u : ℝ => (n : ℝ) / (rN μ n u : ℝ) - (μ 0).toReal) := by
      simpa only [Pi.div_def, Pi.sub_def] using (measurable_const.div hr).sub measurable_const
    have hden : Measurable (fun u : ℝ => max 1 (u ^ 2)) := by fun_prop
    simpa only [Pi.div_def, Real.norm_eq_abs] using hratio.norm.div hden
  have hb n (hn : 1 ≤ n) u : 0 ≤ timeError μ ε n u ∧ timeError μ ε n u ≤ 2 / max 1 (u ^ 2) := by
    by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
    · obtain ⟨hnr, -, -⟩ := rN_window_bounds hm hm1 hε0 hε1 hn (abs_le.mpr hu)
      have hr : (0 : ℝ) < rN μ n u := by exact_mod_cast (show 0 < rN μ n u by omega)
      have hfrac : (n : ℝ) / (rN μ n u : ℝ) ≤ 1 := (div_le_one hr).mpr (by exact_mod_cast hnr)
      have hnfrac : 0 ≤ (n : ℝ) / (rN μ n u : ℝ) := by positivity
      rw [timeError, Set.indicator_of_mem hu]
      refine ⟨by positivity, div_le_div_of_nonneg_right ?_ (by positivity)⟩
      rw [abs_le]
      constructor <;> linarith
    · rw [timeError, Set.indicator_of_notMem hu]
      exact ⟨le_rfl, by positivity⟩
  have hdom : Integrable (fun u : ℝ => 2 / max 1 (u ^ 2)) := by
    convert window_weight_integrable.const_mul 2 using 1
    ext u
    ring
  have hi n hn : Integrable (timeError μ ε n) := hdom.mono' (hmeas n).aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (hb n hn u).1]; exact (hb n hn u).2)
  have ht u : Tendsto (fun n : ℕ => timeError μ ε n u) atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ => (n : ℝ) / (rN μ n u : ℝ)) atTop (𝓝 (μ 0).toReal) := by
      have hh := (rN_ratio hm u).inv₀ (one_div_pos.mpr hm).ne'
      simpa only [inv_div, div_one] using hh
    have hraw : Tendsto (fun n : ℕ => |(n : ℝ) / (rN μ n u : ℝ) - (μ 0).toReal| / max 1 (u ^ 2)) atTop (𝓝 0) := by
      simpa using ((hr.sub_const (μ 0).toReal).abs.div_const (max 1 (u ^ 2)))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hraw
    · exact (eventually_ge_atTop 1).mono fun n hn => (hb n hn u).1
    · exact Eventually.of_forall fun n => by
        unfold timeError
        by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
        · rw [Set.indicator_of_mem hu]
        · rw [Set.indicator_of_notMem hu]; positivity
  have hdct := tendsto_integral_filter_of_dominated_convergence (fun u : ℝ => 2 / max 1 (u ^ 2))
    (Eventually.of_forall fun n => (hmeas n).aestronglyMeasurable)
    ((eventually_ge_atTop 1).mono fun n hn => Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb n hn u).1]; exact (hb n hn u).2)
    hdom (Eventually.of_forall ht)
  exact ⟨by simpa only [integral_zero] using hdct, fun n hn => ⟨hi n hn, fun u => (hb n hn u).1⟩⟩

theorem eq_cvdd {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |((j : ℝ) / norming (etaLaw μ) θ n) * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
            (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u (j : ℤ)) -
        ((j : ℝ) / norming (etaLaw μ) θ n) * (μ 0).toReal *
          ∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u (j : ℤ)| ≤ ε' := by
  obtain ⟨Ca, Na, ha⟩ := aN_majorant (hc.apply_zero_ne_zero hne) (NormRatios.mu0_ne_one hc hne) hε0 hε1
  obtain ⟨Cb, Nb, hb⟩ := bN_bounded hc hne hap hDA hnl hε0 hε1
  obtain ⟨R, hR⟩ := step_bp_ratio hc hne hap hDA hnl
  obtain ⟨ht, hi⟩ := timeError_integral hc hne hap hDA hnl hε0 hε1
  let A : ℝ := α * (|R| + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let C : ℝ := |Ca| * |Cb|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun n : ℕ => A * C * ∫ u, timeError μ ε n u) atTop (𝓝 0) := by simpa using ht.const_mul (A * C)
  have hratio : ∀ᶠ n : ℕ in atTop, normB μ θ n / norming (etaLaw μ) θ n ≤ |R| + 1 := by
    filter_upwards [hR.eventually (Metric.ball_mem_nhds R zero_lt_one)] with n hn
    rw [Real.dist_eq] at hn
    rw [normB_natCast]
    linarith [le_abs_self (norming (stepLaw μ) θ n / norming (etaLaw μ) θ n - R), le_abs_self R]
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hlim.eventually (eventually_lt_nhds hε')).and
    (hratio.and (normBp_eventually_pos hc hne hap hDA hnl)))
  refine ⟨max 1 (max N (max Na Nb)), fun n hn j hj hju => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnN : N ≤ n := by omega
  have hnNa : Na ≤ n := by omega
  have hnNb : Nb ≤ n := by omega
  obtain ⟨hsmall, hrat, hpos⟩ := hN n hnN
  have hj0 : 0 ≤ (j : ℝ) / norming (etaLaw μ) θ n := by positivity
  have hjA : (j : ℝ) / norming (etaLaw μ) θ n ≤ A := by
    calc
      _ ≤ α * normB μ θ n / norming (etaLaw μ) θ n := div_le_div_of_nonneg_right hju hpos.le
      _ = α * (normB μ θ n / norming (etaLaw μ) θ n) := by ring
      _ ≤ A := mul_le_mul_of_nonneg_left hrat hα.le
  let P : ℝ → ℝ := fun u => aWindow μ ε n u * bN μ θ n u j
  let D : ℝ → ℝ := fun u => ((n : ℝ) / (rN μ n u : ℝ) - (μ 0).toReal) * P u
  have hPmeas : Measurable P := by
    simpa only [P, aWindow, Pi.mul_def] using
      ((aN_measurable μ n).indicator (s := Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)) measurableSet_Icc).mul (bN_measurable μ θ n j)
  have hDmeas : Measurable D := by
    have hr : Measurable (fun u : ℝ => (rN μ n u : ℝ)) :=
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (Nat.measurable_floor.comp (measurable_const.add (measurable_id.mul_const _)))
    simpa only [D, Pi.mul_def, Pi.sub_def, Pi.div_def] using
      ((measurable_const.div hr).sub measurable_const).mul hPmeas
  have hPb u : |P u| ≤ C / max 1 (u ^ 2) := by
    by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
    · have hau := ha n hnNa u (abs_le.mpr hu)
      have hbu := hb n hnNb u (abs_le.mpr hu) j
      dsimp only [P]
      rw [aWindow, Set.indicator_of_mem hu, abs_mul, abs_of_nonneg (aN_nonneg μ n u)]
      calc
        _ ≤ (|Ca| / max 1 (u ^ 2)) * |Cb| := mul_le_mul
          (hau.trans (div_le_div_of_nonneg_right (le_abs_self Ca) (by positivity)))
          (hbu.trans (le_abs_self Cb)) (abs_nonneg _) (by positivity)
        _ = _ := by dsimp [C]; ring
    · simp only [P, aWindow, Set.indicator_of_notMem hu, zero_mul, abs_zero]
      positivity
  have hDb u : |D u| ≤ C * timeError μ ε n u := by
    by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
    · dsimp only [D]
      rw [abs_mul, timeError, Set.indicator_of_mem hu]
      calc
        _ ≤ |(n : ℝ) / (rN μ n u : ℝ) - (μ 0).toReal| * (C / max 1 (u ^ 2)) := mul_le_mul_of_nonneg_left (hPb u) (abs_nonneg _)
        _ = _ := by ring
    · simp only [D, P, aWindow, timeError, Set.indicator_of_notMem hu, zero_mul, mul_zero, abs_zero]
      rfl
  have hPi : Integrable P := by
    apply (window_weight_integrable.const_mul C).mono' hPmeas.aestronglyMeasurable
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      simpa only [one_div, one_mul, div_eq_mul_inv] using hPb u
  have hDi : Integrable D := ((hi n hn1).1.const_mul C).mono' hDmeas.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hDb u)
  have hTPi : Integrable (fun u => (n : ℝ) / (rN μ n u : ℝ) * P u) := by
    convert hDi.add (hPi.const_mul (μ 0).toReal) using 1
    ext u
    dsimp [D]
    ring
  have hI (f : ℝ → ℝ) : (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), f u * aN μ n u * bN μ θ n u j) = ∫ u, f u * P u := by
    rw [intervalIntegral.integral_of_le (by nlinarith [mul_nonneg hε0.le (Real.sqrt_nonneg (n : ℝ))]),
      ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
      · simp only [P, aWindow, Set.indicator_of_mem hu, mul_assoc]
      · simp only [P, aWindow, Set.indicator_of_notMem hu, zero_mul, mul_zero]
  have hIP : (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u j) = ∫ u, P u := by
    simpa only [one_mul] using hI (fun _ => 1)
  rw [hI, hIP]
  have heq : (∫ u, (n : ℝ) / (rN μ n u : ℝ) * P u) - (μ 0).toReal * ∫ u, P u = ∫ u, D u := by
    rw [← integral_const_mul, ← integral_sub hTPi (hPi.const_mul (μ 0).toReal)]
    congr 1
    ext u
    dsimp [D]
    ring
  rw [mul_assoc, ← mul_sub, heq, abs_mul, abs_of_nonneg hj0]
  have hDint : |∫ u, D u| ≤ C * ∫ u, timeError μ ε n u := by
    rw [← integral_const_mul]
    exact (abs_integral_le_integral_abs (f := D)).trans
      (integral_mono hDi.abs ((hi n hn1).1.const_mul C) hDb)
  calc
    _ ≤ A * (C * ∫ u, timeError μ ε n u) :=
      mul_le_mul hjA hDint (abs_nonneg _) hA
    _ ≤ ε' := by rw [← mul_assoc]; exact hsmall.le

end Htheta

private theorem linear_window_deviation {m ε : ℝ} (hm : 0 < m) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ p : ℕ, ε * n < |(p : ℝ) - n / m| →
      (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / m| := by
  have hpow := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  have hlarge : Tendsto (fun n : ℕ => 2 * (n : ℝ) / m) atTop atTop :=
    (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2)).atTop_div_const hm
  have hbig := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hlarge
  filter_upwards [eventually_ge_atTop 1,
    hpow.eventually (eventually_lt_nhds (div_pos hε (Real.rpow_pos_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hm) _))),
    hbig.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2))] with n hn hs hb
  intro p hp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : 0 < 2 * (n : ℝ) / m := by positivity
  have hnpow : (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
    rw [show (3 / 4 : ℝ) = 1 + -(1 / 4 : ℝ) by norm_num, Real.rpow_add hnR, Real.rpow_one]
  by_cases hple : (p : ℝ) ≤ 2 * n / m
  · calc
      (p : ℝ) ^ (3 / 4 : ℝ) ≤ (2 * n / m) ^ (3 / 4 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg p) hple (by norm_num)
      _ = (2 / m) ^ (3 / 4 : ℝ) * ((n : ℝ) * (n : ℝ) ^ (-(1 / 4 : ℝ))) := by
        rw [show 2 * (n : ℝ) / m = (2 / m) * n by ring,
          Real.mul_rpow (by positivity) hnR.le, hnpow]
      _ < ε * n := by
        have hh := (lt_div_iff₀ (Real.rpow_pos_of_pos (div_pos (by norm_num : (0 : ℝ) < 2) hm) (3 / 4 : ℝ))).mp hs
        dsimp only [Function.comp_apply] at hh
        have hh' := mul_lt_mul_of_pos_right hh hnR
        nlinarith only [hh']
      _ < |(p : ℝ) - n / m| := hp
  · have hpg : 2 * (n : ℝ) / m < p := lt_of_not_ge hple
    have hpR : (0 : ℝ) < p := hbase.trans hpg
    have hppow : (p : ℝ) ^ (3 / 4 : ℝ) = (p : ℝ) * (p : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [show (3 / 4 : ℝ) = 1 + -(1 / 4 : ℝ) by norm_num, Real.rpow_add hpR, Real.rpow_one]
    have hsmall : (p : ℝ) ^ (-(1 / 4 : ℝ)) < 1 / 2 :=
      (Real.rpow_le_rpow_of_nonpos hbase hpg.le (by norm_num)).trans_lt hb
    rw [hppow]
    have hh : (p : ℝ) / 2 < (p : ℝ) - n / m := by
      rw [mul_div_assoc] at hpg
      linarith
    exact (by nlinarith : (p : ℝ) * (p : ℝ) ^ (-(1 / 4 : ℝ)) < p / 2).trans
      (hh.trans_le (le_abs_self _))

private theorem measurable_leaf_subset {j n : ℕ} {E : Set (Fin j → BGW.LocallyFinite.Tree)}
    (h : E ⊆ forestLeafCountEvent j n) : MeasurableSet E := by
  apply Set.Countable.measurableSet
  apply (Set.countable_range (fun ts : Fin j → BGW.PlaneTree => fun i => (ts i).toLocallyFinite)).mono
  intro F hF
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (h hF)
  obtain ⟨ts, -, -, hts⟩ := hp
  exact ⟨ts, hts.symm⟩

theorem eq_psi {μ : PMF ℕ} (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) {ε : ℝ} (hε : 0 < ε) :
    IsOeUniform (1 / 2) fun j n : ℕ =>
      |(n : ℝ) * (psi μ n j).toReal - (n : ℝ) * (forestLaw μ j).real (forestLeafWindowEvent j n
          ((n : ℝ) / (μ 0).toReal - ε * n) ((n : ℝ) / (μ 0).toReal + ε * n))| := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos h0 (μ.apply_ne_top 0)
  let x : ℕ → ℕ → ℝ := fun j n => |(psi μ n j).toReal - (forestLaw μ j).real
    (forestLeafWindowEvent j n ((n : ℝ) / (μ 0).toReal - ε * n) ((n : ℝ) / (μ 0).toReal + ε * n))|
  have hsub j n : forestLeafWindowEvent j n ((n : ℝ) / (μ 0).toReal - ε * n) ((n : ℝ) / (μ 0).toReal + ε * n) ⊆
      forestLeafCountEvent j n := by rintro F ⟨p, hp, -, -⟩; exact Set.mem_iUnion.mpr ⟨p, hp⟩
  have heq j n : x j n = (forestLaw μ j).real (forestLeafCountEvent j n \
      forestLeafWindowEvent j n ((n : ℝ) / (μ 0).toReal - ε * n) ((n : ℝ) / (μ 0).toReal + ε * n)) := by
    rw [measureReal_sdiff (hsub j n) (measurable_leaf_subset (hsub j n))]
    change |(forestLaw μ j).real (forestLeafCountEvent j n) - _| = _
    exact abs_of_nonneg (sub_nonneg.mpr (measureReal_mono (hsub j n)))
  have hx j n : x j n ≤ 1 := by rw [heq]; exact measureReal_le_one
  obtain ⟨C, c, hC, hc, hb⟩ := lem_GdesDev2_ii μ h0 h1
  obtain ⟨N, hN⟩ := eventually_atTop.mp (linear_window_deviation hm hε)
  have hb' : ∀ n j : ℕ, N ≤ n → 1 ≤ j → j ≤ n → x j n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
    intro n j hn hj hjn
    rw [heq]
    apply (measureReal_mono (μ := forestLaw μ j) (s₂ := {F | ∃ p : ℕ, F ∈ forestEvent j p n ∧
      (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / (μ 0).toReal|}) ?_).trans (hb n j hj hjn)
    rintro F ⟨hF, hnot⟩
    obtain ⟨p, hp⟩ := Set.mem_iUnion.mp hF
    refine ⟨p, hp, hN n hn p ?_⟩
    by_contra hd
    have hh := abs_le.mp (le_of_not_gt hd)
    apply hnot
    exact ⟨p, hp, by linarith [hh.1], by linarith [hh.2]⟩
  let D : ℝ := C + Real.exp (c * (N : ℝ) ^ (1 / 2 : ℝ))
  have hD : 0 < D := by dsimp [D]; positivity
  have hbound n j (hj : 1 ≤ j) (hjn : j ≤ n) : x j n ≤ D * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
    by_cases hn : N ≤ n
    · exact (hb' n j hn hj hjn).trans (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith [Real.exp_pos (c * (N : ℝ) ^ (1 / 2 : ℝ))]) (Real.exp_pos _).le)
    · have hpow : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show n ≤ N by omega)) (by norm_num)
      have he : 1 ≤ Real.exp (c * (N : ℝ) ^ (1 / 2 : ℝ)) * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
        rw [← Real.exp_add, Real.one_le_exp_iff]
        nlinarith
      exact (hx j n).trans (he.trans (mul_le_mul_of_nonneg_right (by dsimp [D]; linarith) (Real.exp_pos _).le))
  obtain ⟨C', hC', hab⟩ := LeafConcentration.OeLemmas.polyExp_absorb (by norm_num : (0 : ℝ) < 1 / 2)
    1 (half_pos hc) (half_lt_self hc)
  refine ⟨D * C', c / 2, mul_pos hD hC', half_pos hc, fun n j hj hjn => ?_⟩
  dsimp only
  rw [← mul_sub, abs_mul, abs_of_nonneg (Nat.cast_nonneg n)]
  change (n : ℝ) * x j n ≤ _
  calc
    _ ≤ (n : ℝ) * (D * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (hbound n j hj hjn) (Nat.cast_nonneg n)
    _ = D * ((n : ℝ) ^ (1 : ℝ) * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
    _ ≤ D * (C' * Real.exp (-(c / 2) * (n : ℝ) ^ (1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (hab n) hD.le
    _ = _ := by ring



private theorem eta_probability_general {μ : PMF ℕ} (h1 : μ 0 ≠ 1) :
    IsProbabilityMeasure (eta μ.toMeasure) := by
  have hcond : μ.toMeasure (Set.Ici 1) ≠ 0 := by
    intro hz
    apply h1
    have he : Set.Ici (1 : ℕ) = {0}ᶜ := by ext k; simp; omega
    rw [he, measure_compl (measurableSet_singleton 0) (measure_ne_top _ _), measure_univ,
      PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] at hz
    exact le_antisymm (PMF.coe_le_one μ 0) (tsub_eq_zero_iff_le.mp hz)
  let : IsProbabilityMeasure (μ.toMeasure[|Set.Ici 1]) := cond_isProbabilityMeasure hcond
  unfold eta
  exact (Measure.isProbabilityMeasure_map_iff (measurable_id.sub_const 1).aemeasurable).2 inferInstance

private theorem pi_eta_walk_general {μ : PMF ℕ} (h1 : μ 0 ≠ 1) (k n j : ℕ) :
    (Measure.pi (fun _ : Fin k => eta μ.toMeasure)).real {ω | ∑ i, ω i + j = n} =
      intWalkProb (etaLaw μ) k ((n : ℤ) - j) := by
  let := eta_probability_general h1
  let : IsProbabilityMeasure (etaLaw μ) := by
    rw [← LeafMass.Arithmetic.eta_map_cast_eq_etaLaw]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2 inferInstance
  rw [intWalkProb, LeafMass.Arithmetic.intWalk_eq_map_sum,
    ← LeafMass.Arithmetic.eta_map_cast_eq_etaLaw, measureReal_def, measureReal_def,
    ← Measure.pi_map_pi (μ := fun _ : Fin k => eta μ.toMeasure)
      (f := fun _ : Fin k => fun k : ℕ => (k : ℤ))
      (fun _ => (measurable_of_countable _).aemeasurable),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  congr 2
  ext ω
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    have hh : ((∑ i, ω i : ℕ) : ℤ) + j = n := by exact_mod_cast h
    push_cast at hh
    omega
  · intro h
    have hh : ((∑ i, ω i : ℕ) : ℤ) + j = n := by push_cast; omega
    exact_mod_cast hh

private theorem forest_joint_real {μ : PMF ℕ} (h1 : μ 0 ≠ 1)
    {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j) (p : ℕ) :
    (forestLaw μ j).real (forestEvent j p n) =
      (j : ℝ) / p * binomProb (μ 0).toReal p n *
        intWalkProb (etaLaw μ) (p - n) ((n : ℤ) - j) := by
  by_cases hnp : n ≤ p
  · have hμ0 : μ.toMeasure {0} ≠ 1 := by simpa only [PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] using h1
    rw [measureReal_def, forestLaw, prop_K μ.toMeasure hμ0 hj (by omega) hnp,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_div,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_pow, ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_one]
    rw [← measureReal_def, pi_eta_walk_general h1]
    rfl
  · have he : forestEvent j p n = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro F ⟨ts, hp, hleaf, -⟩
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (ts i).degreeCount_le_size 0)
      rw [hp, hleaf] at hh
      exact hnp hh
    rw [he, measureReal_empty, binomProb, Nat.choose_eq_zero_of_lt (by omega)]
    simp

private theorem floor_cell (p : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (p : ℝ) (p + 1)) : ⌊x⌋₊ = p := by
  exact (Nat.floor_eq_iff ((Nat.cast_nonneg p).trans hx.1.le)).mpr ⟨hx.1.le, hx.2⟩

private theorem floor_step_integrable (f : ℕ → ℝ) (p : ℕ) :
    IntervalIntegrable (fun x : ℝ => f ⌊x⌋₊) volume p (p + 1) := by
  apply (intervalIntegrable_congr_uIoo (g := fun _ => f p) ?_).mpr intervalIntegrable_const
  rw [Set.uIoo_of_le (by linarith : (p : ℝ) ≤ p + 1)]
  intro x hx
  change f ⌊x⌋₊ = f p
  rw [floor_cell p hx]

private theorem floor_step_integral (f : ℕ → ℝ) (p : ℕ) :
    (∫ x in (p : ℝ)..(p + 1), f ⌊x⌋₊) = f p := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (g := fun _ => f p)
    (by linarith : (p : ℝ) ≤ p + 1) (fun x hx => by rw [floor_cell p hx])]
  simp

private theorem floor_quad_nat (f : ℕ → ℝ) {l r : ℕ} (hlr : l ≤ r + 1) :
    (∫ x in (l : ℝ)..(r + 1), f ⌊x⌋₊) = ∑ p ∈ Finset.Icc l r, f p := by
  have hh := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun p : ℕ => (p : ℝ)) (m := l) (n := r + 1) (f := fun x : ℝ => f ⌊x⌋₊) hlr
    (fun p _ => by simpa only [Nat.cast_add, Nat.cast_one] using floor_step_integrable f p)
  simp only [Nat.cast_add, Nat.cast_one] at hh
  rw [← hh]
  simp only [floor_step_integral]
  rw [Finset.Ico_add_one_right_eq_Icc]


private theorem floor_quad (f : ℕ → ℝ) (hf : f 0 = 0) {a b : ℝ} (hab : a ≤ b) (hb : 0 ≤ b) :
    (∫ x in (⌈a⌉ : ℤ)..((⌊b⌋ : ℤ) + 1 : ℝ), f ⌊x⌋₊) =
      ∑ p ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, f p := by
  have hlr : ⌈a⌉₊ ≤ ⌊b⌋₊ + 1 := (Nat.ceil_mono hab).trans (Nat.ceil_le_floor_add_one b)
  rw [← natCast_floor_eq_intCast_floor hb]
  by_cases ha : 0 ≤ a
  · rw [← natCast_ceil_eq_intCast_ceil ha]
    exact floor_quad_nat f hlr
  · have hca : ⌈a⌉₊ = 0 := Nat.ceil_eq_zero.mpr (le_of_not_ge ha)
    have hica : (⌈a⌉ : ℤ) ≤ 0 := Int.ceil_nonpos.mpr (le_of_not_ge ha)
    have hreal : ((⌈a⌉ : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hica
    have hneg : IntervalIntegrable (fun x : ℝ => f ⌊x⌋₊) volume (⌈a⌉ : ℤ) 0 := by
      apply (intervalIntegrable_congr_uIoo (g := fun _ => (0 : ℝ)) ?_).mpr intervalIntegrable_const
      rw [Set.uIoo_of_le hreal]
      intro x hx
      change f ⌊x⌋₊ = 0
      rw [Nat.floor_of_nonpos hx.2.le, hf]
    have hpos : IntervalIntegrable (fun x : ℝ => f ⌊x⌋₊) volume 0 (⌊b⌋₊ + 1) := by
      have hh := IntervalIntegrable.trans_iterate_Ico (a := fun k : ℕ => (k : ℝ))
        (f := fun x : ℝ => f ⌊x⌋₊) (μ := volume) (Nat.zero_le (⌊b⌋₊ + 1))
        (fun k _ => by simpa only [Nat.cast_add, Nat.cast_one] using floor_step_integrable f k)
      simpa only [Nat.cast_zero, Nat.cast_add, Nat.cast_one] using hh
    rw [← intervalIntegral.integral_add_adjacent_intervals hneg hpos]
    have hz : (∫ x in (⌈a⌉ : ℤ)..(0 : ℝ), f ⌊x⌋₊) = 0 := by
      rw [intervalIntegral.integral_congr_Ioo_of_le (g := fun _ => (0 : ℝ)) hreal
        (fun x hx => by dsimp; rw [Nat.floor_of_nonpos hx.2.le, hf])]
      simp
    rw [hz, zero_add, hca]
    simpa only [Nat.cast_zero] using floor_quad_nat f (l := 0) (r := ⌊b⌋₊) (Nat.zero_le _)

private theorem forest_joint_measurable (j p n : ℕ) : MeasurableSet (forestEvent j p n) := by
  apply Set.Countable.measurableSet
  apply (Set.countable_range (fun ts : Fin j → BGW.PlaneTree => fun i => (ts i).toLocallyFinite)).mono
  rintro F ⟨ts, -, -, hts⟩
  exact ⟨ts, hts.symm⟩

private theorem forest_joint_disjoint (j n : ℕ) : Pairwise (Function.onFun Disjoint (fun p => forestEvent j p n)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  rintro F ⟨ts, hp, -, hts⟩ ⟨us, hq, -, hus⟩
  have he : ts = us := by
    funext i
    exact BGW.PlaneTree.toLocallyFinite_injective (congrFun (hts.symm.trans hus) i)
  subst us
  exact hpq (hp.symm.trans hq)

private theorem forest_window_sum (μ : PMF ℕ) (j n : ℕ) {a b : ℝ} (hb : 0 ≤ b) :
    (forestLaw μ j).real (forestLeafWindowEvent j n a b) =
      ∑ p ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, (forestLaw μ j).real (forestEvent j p n) := by
  have he : forestLeafWindowEvent j n a b = ⋃ p ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, forestEvent j p n := by
    ext F
    simp only [forestLeafWindowEvent, Set.mem_ofPred_eq, Set.mem_iUnion, Finset.mem_Icc]
    constructor
    · rintro ⟨p, hp, ha, hb'⟩
      exact ⟨p, ⟨Nat.ceil_le.mpr ha, Nat.le_floor hb'⟩, hp⟩
    · rintro ⟨p, ⟨ha, hb'⟩, hp⟩
      exact ⟨p, hp, (Nat.le_ceil a).trans (by exact_mod_cast ha),
        (by exact_mod_cast hb' : (p : ℝ) ≤ (⌊b⌋₊ : ℝ)) |>.trans (Nat.floor_le hb)⟩
  rw [he]
  apply measureReal_biUnion_finset
  · intro p _ q _ hpq
    exact forest_joint_disjoint j n hpq
  · intro p _
    exact forest_joint_measurable j p n
  · intro p _
    exact measure_ne_top _ _

theorem eq_retenir {μ : PMF ℕ} (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1)
    {θ ε : ℝ} (hε : 0 < ε) {n j : ℕ} (hn : 1 ≤ n) (hj : 1 ≤ j)
    (hB : 0 < norming (etaLaw μ) θ n) :
    (n : ℝ) * (forestLaw μ j).real (forestLeafWindowEvent j n
        ((n : ℝ) / (μ 0).toReal - ε * n) ((n : ℝ) / (μ 0).toReal + ε * n)) =
      ((j : ℝ) / norming (etaLaw μ) θ n) *
        ∫ u in ((⌈(n : ℝ) / (μ 0).toReal - ε * n⌉ - (n : ℝ) / (μ 0).toReal) / Real.sqrt n)..
            ((⌊(n : ℝ) / (μ 0).toReal + ε * n⌋ + 1 - (n : ℝ) / (μ 0).toReal) / Real.sqrt n),
          (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u j := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos h0 (μ.apply_ne_top 0)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  let a : ℝ := (n : ℝ) / (μ 0).toReal - ε * n
  let b : ℝ := (n : ℝ) / (μ 0).toReal + ε * n
  let f : ℕ → ℝ := fun p => (forestLaw μ j).real (forestEvent j p n)
  have hab : a ≤ b := by dsimp [a, b]; nlinarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hf : f 0 = 0 := by dsimp only [f]; rw [forest_joint_real h1 hn hj]; simp
  have hquad := floor_quad f hf hab hb
  have haff := intervalIntegral.integral_comp_add_mul (fun x : ℝ => f ⌊x⌋₊) hs.ne' ((n : ℝ) / (μ 0).toReal)
    (a := (((⌈a⌉ : ℤ) : ℝ) - (n : ℝ) / (μ 0).toReal) / Real.sqrt n)
    (b := (((⌊b⌋ : ℤ) : ℝ) + 1 - (n : ℝ) / (μ 0).toReal) / Real.sqrt n)
  have hleft : (n : ℝ) / (μ 0).toReal + Real.sqrt n *
      ((((⌈a⌉ : ℤ) : ℝ) - (n : ℝ) / (μ 0).toReal) / Real.sqrt n) = (⌈a⌉ : ℤ) := by field_simp; ring
  have hright : (n : ℝ) / (μ 0).toReal + Real.sqrt n *
      ((((⌊b⌋ : ℤ) : ℝ) + 1 - (n : ℝ) / (μ 0).toReal) / Real.sqrt n) = (⌊b⌋ : ℤ) + 1 := by field_simp; ring
  rw [hleft, hright, smul_eq_mul, hquad] at haff
  rw [forest_window_sum μ j n hb]
  change (n : ℝ) * ∑ p ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, f p = _
  rw [← intervalIntegral.integral_const_mul]
  have heq (u : ℝ) : ((j : ℝ) / norming (etaLaw μ) θ n) *
      ((n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u j) =
      (n : ℝ) * Real.sqrt n * f ⌊(n : ℝ) / (μ 0).toReal + Real.sqrt n * u⌋₊ := by
    dsimp only [f]
    rw [forest_joint_real h1 hn hj]
    have hr : ⌊(n : ℝ) / (μ 0).toReal + Real.sqrt n * u⌋₊ = rN μ n u := by
      unfold rN
      rw [mul_comm (Real.sqrt n) u]
    simp only [hr]
    unfold aN bN
    field_simp [hB.ne']
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, haff]
  field_simp



section HthetaFinal
variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b) (hnl : ¬ IsLatticeLaw (etaLaw μ))
include hc hne hap hDA hnl

private theorem weighted_window_limit {α ε : ℝ} (hα : 0 < α) (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |((j : ℝ) / norming (etaLaw μ) θ n) *
        (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
          (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u j) -
        qKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ η := by
  obtain ⟨R, hR⟩ := step_bp_ratio hc hne hap hDA hnl
  let A : ℝ := α * (|R| + 1)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨M, hM, hMb⟩ := Scalar.exists_stableDensity_le (α := θ)
  obtain ⟨r, hrat, hmain⟩ : ∃ r : ℝ,
      Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 r) ∧
      (∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
        |(μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u j) -
          r * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ η / (3 * (A + 1))) := by
    by_cases hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)
    · exact ⟨_, NormRatios.normBp_div_normB_finVar hc hne hap hDA hfin,
        eq_lemtechnique0_finVar_corrected hc hne hap hDA hnl hfin hα hε0 hε1 (by positivity)⟩
    · exact ⟨_, NormRatios.normBp_div_normB_infVar hc hne hap hDA hfin,
        eq_lemtechnique0_infVar hc hne hap hDA hnl hfin hα hε0 hε1 (by positivity)⟩
  obtain ⟨Nm, hm⟩ := hmain
  obtain ⟨Nc, hcv⟩ := eq_cvdd hc hne hap hDA hnl hα hε0 hε1 (by positivity : 0 < η / 3)
  have hsmall : Tendsto (fun n : ℕ => A * M *
      |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)|) atTop (𝓝 0) := by
    simpa using (((tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).sub hrat).abs.const_mul (A * M))
  have hratio : ∀ᶠ n : ℕ in atTop, normB μ θ n / norming (etaLaw μ) θ n ≤ |R| + 1 := by
    filter_upwards [hR.eventually (Metric.ball_mem_nhds R zero_lt_one)] with n hn
    rw [Real.dist_eq] at hn
    rw [normB_natCast]
    linarith [le_abs_self (norming (stepLaw μ) θ n / norming (etaLaw μ) θ n - R), le_abs_self R]
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hsmall.eventually (eventually_lt_nhds (by positivity : 0 < η / 3))).and
    (hratio.and (normBp_eventually_pos hc hne hap hDA hnl)))
  refine ⟨max N (max Nm Nc), fun n hn j hj hju => ?_⟩
  have hnN : N ≤ n := by omega
  have hnm : Nm ≤ n := by omega
  have hnc : Nc ≤ n := by omega
  obtain ⟨hs, hnb, hpos⟩ := hN n hnN
  let x : ℝ := (j : ℝ) / norming (etaLaw μ) θ n
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hxA : x ≤ A := by
    calc
      _ ≤ α * normB μ θ n / norming (etaLaw μ) θ n := div_le_div_of_nonneg_right hju hpos.le
      _ = α * (normB μ θ n / norming (etaLaw μ) θ n) := by ring
      _ ≤ A := mul_le_mul_of_nonneg_left hnb hα.le
  let d : ℝ := Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))
  have hq : |x * (r * d) - qKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ η / 3 := by
    have heq : x * (r * d) - qKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)) =
        x * (r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) * d := by
      rw [qKernel_one]
      dsimp [x, d]
      field_simp [hpos.ne']
    rw [heq, abs_mul, abs_mul, abs_of_nonneg hx]
    calc
      _ ≤ (A * |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)|) * M :=
        mul_le_mul (mul_le_mul_of_nonneg_right hxA (abs_nonneg _)) (hMb _) (abs_nonneg _) (by positivity)
      _ = A * M * |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)| := by ring
      _ ≤ η / 3 := hs.le
  have hm' : |x * ((μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u j)) -
      x * (r * d)| ≤ η / 3 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hx]
    calc
      _ ≤ A * (η / (3 * (A + 1))) := mul_le_mul hxA (hm n hnm j hj hju) (abs_nonneg _) hA
      _ ≤ η / 3 := by
        have hh : 0 < A + 1 := by positivity
        apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 3)).mpr
        field_simp
        nlinarith
  have hh := abs_sub_le
    (x * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u j))
    (x * ((μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u j)))
    (qKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))
  have hh' := abs_sub_le
    (x * ((μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u j)))
    (x * (r * d)) (qKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))
  have hcv' := hcv n hnc j hj hju
  rw [mul_assoc] at hcv'
  change |_ - _| ≤ η
  linarith

private theorem normB_range_small {α : ℝ} (_hα : 0 < α) :
    ∀ᶠ n : ℕ in atTop, α * normB μ θ n ≤ n := by
  obtain ⟨b, hb⟩ := hDA
  have hDA' : ∃ b, IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b :=
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA'
  have hmono := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA').1
  rw [mean_stepLaw hc] at ha
  obtain ⟨a, heq, h⟩ := ha.exists_stableDomain hc hne hmono
  have ht := (Scalar.regularlyVaryingSeq h).tendsto_div_self h.monotone h.pos
    (by have := h.alpha_mem.1; positivity : 0 ≤ 1 / θ) ((div_lt_one (by linarith [h.alpha_mem.1] : 0 < θ)).mpr h.alpha_mem.1)
  have ht' : Tendsto (fun n : ℕ => α * (a n / n)) atTop (𝓝 0) := by simpa using ht.const_mul α
  filter_upwards [ht'.eventually (eventually_lt_nhds zero_lt_one), heq, eventually_ge_atTop 1] with n hn he hn1
  rw [normB_natCast, ← he]
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [← mul_div_assoc, div_lt_one hnR] at hn
  exact hn.le

private theorem time_kernel_interval {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ,
      IntervalIntegrable (fun u => (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u j)
        volume (-(ε * Real.sqrt n)) (ε * Real.sqrt n) := by
  obtain ⟨Ca, Na, ha⟩ := aN_majorant (hc.apply_zero_ne_zero hne) (NormRatios.mu0_ne_one hc hne) hε0 hε1
  obtain ⟨Cb, Nb, hb⟩ := bN_bounded hc hne hap hDA hnl hε0 hε1
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  refine ⟨max 1 (max Na Nb), fun n hn j => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnNa : Na ≤ n := by omega
  have hnNb : Nb ≤ n := by omega
  have hmeas : Measurable (fun u => (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u j) := by
    have hr : Measurable (fun u : ℝ => (rN μ n u : ℝ)) :=
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
        (Nat.measurable_floor.comp (measurable_const.add (measurable_id.mul_const _)))
    simpa only [Pi.mul_def, Pi.div_def] using ((measurable_const.div hr).mul (aN_measurable μ n)).mul (bN_measurable μ θ n j)
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by nlinarith [mul_nonneg hε0.le (Real.sqrt_nonneg (n : ℝ))])).mpr
  apply Measure.integrableOn_of_bounded (by simp) hmeas.aestronglyMeasurable (M := |Ca| * |Cb|)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  have huu := abs_le.mpr hu
  have hnr := (rN_window_bounds hm hm1 hε0 hε1 hn1 huu).1
  have hrpos : (0 : ℝ) < rN μ n u := by exact_mod_cast (show 0 < rN μ n u by omega)
  have hfrac : (n : ℝ) / (rN μ n u : ℝ) ≤ 1 := (div_le_one hrpos).mpr (by exact_mod_cast hnr)
  have hannon : 0 ≤ aN μ n u := aN_nonneg μ n u
  have han : aN μ n u ≤ |Ca| := by
    calc _ ≤ Ca / max 1 (u ^ 2) := ha n hnNa u huu
      _ ≤ |Ca| / max 1 (u ^ 2) := div_le_div_of_nonneg_right (le_abs_self Ca) (by positivity)
      _ ≤ |Ca| := div_le_self (abs_nonneg _) (le_max_left _ _)
  have hbn : |bN μ θ n u j| ≤ |Cb| := (hb n hnNb u huu j).trans (le_abs_self Cb)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) / (rN μ n u : ℝ)), abs_of_nonneg hannon]
  calc _ ≤ (1 * |Ca|) * |Cb| := mul_le_mul (mul_le_mul hfrac han hannon (by norm_num)) hbn (abs_nonneg _) (by positivity)
    _ = _ := by ring

theorem lem_technical_ii {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(n : ℝ) * (psi μ n j).toReal - qKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  let δ : ℝ := (1 - (μ 0).toReal) / (8 * (μ 0).toReal)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδwide : 2 * δ < (1 - (μ 0).toReal) / (2 * (μ 0).toReal) := by dsimp [δ]; field_simp; nlinarith
  have hδsmall : δ / 2 < (1 - (μ 0).toReal) / (2 * (μ 0).toReal) := by linarith
  obtain ⟨Ns, hs⟩ := weighted_window_limit hc hne hap hDA hnl hα (half_pos hδ) hδsmall (half_pos hε)
  obtain ⟨Nw, hw⟩ := weighted_window_limit hc hne hap hDA hnl hα (by positivity : 0 < 2 * δ) hδwide (half_pos hε)
  obtain ⟨Ni, hi⟩ := time_kernel_interval hc hne hap hDA hnl (by positivity : 0 < 2 * δ) hδwide
  obtain ⟨C, c, hC, hcp, hb⟩ := eq_psi (hc.apply_zero_ne_zero hne) (NormRatios.mu0_ne_one hc hne) hδ
  have hexp : Tendsto (fun n : ℕ => C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hcp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop))
    simpa only [Function.comp_apply, neg_mul, mul_zero] using hh.const_mul C
  have hgrowth : ∀ᶠ n : ℕ in atTop, 2 ≤ δ * (n : ℝ) :=
    (Filter.Tendsto.const_mul_atTop hδ tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hexp.eventually (eventually_lt_nhds (half_pos hε))).and
    ((normB_range_small hc hne hap hDA hnl hα).and
      ((normBp_eventually_pos hc hne hap hDA hnl).and hgrowth)))
  refine ⟨max 1 (max N (max Ns (max Nw Ni))), fun n hn j hj hju => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnN : N ≤ n := by omega
  have hnNs : Ns ≤ n := by omega
  have hnNw : Nw ≤ n := by omega
  have hnNi : Ni ≤ n := by omega
  obtain ⟨hex, hBn, hBp, hgr⟩ := hN n hnN
  have hjn : j ≤ n := by exact_mod_cast hju.trans hBn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsq := Real.sq_sqrt hnR.le
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  let L : ℝ := (((⌈(n : ℝ) / (μ 0).toReal - δ * n⌉ : ℤ) : ℝ) - (n : ℝ) / (μ 0).toReal) / Real.sqrt n
  let U : ℝ := (((⌊(n : ℝ) / (μ 0).toReal + δ * n⌋ : ℤ) : ℝ) + 1 - (n : ℝ) / (μ 0).toReal) / Real.sqrt n
  have hL0 : -(2 * δ * Real.sqrt n) ≤ L := by
    dsimp [L]
    rw [le_div_iff₀ hsn]
    nlinarith [Int.le_ceil ((n : ℝ) / (μ 0).toReal - δ * n)]
  have hL1 : L ≤ -(δ / 2 * Real.sqrt n) := by
    dsimp [L]
    rw [div_le_iff₀ hsn]
    nlinarith [Int.ceil_lt_add_one ((n : ℝ) / (μ 0).toReal - δ * n)]
  have hU0 : δ / 2 * Real.sqrt n ≤ U := by
    dsimp [U]
    rw [le_div_iff₀ hsn]
    nlinarith [Int.lt_floor_add_one ((n : ℝ) / (μ 0).toReal + δ * n)]
  have hU1 : U ≤ 2 * δ * Real.sqrt n := by
    dsimp [U]
    rw [div_le_iff₀ hsn]
    nlinarith [Int.floor_le ((n : ℝ) / (μ 0).toReal + δ * n)]
  have hLU : L ≤ U := by nlinarith [mul_nonneg hδ.le hsn.le]
  let F : ℝ → ℝ := fun u => (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u j
  have hFn u : 0 ≤ F u := by
    have hb0 : 0 ≤ bN μ θ n u j := mul_nonneg hBp.le measureReal_nonneg
    exact mul_nonneg (mul_nonneg (by positivity) (aN_nonneg μ n u)) hb0
  have hFi := hi n hnNi (j : ℤ)
  have hsmallI := intervalIntegral.integral_mono_interval hL1
    (by nlinarith [mul_nonneg hδ.le hsn.le] : -(δ / 2 * Real.sqrt n) ≤ δ / 2 * Real.sqrt n) hU0
    (Eventually.of_forall hFn)
    (hFi.mono_set (by simp only [Set.uIcc_of_le hLU, Set.uIcc_of_le (show -(2 * δ * Real.sqrt n) ≤ 2 * δ * Real.sqrt n by nlinarith [mul_nonneg hδ.le hsn.le])]; exact Set.Icc_subset_Icc hL0 hU1))
  have hlargeI := intervalIntegral.integral_mono_interval hL0 hLU hU1 (Eventually.of_forall hFn) hFi
  have hx : 0 ≤ (j : ℝ) / norming (etaLaw μ) θ n := by positivity
  have hps := mul_le_mul_of_nonneg_left hsmallI hx
  have hpw := mul_le_mul_of_nonneg_left hlargeI hx
  have hret := eq_retenir (hc.apply_zero_ne_zero hne) (NormRatios.mu0_ne_one hc hne) hδ hn1 hj hBp
  have hb' := hb n j hj hjn
  have hs' := hs n hnNs j hj hju
  have hw' := hw n hnNw j hj hju
  rw [abs_le] at hs' hw' hb' ⊢
  change _ ≤ (j : ℝ) / norming (etaLaw μ) θ n * (∫ u in L..U, F u) at hps
  change (j : ℝ) / norming (etaLaw μ) θ n * (∫ u in L..U, F u) ≤ _ at hpw
  change (n : ℝ) * (forestLaw μ j).real (forestLeafWindowEvent j n _ _) =
    (j : ℝ) / norming (etaLaw μ) θ n * (∫ u in L..U, F u) at hret
  rw [← hret] at hps hpw
  constructor <;> linarith

end HthetaFinal

end BGWLeaves.LocalEstimates.Technique
