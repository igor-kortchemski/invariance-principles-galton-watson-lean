/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Scalar.Normalization
public import BGW.StableTrees.CriticalSupport
public import Mathlib.Probability.CentralLimitTheorem
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite-variance normalization

The finite-variance assertion at source line 864: the normalizing sequence in
`StableDomain` is asymptotic to a positive constant times `√n`.

Adapted from `PoissonDeclumping/Stable/FiniteVariance.lean` in
`igor-kortchemski/rare-subtree-patterns`, commit
`fc5ef722392b1af41e8b9d5fc45d5a521b7823dd` (Apache-2.0).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex Set Asymptotics
open scoped Topology ENNReal

namespace BGW.StableTrees.Scalar

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

lemma offspring_integral_eq_one (hc : IsCritical μ) :
    ∫ j : ℕ, (j : ℝ) ∂μ.toMeasure = 1 := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun j => Nat.cast_nonneg j)
    (measurable_of_countable _).aestronglyMeasurable, lintegral_countable']
  simp only [ENNReal.ofReal_natCast,
    PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
  rw [show ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 1 from hc]
  simp

lemma memLp_step_of_memLp_offspring
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    MemLp (fun z : ℤ => (z : ℝ)) 2 (stepLaw μ) := by
  rw [stepLaw, memLp_map_measure_iff (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable]
  convert hfinite.sub (memLp_const (1 : ℝ)) using 1
  funext j
  simp

lemma step_integral_eq_zero (hc : IsCritical μ)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    ∫ z : ℤ, (z : ℝ) ∂stepLaw μ = 0 := by
  rw [stepLaw, integral_map (measurable_of_countable _).aemeasurable
    (measurable_of_countable _).aestronglyMeasurable]
  simp only [Int.cast_sub, Int.cast_natCast, Int.cast_one]
  rw [integral_sub (hfinite.integrable (by norm_num)) (integrable_const _),
    offspring_integral_eq_one hc]
  simp

lemma step_secondMoment_pos (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    0 < ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ := by
  have hi := (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).1
    (memLp_step_of_memLp_offspring hfinite)
  have hn : 0 ≤ ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ := integral_nonneg fun z => sq_nonneg _
  apply lt_of_le_of_ne hn
  intro hz
  have hz' := (integral_eq_zero_iff_of_nonneg (fun z : ℤ => sq_nonneg (z : ℝ)) hi).1 hz.symm
  have hm := ae_iff.1 hz'
  have hsub : ({-1} : Set ℤ) ⊆ {z : ℤ | ¬(z : ℝ) ^ 2 = 0} := by
    intro z hz
    simp only [mem_singleton_iff] at hz
    subst z
    norm_num
  have heq : stepLaw μ {-1} = 0 := measure_mono_null hsub hm
  rw [stepLaw, Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _)] at heq
  have hp : (fun j : ℕ => (j : ℤ) - 1) ⁻¹' ({-1} : Set ℤ) = {0} := by
    ext j
    simp only [mem_preimage, mem_singleton_iff]
    omega
  rw [hp, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton _)] at heq
  exact hc.apply_zero_ne_zero hne heq

/-- Weak convergence of probability measures also controls characteristic functions at moving
arguments. This is the equicontinuity argument used for the stable normalization. -/
lemma tendsto_charFun_moving {P : ℕ → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hP : Tendsto P atTop (𝓝 Q)) {s : ℕ → ℝ} {t : ℝ}
    (hs : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun n => charFun (P n : Measure ℝ) (s n)) atTop
      (𝓝 (charFun (Q : Measure ℝ) t)) := by
  have hr := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hP)
  have hcf := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hP t
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hδ : ∃ δ : ℝ, 0 < δ ∧ ∫ x, bumpFn δ x ∂(Q : Measure ℝ) < ε / 4 := by
    have h1 := (tendsto_integral_bumpFn (Q : Measure ℝ)).eventually
      (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4))
    have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
        ∫ x, bumpFn δ x ∂(Q : Measure ℝ) < ε / 4 ∧ 0 < δ :=
      (h1.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
    obtain ⟨δ, hδ1, hδ2⟩ := h2.exists
    exact ⟨δ, hδ2, hδ1⟩
  obtain ⟨δ, hδpos, hδν⟩ := hδ
  have e1 : ∀ᶠ j in atTop, |s j - t| ≤ δ := by
    have := (Metric.tendsto_nhds.1 hs) δ hδpos
    filter_upwards [this] with j hj
    rw [Real.dist_eq] at hj
    exact hj.le
  have e2 : ∀ᶠ j in atTop, ∫ x, bumpFn δ x ∂(P j : Measure ℝ) < ε / 2 :=
    (hr (bumpFn δ)).eventually (gt_mem_nhds (by linarith))
  have e3 : ∀ᶠ j in atTop,
      dist (charFun (P j : Measure ℝ) t) (charFun (Q : Measure ℝ) t) < ε / 4 :=
    (Metric.tendsto_nhds.1 hcf) (ε / 4) (by linarith)
  obtain ⟨N, hN⟩ := (e1.and (e2.and e3)).exists_forall_of_atTop
  refine ⟨N, fun j hj => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hN j hj
  calc dist (charFun (P j : Measure ℝ) (s j)) (charFun (Q : Measure ℝ) t)
      ≤ dist (charFun (P j : Measure ℝ) (s j)) (charFun (P j : Measure ℝ) t) +
        dist (charFun (P j : Measure ℝ) t) (charFun (Q : Measure ℝ) t) := dist_triangle _ _ _
    _ < ε / 2 + ε / 4 := by
        gcongr
        rw [dist_eq_norm]
        exact (norm_charFun_sub_le _ h1).trans_lt h2
    _ < ε := by linarith

/-- The law of the `n`-step offspring-minus-one walk divided by `σ * Real.sqrt n`. -/
noncomputable def finiteVarianceLaw (μ : PMF ℕ) (σ : ℝ) (n : ℕ) : ProbabilityMeasure ℝ :=
  ⟨scaledLaw μ (fun n => σ * Real.sqrt n) n, inferInstance⟩

/-- The centered real Gaussian probability measure with variance one. -/
noncomputable def standardGaussian : ProbabilityMeasure ℝ := ⟨gaussianReal 0 1, inferInstance⟩

lemma norm_charFun_finiteVarianceLaw (μ : PMF ℕ) (σ : ℝ) (n : ℕ) (t : ℝ) :
    ‖charFun (finiteVarianceLaw μ σ n : Measure ℝ) t‖ =
      ‖stepCF μ (t / (σ * Real.sqrt n))‖ ^ n := by
  change ‖charFun (scaledLaw μ (fun n => σ * Real.sqrt n) n) t‖ = _
  rw [scaledLaw, charFun_walkLaw_map_div, norm_pow]

/-- The ordinary central limit theorem for the walk, using its genuine finite variance. -/
lemma finiteVariance_clt (hc : IsCritical μ)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure)
    {σ : ℝ} (hσ : 0 < σ)
    (hσsq : σ ^ 2 = ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) :
    Tendsto (finiteVarianceLaw μ σ) atTop (𝓝 standardGaussian) := by
  have h0 : ∫ z : ℤ, (z : ℝ) / σ ∂stepLaw μ = 0 := by
    rw [integral_div, step_integral_eq_zero hc hfinite, zero_div]
  have h1 : ∫ z : ℤ, ((z : ℝ) / σ) ^ 2 ∂stepLaw μ = 1 := by
    simp_rw [div_pow]
    rw [integral_div, ← hσsq, div_self (pow_ne_zero _ hσ.ne')]
  rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
  intro t
  have h := tendsto_charFun_inv_sqrt_mul_pow (P := stepLaw μ)
    (X := fun z : ℤ => (z : ℝ) / σ) (measurable_of_countable _).aemeasurable h0 h1 t
  have heq : ∀ n : ℕ,
      charFun (scaledLaw μ (fun n => σ * Real.sqrt n) n) t =
      charFun ((stepLaw μ).map (fun z : ℤ => (z : ℝ) / σ)) ((Real.sqrt n)⁻¹ * t) ^ n := by
    intro n
    rw [scaledLaw, charFun_walkLaw_map_div]
    congr 1
    rw [charFun_apply_real, integral_map (measurable_of_countable _).aemeasurable
      (by fun_prop), stepCF]
    congr 1
    funext z
    congr 1
    push_cast
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  change Tendsto (fun n => charFun (scaledLaw μ (fun n => σ * Real.sqrt n) n) t) atTop
    (𝓝 (charFun (gaussianReal 0 1) t))
  simp_rw [heq]
  simpa only [charFun_gaussianReal, NNReal.coe_one, ofReal_zero, mul_zero, zero_mul,
    ofReal_one, one_mul, zero_sub, neg_div] using h

/-- Comparison with the ordinary central limit scaling fixes the stable normalization up to
an explicit positive constant. -/
lemma finiteVariance_norming_ratio (h : StableDomain μ α a)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure)
    {σ : ℝ} (hσ : 0 < σ)
    (hσsq : σ ^ 2 = ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) :
    Tendsto (fun n => a n / (σ * Real.sqrt n)) atTop
      (𝓝 (((-1 / 2 : ℝ) / Real.cos (Real.pi * α / 2)) ^ (1 / α))) := by
  have hα := h.alpha_mem
  have hα0 : 0 < α := by linarith
  set c0 : ℝ := Real.cos (Real.pi * α / 2) with hc0
  have hc0neg : c0 < 0 := cos_pi_mul_div_two_neg hα
  set G : ℝ → ℝ := fun s => Real.exp (c0 * |s| ^ α) with hG
  set b : ℕ → ℝ := fun n => σ * Real.sqrt n with hb
  set u : ℕ → ℝ := fun n => a n / b n with hu
  have hbpos : ∀ᶠ n in atTop, 0 < b n := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact mul_pos hσ (Real.sqrt_pos.2 (by exact_mod_cast hn))
  have hupos : ∀ᶠ n in atTop, 0 < u n := by
    filter_upwards [eventually_ge_atTop 1, hbpos] with n hn hbn
    exact div_pos (h.pos n hn) hbn
  have hCLT := finiteVariance_clt h.critical hfinite hσ hσsq
  have normGauss (t : ℝ) : ‖charFun (standardGaussian : Measure ℝ) t‖ =
      Real.exp (-(t ^ 2) / 2) := by
    change ‖charFun (gaussianReal 0 1) t‖ = _
    rw [charFun_gaussianReal, Complex.norm_exp]
    simp [← Complex.ofReal_pow, neg_div]
  have hG1 : G 1 < 1 := by
    simp only [hG, abs_one, Real.one_rpow, mul_one]
    exact Real.exp_lt_one_iff.2 hc0neg
  apply tendsto_of_subseq_tendsto
  intro ns hns
  set v : ℕ → ℝ := fun k => u (ns k) / (1 + u (ns k)) with hv
  have hvmem : ∃ᶠ k in atTop, v k ∈ Icc (0 : ℝ) 1 := by
    apply Eventually.frequently
    filter_upwards [hns.eventually hupos] with k hk
    refine ⟨div_nonneg hk.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
  obtain ⟨w, hw, φ, hφ, hvφ⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_Icc 0 1) hvmem
  rw [closure_Icc] at hw
  set ψ : ℕ → ℕ := ns ∘ φ with hψ
  have hψtop : Tendsto ψ atTop atTop := hns.comp hφ.tendsto_atTop
  have huψpos : ∀ᶠ k in atTop, 0 < u (ψ k) := hψtop.eventually hupos
  have hrecov : ∀ᶠ k in atTop, u (ψ k) = v (φ k) / (1 - v (φ k)) := by
    filter_upwards [huψpos] with k hk
    have hk' : 0 < u (ns (φ k)) := hk
    simp only [hv, hψ, Function.comp]
    have h2 : 1 - u (ns (φ k)) / (1 + u (ns (φ k))) = 1 / (1 + u (ns (φ k))) := by
      field_simp; ring
    rw [h2, div_div_div_cancel_right₀ (by positivity)]
    simp
  rcases hw.2.lt_or_eq with hw1 | hw1
  · set ustar : ℝ := w / (1 - w) with hustar
    have hu_t : Tendsto (fun k => u (ψ k)) atTop (𝓝 ustar) := by
      have : Tendsto (fun k => v (φ k) / (1 - v (φ k))) atTop (𝓝 (w / (1 - w))) :=
        hvφ.div (tendsto_const_nhds.sub hvφ) (by linarith)
      exact this.congr' (hrecov.mono fun k hk => hk.symm)
    have hustar0 : 0 ≤ ustar := div_nonneg hw.1 (by linarith)
    have L1 : Tendsto (fun k => ‖stepCF μ (1 / b (ψ k))‖ ^ ψ k) atTop
        (𝓝 (Real.exp (-1 / 2))) := by
      have hc := (tendsto_charFun_moving (hCLT.comp hψtop)
        (s := fun _ => (1 : ℝ)) tendsto_const_nhds).norm
      rw [normGauss] at hc
      norm_num at hc
      simpa only [norm_charFun_finiteVarianceLaw, b, neg_div] using hc
    have L2 := tendsto_norm_stepCF_pow h hψtop hu_t
    have E : ∀ᶠ k in atTop, 1 / b (ψ k) = u (ψ k) / a (ψ k) := by
      filter_upwards [hψtop.eventually (eventually_ge_atTop 1), hψtop.eventually hbpos]
        with k hk hbk
      dsimp only [u]
      have hak := (h.pos _ hk).ne'
      field_simp
    have heq : Real.exp (-1 / 2) = G ustar :=
      tendsto_nhds_unique L1 (L2.congr' (E.mono fun k hk => by dsimp only; rw [hk]))
    have hval : ustar = ((-1 / 2 : ℝ) / c0) ^ (1 / α) := by
      have h1 : -1 / 2 = c0 * ustar ^ α := by
        apply Real.exp_injective
        simpa only [hG, abs_of_nonneg hustar0] using heq
      have h2 : ustar ^ α = (-1 / 2) / c0 := by
        apply (eq_div_iff hc0neg.ne).2
        linarith
      calc ustar = (ustar ^ α) ^ (1 / α) := by
            rw [← Real.rpow_mul hustar0, mul_one_div_cancel hα0.ne', Real.rpow_one]
        _ = _ := by rw [h2]
    refine ⟨φ, ?_⟩
    rw [← hval]
    exact hu_t
  · exfalso
    have hinv : Tendsto (fun k => 1 / u (ψ k)) atTop (𝓝 0) := by
      have : Tendsto (fun k => (1 - v (φ k)) / v (φ k)) atTop (𝓝 ((1 - w) / w)) :=
        (tendsto_const_nhds.sub hvφ).div hvφ (by rw [hw1]; norm_num)
      rw [hw1, sub_self, zero_div] at this
      refine this.congr' ?_
      filter_upwards [hrecov, huψpos] with k hk hk'
      rw [hk]
      have hv1 : v (φ k) ≠ 1 := by
        intro h1; rw [h1, sub_self, div_zero] at hk; linarith
      have hv0 : v (φ k) ≠ 0 := by
        intro h0; rw [h0, zero_div] at hk; linarith
      have : 1 - v (φ k) ≠ 0 := sub_ne_zero.2 (Ne.symm hv1)
      field_simp
    have L1 : Tendsto (fun k => ‖stepCF μ (1 / a (ψ k))‖ ^ ψ k) atTop (𝓝 (G 1)) :=
      tendsto_norm_stepCF_pow h hψtop tendsto_const_nhds
    have L2 : Tendsto (fun k => ‖stepCF μ ((1 / u (ψ k)) / b (ψ k))‖ ^ ψ k) atTop
        (𝓝 1) := by
      have hc := (tendsto_charFun_moving (hCLT.comp hψtop) hinv).norm
      rw [normGauss] at hc
      norm_num at hc
      simpa only [norm_charFun_finiteVarianceLaw, b, one_div] using hc
    have E : ∀ᶠ k in atTop, 1 / a (ψ k) = (1 / u (ψ k)) / b (ψ k) := by
      filter_upwards [hψtop.eventually (eventually_ge_atTop 1), hψtop.eventually hbpos]
        with k hk hbk
      dsimp only [u]
      have hak := (h.pos _ hk).ne'
      field_simp
    have heq : G 1 = 1 :=
      tendsto_nhds_unique L1 (L2.congr' (E.mono fun k hk => by dsimp only; rw [hk]))
    linarith

/-- **Finite-variance normalization** (source line 864, inventory B09): under the paper's
standing hypothesis, any finite-variance offspring law has `a_n ∼ c √n` for some `c > 0`. -/
theorem exists_norming_isEquivalent_sqrt (h : StableDomain μ α a)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    ∃ c : ℝ, 0 < c ∧ (a ~[atTop] fun n : ℕ => c * Real.sqrt n) := by
  let σ : ℝ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
  have hσ : 0 < σ := Real.sqrt_pos.2
    (step_secondMoment_pos h.critical h.nondegenerate hfinite)
  have hσsq : σ ^ 2 = ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ :=
    Real.sq_sqrt (integral_nonneg fun z => sq_nonneg (z : ℝ))
  let q : ℝ := ((-1 / 2 : ℝ) / Real.cos (Real.pi * α / 2)) ^ (1 / α)
  have hq : 0 < q := Real.rpow_pos_of_pos
    (div_pos_of_neg_of_neg (by norm_num) (cos_pi_mul_div_two_neg h.alpha_mem)) _
  refine ⟨q * σ, mul_pos hq hσ, ?_⟩
  apply isEquivalent_of_tendsto_one
  have ht := (finiteVariance_norming_ratio h hfinite hσ hσsq).div_const q
  rw [div_self hq.ne'] at ht
  convert ht using 1
  funext n
  dsimp only [Pi.div_apply]
  ring

/-- A nondegenerate finite-variance offspring law can only have stable index `2`. -/
theorem alpha_eq_two_of_finiteVariance (h : StableDomain μ α a)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) : α = 2 := by
  obtain ⟨c, hc, he⟩ := exists_norming_isEquivalent_sqrt h hfinite
  have hn : Tendsto (fun n : ℕ => 2 * n) atTop atTop := by
    apply Filter.tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with n hnb
    omega
  have hediv := (he.comp_tendsto hn).div he
  have hsq : Tendsto (fun n : ℕ =>
      (c * Real.sqrt (2 * n : ℕ)) / (c * Real.sqrt n)) atTop (𝓝 (Real.sqrt 2)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hs : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.2 (by exact_mod_cast hn)).ne'
    push_cast
    rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    field_simp
  have hlim : Tendsto (fun n : ℕ => a (2 * n) / a n) atTop (𝓝 (Real.sqrt 2)) :=
    hediv.symm.tendsto_nhds hsq
  have hstable : Tendsto (fun n : ℕ => a (2 * n) / a n) atTop (𝓝 ((2 : ℝ) ^ (1 / α))) := by
    have ht := regularlyVaryingSeq h 2 (by norm_num)
    convert ht using 1
    funext n
    congr 1
    rw [show (2 : ℝ) * n = ((2 * n : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  have heq : (2 : ℝ) ^ (1 / α) = (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact tendsto_nhds_unique hstable hlim
  have hexp := (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).1 heq
  have hα0 : α ≠ 0 := by linarith [h.alpha_mem.1]
  field_simp at hexp
  linarith

lemma summable_offspring_secondMoment
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    Summable (fun j : ℕ => (j : ℝ) ^ 2 * (μ j).toReal) := by
  have hi := (memLp_two_iff_integrable_sq (measurable_of_countable _).aestronglyMeasurable).1 hfinite
  have hme : (Measure.sum fun j : ℕ => μ j • Measure.dirac j) = μ.toMeasure := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
      using Measure.sum_smul_dirac μ.toMeasure
  rw [← hme] at hi
  convert hi.summable_of_dirac using 1
  funext j
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (j : ℝ))]
  ring

lemma finiteVariance_second_moment (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    ∃ ℓ : ℝ → ℝ, SlowlyVarying ℓ ∧ ∀ n : ℕ, 1 ≤ n →
      ∑ j ∈ Finset.range (n + 1), (j : ℝ) ^ 2 * (μ j).toReal = ℓ n * (n : ℝ) ^ ((2 : ℝ) - 2) := by
  let f : ℕ → ℝ := fun j => (j : ℝ) ^ 2 * (μ j).toReal
  have hf := summable_offspring_secondMoment hfinite
  have hpos : 0 < ∑' j, f j := by
    obtain ⟨j, hj, hμj⟩ := hc.exists_two_le_ne_zero hne
    apply hf.tsum_pos (fun j => mul_nonneg (sq_nonneg _) ENNReal.toReal_nonneg) j
    apply mul_pos (pow_pos (by exact_mod_cast (show 0 < j by omega)) 2)
    exact ENNReal.toReal_pos hμj (μ.apply_ne_top j)
  let ℓ : ℝ → ℝ := fun x => ∑ j ∈ Finset.range (⌊x⌋₊ + 1), f j
  have hl : Tendsto ℓ atTop (𝓝 (∑' j, f j)) :=
    (hf.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).comp
      (tendsto_nat_floor_atTop (α := ℝ))
  refine ⟨ℓ, ?_, ?_⟩
  · intro c hc
    have hm : Tendsto (fun x : ℝ => c * x) atTop atTop :=
      (tendsto_const_mul_atTop_of_pos hc).2 tendsto_id
    have ht := (hl.comp hm).div hl hpos.ne'
    rw [div_self hpos.ne'] at ht
    convert ht using 1
    funext x
    rfl
  · intro n hn
    simp only [ℓ, Nat.floor_natCast, sub_self, Real.rpow_zero, mul_one, f]

/-- Every nondegenerate critical finite-variance offspring law satisfies the paper's complete
stable-domain hypothesis with index `2` and normalization `σ √n / √2`. The variance and the
truncated-moment slowly varying function are constructed from the actual offspring law. -/
theorem stableDomain_of_finiteVariance (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    StableDomain μ 2 (fun n : ℕ =>
      (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / Real.sqrt 2) * Real.sqrt n) := by
  let σ : ℝ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
  have hσ : 0 < σ := Real.sqrt_pos.2 (step_secondMoment_pos hc hne hfinite)
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hσsq : σ ^ 2 = ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ :=
    Real.sq_sqrt (integral_nonneg fun z => sq_nonneg (z : ℝ))
  have hCLT := finiteVariance_clt hc hfinite hσ hσsq
  let PL : ℕ → ProbabilityMeasure ℝ := fun n =>
    finiteVarianceLaw μ (σ / Real.sqrt 2) n
  let Pν : ProbabilityMeasure ℝ := ⟨gaussianReal 0 2, inferInstance⟩
  have hw : Tendsto PL atTop (𝓝 Pν) := by
    rw [ProbabilityMeasure.tendsto_iff_tendsto_charFun]
    intro t
    have ht := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hCLT (Real.sqrt 2 * t)
    have heq : ∀ n : ℕ, charFun (PL n : Measure ℝ) t =
        charFun (finiteVarianceLaw μ σ n : Measure ℝ) (Real.sqrt 2 * t) := by
      intro n
      change charFun (scaledLaw μ (fun n => σ / Real.sqrt 2 * Real.sqrt n) n) t =
        charFun (scaledLaw μ (fun n => σ * Real.sqrt n) n) (Real.sqrt 2 * t)
      rw [scaledLaw, scaledLaw, charFun_walkLaw_map_div, charFun_walkLaw_map_div]
      congr 2
      field_simp
    have heqν : charFun (Pν : Measure ℝ) t =
        charFun (standardGaussian : Measure ℝ) (Real.sqrt 2 * t) := by
      change charFun (gaussianReal 0 2) t = charFun (gaussianReal 0 1) (Real.sqrt 2 * t)
      rw [charFun_gaussianReal, charFun_gaussianReal]
      congr 1
      push_cast
      have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
        rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num)]
        norm_num
      linear_combination (t : ℂ) ^ 2 / 2 * h2
    simpa only [heq, heqν] using ht
  refine { critical := hc, nondegenerate := hne, alpha_mem := by norm_num
           monotone := ?_, pos := ?_, converges := ?_ }
  · intro m n hmn
    apply mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by exact_mod_cast hmn))
      (div_pos hσ hs2).le
  · intro n hn
    exact mul_pos (div_pos hσ hs2) (Real.sqrt_pos.2 (by exact_mod_cast hn))
  · refine ⟨gaussianReal 0 2, inferInstance, ?_, ?_⟩
    · intro lam hlam
      have ht := congrFun (mgf_id_gaussianReal (μ := 0) (v := 2)) (-lam)
      simp only [mgf, id] at ht
      rw [ht, Real.rpow_two]
      congr 1
      push_cast
      ring
    · exact ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hw

/-- The finite-variance special case of the stable-domain characterization. -/
theorem inStableDomain_of_finiteVariance (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) : InStableDomain μ :=
  ⟨2, _, stableDomain_of_finiteVariance hc hne hfinite⟩

end BGW.StableTrees.Scalar

