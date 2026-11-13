module

public import BGWLeaves.StableAnalysis.Defs
public import BGWLeaves.StableAnalysis.EtaTransfer
public import BGWLeaves.StableAnalysis.QuantileInversion
public import BGWLeaves.StableAnalysis.GaussianBranch
public import BGWLeaves.StableAnalysis.DomainCriterion
public import BGWLeaves.StableAnalysis.SlowVariation

/-!
# Lemma 3.4 (`lem:hhp`), infinite variance

`B'_n / B_n → (1 - μ₀)^{-1/θ}` for the corrected normings of the law `Y = K - 1 | K ≥ 1`
(`etaLaw μ`) and of the step law `K - 1` (`stepLaw μ`).

* `θ < 2`: both normings are `(-Γ(1-θ))^{1/θ}` times a tail quantile, and the tail quantile of
  `etaLaw` is the multiplier quantile `inf {x ≥ 0 : T(x) ≤ (1-μ₀)/n}` of `stepLaw`
  (`etaLaw_tail_eq`); the ratio tends to `(1-μ₀)^{-1/θ}` by `multQuantile_div_tailQuantile`.
* `θ = 2`: `K_η = (K_ν - μ₀)/(1-μ₀)` is slowly varying and unbounded, and the Gaussian crossing
  points satisfy `g_ν(⌊l n⌋) ≤ g_η(n) ≤ g_ν(⌊l' n⌋)` eventually for `l < 1/(1-μ₀) < l'`; the
  regular variation of index `1/2` of `g_ν` concludes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace BGWLeaves.StableAnalysis.LemHhp

open BGW.StableTrees
open BGWLeaves.StableAnalysis
open BGWLeaves.StableAnalysis.GaussianBranch

/-! ## Transfer of the truncated second moment -/

theorem tendsto_K_eta {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hK : Tendsto (truncSecondMoment (stepLaw μ)) atTop atTop) :
    Tendsto (truncSecondMoment (etaLaw μ)) atTop atTop := by
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  have h1 : Tendsto (fun x => (truncSecondMoment (stepLaw μ) x - (μ 0).toReal) /
      (1 - (μ 0).toReal)) atTop atTop := by
    apply Tendsto.atTop_div_const hq
    have := tendsto_atTop_add_const_right atTop (-(μ 0).toReal) hK
    simpa only [sub_eq_add_neg] using this
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  exact (EtaTransfer.etaLaw_truncSecondMoment_eq μ hx).symm

theorem slowlyVarying_K_eta {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hK : SlowlyVarying (truncSecondMoment (stepLaw μ)))
    (hKinf : Tendsto (truncSecondMoment (stepLaw μ)) atTop atTop) :
    SlowlyVarying (truncSecondMoment (etaLaw μ)) := by
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  intro a ha
  have h1 := hK a ha
  have h2 : Tendsto (fun x => (μ 0).toReal / truncSecondMoment (stepLaw μ) x) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hKinf
  have h3 := (h1.sub h2).div (tendsto_const_nhds.sub h2) (by norm_num : (1 : ℝ) - 0 ≠ 0)
  rw [sub_zero, div_one] at h3
  have hax : Tendsto (fun x : ℝ => a * x) atTop atTop := tendsto_id.const_mul_atTop ha
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), hax.eventually_ge_atTop 1,
    hKinf.eventually_gt_atTop (μ 0).toReal] with x hx1 hx2 hKm
  simp only [Pi.div_apply]
  rw [EtaTransfer.etaLaw_truncSecondMoment_eq μ hx1, EtaTransfer.etaLaw_truncSecondMoment_eq μ hx2,
    div_div_div_cancel_right₀ hq.ne']
  have h0 : truncSecondMoment (stepLaw μ) x ≠ 0 := by
    have := (μ 0).toReal_nonneg
    intro h
    linarith
  have h4 : truncSecondMoment (stepLaw μ) x - (μ 0).toReal ≠ 0 := by
    intro h; linarith
  field_simp

/-! ## The case `θ < 2` -/

theorem tailQuantile_eta_eq {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    tailQuantile (etaLaw μ) n =
      QuantileInversion.multQuantile (stepLaw μ) (1 - (μ 0).toReal) n := by
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  unfold tailQuantile QuantileInversion.multQuantile
  congr 1
  ext x
  simp only [mem_ofPred_eq]
  have e : 1 / (n : ℝ) * (1 - (μ 0).toReal) = (1 - (μ 0).toReal) / n := by ring
  constructor
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rw [EtaTransfer.etaLaw_tail_eq μ hx, div_le_iff₀ hq, e] at h
    exact h
  · rintro ⟨hx, h⟩
    refine ⟨hx, ?_⟩
    rw [EtaTransfer.etaLaw_tail_eq μ hx, div_le_iff₀ hq, e]
    exact h

/-! ## The case `θ = 2` -/

theorem bddAbove_gaussSet {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hK : SlowlyVarying (truncSecondMoment ν)) {n : ℕ} (hn : 0 < n) :
    BddAbove {z : ℝ | 0 ≤ z ∧ 1 / (n : ℝ) ≤ truncSecondMoment ν z / z ^ 2} := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have h0 : Tendsto (fun x : ℝ => truncSecondMoment ν x / x ^ 2) atTop (𝓝 0) := by
    have h := SlowVariation.slow_rpow_neg_mul_tendsto_zero (L := truncSecondMoment ν)
      (truncSecondMoment_mono (ν := ν)).measurable (fun x _ => truncSecondMoment_nonneg' x) hK
      (ε := 2) two_pos
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [Real.rpow_neg hx.le, Real.rpow_two, inv_mul_eq_div]
  have h := h0.eventually (gt_mem_nhds (show (0 : ℝ) < 1 / (n : ℝ) by positivity))
  obtain ⟨X, hX⟩ := eventually_atTop.1 h
  refine ⟨X, fun z hz => ?_⟩
  by_contra hzX
  push Not at hzX
  exact absurd hz.2 (not_le.2 (hX z hzX.le))

section GaussRatio

variable {μ : PMF ℕ}

/-- Upper comparison: `g_η(n) ≤ g_ν(⌊l n⌋)` eventually for `l > 1/(1-μ₀)`. -/
theorem gauss_eta_le (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hKν : SlowlyVarying (truncSecondMoment (stepLaw μ)))
    (hKνinf : Tendsto (truncSecondMoment (stepLaw μ)) atTop atTop)
    (hKη : SlowlyVarying (truncSecondMoment (etaLaw μ)))
    (hKηinf : Tendsto (truncSecondMoment (etaLaw μ)) atTop atTop)
    {l : ℝ} (hl : 1 / (1 - (μ 0).toReal) < l) :
    ∀ᶠ n : ℕ in atTop, gaussQuantile (etaLaw μ) n ≤ gaussQuantile (stepLaw μ) ⌊l * n⌋₊ := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  have hε : 0 < l - 1 / (1 - (μ 0).toReal) := sub_pos.2 hl
  have hg := gaussQuantile_tendsto_atTop hKη hKηinf
  have hm0 := (μ 0).toReal_nonneg
  filter_upwards [gaussQuantile_sq_eventually hKη hKηinf, hg.eventually_ge_atTop 1,
    hg.eventually (hKνinf.eventually_gt_atTop 0),
    eventually_ge_atTop ⌈1 / (l - 1 / (1 - (μ 0).toReal))⌉₊, eventually_gt_atTop 0]
    with n hsq hg1 hK0 hnε hn0
  obtain ⟨hpos, hsq⟩ := hsq
  set z := gaussQuantile (etaLaw μ) n with hz
  set K := truncSecondMoment (stepLaw μ) z with hKdef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hn1 : 1 / (l - 1 / (1 - (μ 0).toReal)) ≤ n := (Nat.le_ceil _).trans (by exact_mod_cast hnε)
  have hn2 : 1 ≤ n * (l - 1 / (1 - (μ 0).toReal)) := by
    rwa [div_le_iff₀ hε] at hn1
  have hfl : l * n - 1 ≤ (⌊l * n⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one (l * n)
    linarith
  have hnq : (n : ℝ) / (1 - (μ 0).toReal) ≤ (⌊l * n⌋₊ : ℝ) := by
    have e : (n : ℝ) / (1 - (μ 0).toReal) = n * (1 / (1 - (μ 0).toReal)) := by ring
    rw [e]
    nlinarith
  have hmpos : 0 < ⌊l * n⌋₊ := by
    have : (0 : ℝ) < (⌊l * n⌋₊ : ℝ) :=
      lt_of_lt_of_le (div_pos hnR hq) hnq
    exact_mod_cast this
  have hmR : (0 : ℝ) < (⌊l * n⌋₊ : ℝ) := by exact_mod_cast hmpos
  have hKη' := EtaTransfer.etaLaw_truncSecondMoment_eq μ hg1
  have hz2 : 0 < z ^ 2 := by positivity
  unfold gaussQuantile
  refine le_csSup (bddAbove_gaussSet hKν hmpos) ⟨hpos.le, ?_⟩
  rw [div_le_div_iff₀ hmR hz2]
  have h1 : z ^ 2 ≤ n * (K / (1 - (μ 0).toReal)) := by
    rw [hsq, hKη']
    apply mul_le_mul_of_nonneg_left _ hnR.le
    exact div_le_div_of_nonneg_right (by linarith) hq.le
  have h2 : (n : ℝ) * (K / (1 - (μ 0).toReal)) = (n / (1 - (μ 0).toReal)) * K := by ring
  have h3 : (n / (1 - (μ 0).toReal)) * K ≤ (⌊l * n⌋₊ : ℝ) * K :=
    mul_le_mul_of_nonneg_right hnq hK0.le
  linarith

/-- Lower comparison: `g_ν(⌊l n⌋) ≤ g_η(n)` eventually for `0 < l < 1/(1-μ₀)`. -/
theorem gauss_eta_ge (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hKν : SlowlyVarying (truncSecondMoment (stepLaw μ)))
    (hKνinf : Tendsto (truncSecondMoment (stepLaw μ)) atTop atTop)
    (hKη : SlowlyVarying (truncSecondMoment (etaLaw μ)))
    {l : ℝ} (hl0 : 0 < l) (hl : l < 1 / (1 - (μ 0).toReal)) :
    ∀ᶠ n : ℕ in atTop, gaussQuantile (stepLaw μ) ⌊l * n⌋₊ ≤ gaussQuantile (etaLaw μ) n := by
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  have hm0 := (μ 0).toReal_nonneg
  have hm : Tendsto (fun n : ℕ => ⌊l * n⌋₊) atTop atTop := tendsto_nat_floor_mul_atTop l hl0
  have hlq : l * (1 - (μ 0).toReal) < 1 := by rwa [lt_div_iff₀ hq] at hl
  have hpos1 : 0 < 1 - l * (1 - (μ 0).toReal) := by linarith
  have hg := (gaussQuantile_tendsto_atTop hKν hKνinf).comp hm
  have hKg := (truncSecondMoment_gaussQuantile_tendsto_atTop hKν hKνinf).comp hm
  filter_upwards [hm.eventually (gaussQuantile_sq_eventually hKν hKνinf),
    hg.eventually_ge_atTop 1,
    hKg.eventually_gt_atTop ((μ 0).toReal / (1 - l * (1 - (μ 0).toReal))),
    eventually_gt_atTop 0] with n hsq hg1 hKbig hn0
  obtain ⟨hpos, hsq⟩ := hsq
  simp only [Function.comp_def] at hg1 hKbig
  set z := gaussQuantile (stepLaw μ) ⌊l * n⌋₊ with hz
  set K := truncSecondMoment (stepLaw μ) z with hKdef
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hKη' := EtaTransfer.etaLaw_truncSecondMoment_eq μ hg1
  have hz2 : 0 < z ^ 2 := by positivity
  have hmle : (⌊l * n⌋₊ : ℝ) ≤ l * n := Nat.floor_le (by positivity)
  have hK0 : 0 ≤ K := truncSecondMoment_nonneg' z
  have hKb : (μ 0).toReal < K * (1 - l * (1 - (μ 0).toReal)) := by
    rwa [div_lt_iff₀ hpos1] at hKbig
  unfold gaussQuantile
  refine le_csSup (bddAbove_gaussSet hKη hn0) ⟨hpos.le, ?_⟩
  rw [div_le_div_iff₀ hnR hz2, hKη']
  have h1 : z ^ 2 ≤ l * n * K := by
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hmle hK0
  have h2 : l * n * K ≤ (K - (μ 0).toReal) / (1 - (μ 0).toReal) * n := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hq]
    have h : 0 ≤ (n : ℝ) * (K * (1 - l * (1 - (μ 0).toReal)) - (μ 0).toReal) :=
      mul_nonneg hnR.le (by linarith)
    nlinarith [h]
  linarith

/-- The ratio of the Gaussian crossing points: `g_η(n)/g_ν(n) → (1-μ₀)^{-1/2}`. -/
theorem gauss_ratio_eta (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hKν : SlowlyVarying (truncSecondMoment (stepLaw μ)))
    (hKνinf : Tendsto (truncSecondMoment (stepLaw μ)) atTop atTop)
    (hKη : SlowlyVarying (truncSecondMoment (etaLaw μ)))
    (hKηinf : Tendsto (truncSecondMoment (etaLaw μ)) atTop atTop) :
    Tendsto (fun n : ℕ => gaussQuantile (etaLaw μ) n / gaussQuantile (stepLaw μ) n) atTop
      (𝓝 (Real.sqrt (1 / (1 - (μ 0).toReal)))) := by
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  have hq' : 0 < 1 / (1 - (μ 0).toReal) := by positivity
  have hgpos : ∀ᶠ n : ℕ in atTop, 0 < gaussQuantile (stepLaw μ) n :=
    (gaussQuantile_sq_eventually hKν hKνinf).mono fun n h => h.1
  rw [tendsto_order]
  constructor
  · intro a ha
    have ha' : max a 0 < Real.sqrt (1 / (1 - (μ 0).toReal)) :=
      max_lt ha (Real.sqrt_pos.2 hq')
    have ha'sq : (max a 0) ^ 2 < 1 / (1 - (μ 0).toReal) :=
      (Real.lt_sqrt (le_max_right _ _)).1 ha'
    have hl0 : 0 < ((max a 0) ^ 2 + 1 / (1 - (μ 0).toReal)) / 2 := by positivity
    have hl : ((max a 0) ^ 2 + 1 / (1 - (μ 0).toReal)) / 2 < 1 / (1 - (μ 0).toReal) := by
      linarith
    have hlim := gaussQuantile_floor_div hKν hKνinf hl0
    have hlt : a < (((max a 0) ^ 2 + 1 / (1 - (μ 0).toReal)) / 2) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact lt_of_le_of_lt (le_max_left a 0)
        ((Real.lt_sqrt (le_max_right _ _)).2 (by linarith))
    filter_upwards [hlim.eventually (lt_mem_nhds hlt), gauss_eta_ge hc hne hKν hKνinf hKη hl0 hl,
      hgpos] with n h1 h2 h3
    exact lt_of_lt_of_le h1 (div_le_div_of_nonneg_right h2 h3.le)
  · intro b hb
    have hb0 : 0 < b := lt_trans (Real.sqrt_pos.2 hq') hb
    have hbsq : 1 / (1 - (μ 0).toReal) < b ^ 2 := (Real.sqrt_lt' hb0).1 hb
    have hl : 1 / (1 - (μ 0).toReal) < (b ^ 2 + 1 / (1 - (μ 0).toReal)) / 2 := by linarith
    have hl0 : 0 < (b ^ 2 + 1 / (1 - (μ 0).toReal)) / 2 := lt_trans hq' hl
    have hlim := gaussQuantile_floor_div hKν hKνinf hl0
    have hlt : ((b ^ 2 + 1 / (1 - (μ 0).toReal)) / 2) ^ (1 / 2 : ℝ) < b := by
      rw [← Real.sqrt_eq_rpow]
      exact (Real.sqrt_lt' hb0).2 (by linarith)
    filter_upwards [hlim.eventually (gt_mem_nhds hlt),
      gauss_eta_le hc hne hKν hKνinf hKη hKηinf hl, hgpos] with n h1 h2 h3
    exact lt_of_le_of_lt (div_le_div_of_nonneg_right h2 h3.le) h1

end GaussRatio

/-! ## Lemma 3.4 -/

/-- **Lemma 3.4**: if `σ² = ∞`, `B'_n / B_n → (1-μ₀)^{-1/θ}`, for the corrected normings
(`norming` of the law of `Y` and of the law of `K - 1`). -/
theorem lem_hhp {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ b, StableDomain μ θ b)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / norming (stepLaw μ) θ n) atTop
      (𝓝 ((1 - (μ 0).toReal) ^ (-(1 / θ)))) := by
  have _ := hap
  obtain ⟨b, hb⟩ := hDA
  have := isProbabilityMeasure_stepLaw μ
  have := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have hstep := stepLaw_lt_neg_one μ
  have hint := integrable_stepLaw hc
  have hmean := mean_stepLaw hc
  have hb' : IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b := by
    rw [hmean]; exact stableDomain_isStableAttracted hb
  have hθ := hb'.alpha_mem
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  have hKinf0 := truncSecondMoment_tendsto_atTop hinf
  have hηinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (etaLaw μ) :=
    not_integrable_of_tendsto_atTop (tendsto_K_eta hc hne hKinf0)
  rcases lt_or_eq_of_le hθ.2 with hlt | heq
  · have hT := DomainCriterion.rightTail_regularlyVarying hb' hstep hint hinf hlt
    have hθ0 : 0 < θ := by linarith [hθ.1]
    have hcpos : 0 < (-Real.Gamma (1 - θ)) ^ (1 / θ) :=
      Real.rpow_pos_of_pos (negGamma_eq hθ.1 hlt).2.2 _
    have hn1 : ∀ ρ : Measure ℤ, ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ρ → ∀ n : ℕ,
        norming ρ θ n = (-Real.Gamma (1 - θ)) ^ (1 / θ) * tailQuantile ρ n := by
      intro ρ hρ n
      unfold norming
      simp only [hρ, hlt, ite_false, ite_true]
    have hmq := QuantileInversion.multQuantile_div_tailQuantile hθ0 hT hq
    rw [show -(1 / θ) = -1 / θ by ring]
    refine hmq.congr' (Eventually.of_forall fun n => ?_)
    show _ = norming (etaLaw μ) θ n / norming (stepLaw μ) θ n
    rw [hn1 _ hηinf, hn1 _ hinf, tailQuantile_eta_eq hc hne, mul_div_mul_left _ _ hcpos.ne']
  · subst heq
    obtain ⟨hKν, hKνinf⟩ := DomainCriterion.truncSecondMoment_slowlyVarying_unbounded hb' hint hinf
    have hKηinf := tendsto_K_eta hc hne hKνinf
    have hKη := slowlyVarying_K_eta hc hne hKν hKνinf
    have hR := gauss_ratio_eta hc hne hKν hKνinf hKη hKηinf
    have e : (1 - (μ 0).toReal) ^ (-(1 / (2 : ℝ))) = Real.sqrt (1 / (1 - (μ 0).toReal)) := by
      rw [Real.sqrt_eq_rpow, one_div (1 - (μ 0).toReal), Real.inv_rpow hq.le, Real.rpow_neg hq.le]
    rw [e]
    refine hR.congr' ?_
    filter_upwards [norming_two_eventually_eq hKν hKνinf, norming_two_eventually_eq hKη hKηinf]
      with n h1 h2
    rw [h1, h2, div_div_div_cancel_right₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2)).ne']

end BGWLeaves.StableAnalysis.LemHhp
