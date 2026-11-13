module

public import BGWLeaves.StableAnalysis.Defs
public import Mathlib.Data.Int.Lemmas

@[expose] public section

open MeasureTheory ProbabilityTheory Complex Filter Set
open scoped Topology

namespace BGWLeaves.StableAnalysis.LocalLimit

open BGW.StableTrees.Scalar

private noncomputable def stepCF (ν : Measure ℤ) (θ : ℝ) : ℂ :=
  ∫ z, cexp (θ * (z : ℂ) * I) ∂ν

private noncomputable def walkCF (ν : Measure ℤ) (n : ℕ) (θ : ℝ) : ℂ :=
  ∫ z, cexp (θ * (z : ℂ) * I) ∂(intWalk ν n)

private instance intWalk_isProbabilityMeasure (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) : IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using (inferInstance : IsProbabilityMeasure ((intWalk ν n) ∗ ν))

private theorem walkCF_eq_pow (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) (θ : ℝ) :
    walkCF ν n θ = stepCF ν θ ^ n := by
  induction n with
  | zero =>
      simp only [walkCF, intWalk, integral_dirac]
      simp
  | succ n ih =>
      rw [pow_succ, ← ih, walkCF, intWalk, integral_conv_int]
      have hsum : ∀ p : ℤ × ℤ,
          cexp (θ * ((p.1 + p.2 : ℤ) : ℂ) * I) =
            cexp (θ * (p.1 : ℂ) * I) * cexp (θ * (p.2 : ℂ) * I) := by
        intro p
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      simp_rw [hsum]
      rw [integral_prod_mul (fun x : ℤ => cexp (θ * (x : ℂ) * I))
        (fun y : ℤ => cexp (θ * (y : ℂ) * I))]
      rfl

private theorem norm_stepCF_le (ν : Measure ℤ) [IsProbabilityMeasure ν] (θ : ℝ) :
    ‖stepCF ν θ‖ ≤ 1 := by
  refine (norm_integral_le_integral_norm _).trans ?_
  simp [Complex.norm_exp]

private theorem continuous_stepCF (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    Continuous (stepCF ν) := by
  apply continuous_of_dominated (bound := fun _ => 1)
  · exact fun θ => (measurable_of_countable _).aestronglyMeasurable
  · exact fun θ => Eventually.of_forall fun z => by simp [Complex.norm_exp]
  · exact integrable_const 1
  · exact Eventually.of_forall fun z => by fun_prop

private theorem norm_stepCF_neg (ν : Measure ℤ) [IsProbabilityMeasure ν] (θ : ℝ) :
    ‖stepCF ν (-θ)‖ = ‖stepCF ν θ‖ := by
  have hneg : stepCF ν (-θ) = starRingEnd ℂ (stepCF ν θ) := by
    rw [stepCF, stepCF, ← integral_conj]
    congr 1
    funext z
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_intCast]
    push_cast
    ring
  rw [hneg, Complex.norm_conj]

private noncomputable def centeredCF (ν : Measure ℤ) (m θ : ℝ) : ℂ :=
  cexp (-((θ * m : ℝ) * I)) * stepCF ν θ

private theorem continuous_centeredCF (ν : Measure ℤ) [IsProbabilityMeasure ν] (m : ℝ) :
    Continuous (centeredCF ν m) := by
  have hphase : Continuous fun θ : ℝ => cexp (-((θ * m : ℝ) * I)) := by fun_prop
  exact hphase.mul (continuous_stepCF ν)

private noncomputable def scaledIntWalk (ν : Measure ℤ) (m : ℝ) (a : ℕ → ℝ)
    (n : ℕ) : Measure ℝ :=
  (intWalk ν n).map (fun z : ℤ => ((z : ℝ) - n * m) / a n)

private instance scaledIntWalk_isProbabilityMeasure (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m : ℝ) (a : ℕ → ℝ) (n : ℕ) : IsProbabilityMeasure (scaledIntWalk ν m a n) := by
  unfold scaledIntWalk
  constructor
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.univ]
  simp

private theorem charFun_scaledIntWalk (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m : ℝ) (a : ℕ → ℝ) (n : ℕ) (t : ℝ) :
    charFun (scaledIntWalk ν m a n) t = centeredCF ν m (t / a n) ^ n := by
  rw [scaledIntWalk, charFun_apply_real,
    integral_map (measurable_of_countable _).aemeasurable
    (by fun_prop)]
  have hconst : ∀ z : ℤ,
      cexp (t * (((z : ℝ) - n * m) / a n) * I) =
        cexp (-((t / a n * (n * m) : ℝ) * I)) * cexp ((t / a n) * (z : ℂ) * I) := by
    intro z
    rw [← Complex.exp_add]
    congr 1
    push_cast
    rcases eq_or_ne (a n) 0 with ha | ha
    · simp [ha]
    · field_simp
      ring
  calc
    _ = ∫ z, cexp (t * (((z : ℝ) - n * m) / a n) * I) ∂intWalk ν n := by
      apply integral_congr_ae
      filter_upwards [] with z
      congr 1
      push_cast
      ring
    _ = ∫ z, cexp (-((t / a n * (n * m) : ℝ) * I)) *
        cexp ((t / a n) * (z : ℂ) * I) ∂intWalk ν n := by
      apply integral_congr_ae
      filter_upwards [] with z
      exact hconst z
    _ = cexp (-((t / a n * (n * m) : ℝ) * I)) *
        ∫ z, cexp ((t / a n) * (z : ℂ) * I) ∂intWalk ν n := by
      rw [integral_const_mul]
    _ = cexp (-((t / a n * (n * m) : ℝ) * I)) * walkCF ν n (t / a n) := by
      rw [walkCF]
      congr 2
      funext z
      congr 2
      rcases eq_or_ne (a n) 0 with ha | ha
      · simp [ha]
      · push_cast
        field_simp
    _ = centeredCF ν m (t / a n) ^ n := by
      rw [walkCF_eq_pow]
      unfold centeredCF stepCF
      rw [mul_pow, ← Complex.exp_nat_mul]
      congr 2
      push_cast
      ring

private theorem tendsto_centeredCF_pow (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) {s : ℕ → ℝ} {t : ℝ}
    (hs : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun j => centeredCF ν m (s j / a (ψ j)) ^ ψ j) atTop
      (𝓝 (stableCF θ t)) := by
  obtain ⟨X, hX, hL, hconv⟩ := h.converges
  have hθ0 : 0 < θ := by linarith [h.alpha_mem.1]
  rw [← charFun_eq_stableCF hθ0 hL]
  have hr : ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun j => ∫ x, f x ∂(scaledIntWalk ν m a (ψ j))) atTop
        (𝓝 (∫ x, f x ∂X)) := fun f => (hconv f).comp hψ
  set PL : ℕ → ProbabilityMeasure ℝ := fun j =>
    ⟨scaledIntWalk ν m a (ψ j), inferInstance⟩
  set PX : ProbabilityMeasure ℝ := ⟨X, hX⟩
  have hw : Tendsto PL atTop (𝓝 PX) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
    exact hr
  have hcf : Tendsto (fun j => charFun (scaledIntWalk ν m a (ψ j)) t) atTop
      (𝓝 (charFun X t)) := by
    rw [ProbabilityMeasure.tendsto_iff_forall_integral_rclike_tendsto ℂ] at hw
    have := hw (BoundedContinuousFunction.innerProbChar t)
    simpa [PL, PX, charFun_eq_integral_innerProbChar] using this
  have hgoal : Tendsto (fun j => charFun (scaledIntWalk ν m a (ψ j)) (s j)) atTop
      (𝓝 (charFun X t)) := by
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hδ : ∃ δ : ℝ, 0 < δ ∧ ∫ x, bumpFn δ x ∂X < ε / 4 := by
      have h1 := (tendsto_integral_bumpFn X).eventually
        (gt_mem_nhds (by linarith : (0 : ℝ) < ε / 4))
      have h2 : ∀ᶠ δ in 𝓝[>] (0 : ℝ),
          ∫ x, bumpFn δ x ∂X < ε / 4 ∧ 0 < δ :=
        (h1.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
      obtain ⟨δ, hδ1, hδ2⟩ := h2.exists
      exact ⟨δ, hδ2, hδ1⟩
    obtain ⟨δ, hδpos, hδX⟩ := hδ
    have e1 : ∀ᶠ j in atTop, |s j - t| ≤ δ := by
      have := (Metric.tendsto_nhds.1 hs) δ hδpos
      filter_upwards [this] with j hj
      rw [Real.dist_eq] at hj
      exact hj.le
    have e2 : ∀ᶠ j in atTop,
        ∫ x, bumpFn δ x ∂(scaledIntWalk ν m a (ψ j)) < ε / 2 :=
      (hr (bumpFn δ)).eventually (gt_mem_nhds (by linarith))
    have e3 : ∀ᶠ j in atTop,
        dist (charFun (scaledIntWalk ν m a (ψ j)) t) (charFun X t) < ε / 4 :=
      (Metric.tendsto_nhds.1 hcf) (ε / 4) (by linarith)
    obtain ⟨N, hN⟩ := (e1.and (e2.and e3)).exists_forall_of_atTop
    refine ⟨N, fun j hj => ?_⟩
    obtain ⟨h1, h2, h3⟩ := hN j hj
    calc dist (charFun (scaledIntWalk ν m a (ψ j)) (s j)) (charFun X t)
        ≤ dist (charFun (scaledIntWalk ν m a (ψ j)) (s j))
            (charFun (scaledIntWalk ν m a (ψ j)) t) +
          dist (charFun (scaledIntWalk ν m a (ψ j)) t) (charFun X t) :=
            dist_triangle _ _ _
      _ < ε / 2 + ε / 4 := by
          gcongr
          rw [dist_eq_norm]
          exact norm_charFun_sub_le _ h1 |>.trans_lt h2
      _ < ε := by linarith
  refine hgoal.congr fun j => ?_
  exact charFun_scaledIntWalk ν m a (ψ j) (s j)

private theorem norm_centeredCF (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m θ : ℝ) : ‖centeredCF ν m θ‖ = ‖stepCF ν θ‖ := by
  rw [centeredCF, norm_mul]
  have hphase : ‖cexp (-((θ * m : ℝ) * I))‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [hphase, one_mul]

private theorem tendsto_norm_centeredCF_pow (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) {s : ℕ → ℝ} {t : ℝ}
    (hs : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun j => ‖centeredCF ν m (s j / a (ψ j))‖ ^ ψ j) atTop
      (𝓝 (Real.exp (Real.cos (Real.pi * θ / 2) * |t| ^ θ))) := by
  have hθ0 : θ ≠ 0 := by linarith [h.alpha_mem.1]
  have hnorm : ∀ j, ‖centeredCF ν m (s j / a (ψ j))‖ =
      ‖stepCF ν (s j / a (ψ j))‖ := fun j => norm_centeredCF ν m _
  rw [← norm_stableCF hθ0]
  have hlim := (continuous_norm.tendsto _).comp (tendsto_centeredCF_pow ν h hψ hs)
  simpa only [Function.comp_def, norm_pow, hnorm] using hlim

private theorem rpow_pow_div {x : ℝ} (hx : 0 ≤ x) {n m : ℕ} (hn : n ≠ 0) :
    (x ^ n) ^ ((m : ℝ) / n) = x ^ m := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_mul hx, mul_div_cancel₀ _ (by exact_mod_cast hn),
    Real.rpow_natCast]

private theorem tendsto_natCast_of_div {m' : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hm' : Tendsto (fun n : ℕ => (m' n : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto m' atTop atTop := by
  have h1 : Tendsto (fun n : ℕ => (m' n : ℝ) / n * n) atTop atTop :=
    Tendsto.pos_mul_atTop hκ hm' tendsto_natCast_atTop_atTop
  have h2 : Tendsto (fun n : ℕ => (m' n : ℝ)) atTop atTop := by
    refine h1.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  exact tendsto_natCast_atTop_iff.1 h2

/-- Convergence of types for any monotone norming of the abstract stable limit. -/
private theorem tendsto_div_of_tendsto_div (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a)
    (hpos : ∀ n, 1 ≤ n → 0 < a n) {m' : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hm' : Tendsto (fun n : ℕ => (m' n : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto (fun n => a n / a (m' n)) atTop (𝓝 (κ ^ (-(1 / θ)))) := by
  have hθ := h.alpha_mem
  have hθ0 : 0 < θ := by linarith
  set c0 : ℝ := Real.cos (Real.pi * θ / 2) with hc0
  have hc0neg : c0 < 0 := cos_pi_mul_div_two_neg hθ
  set G : ℝ → ℝ := fun s => Real.exp (c0 * |s| ^ θ) with hG
  have hm'top := tendsto_natCast_of_div hκ hm'
  set u : ℕ → ℝ := fun n => a n / a (m' n) with hu
  have hposboth : ∀ᶠ n in atTop, 1 ≤ n ∧ 1 ≤ m' n :=
    (eventually_ge_atTop 1).and (hm'top.eventually (eventually_ge_atTop 1))
  have hupos : ∀ᶠ n in atTop, 0 < u n := by
    filter_upwards [hposboth] with n hn
    exact div_pos (hpos n hn.1) (hpos _ hn.2)
  have E1 : ∀ᶠ n in atTop, ‖centeredCF ν m (1 / a (m' n))‖ ^ m' n =
      (‖centeredCF ν m (u n / a n)‖ ^ n) ^ ((m' n : ℝ) / n) := by
    filter_upwards [hposboth] with n hn
    have ha := (hpos n hn.1).ne'
    have ha' := (hpos _ hn.2).ne'
    rw [rpow_pow_div (norm_nonneg _) (by omega)]
    congr 3
    simp only [hu]
    field_simp
  have E2 : ∀ᶠ n in atTop, ‖centeredCF ν m (1 / a n)‖ ^ n =
      (‖centeredCF ν m ((1 / u n) / a (m' n))‖ ^ m' n) ^ ((n : ℝ) / m' n) := by
    filter_upwards [hposboth] with n hn
    have ha := (hpos n hn.1).ne'
    have ha' := (hpos _ hn.2).ne'
    rw [rpow_pow_div (norm_nonneg _) (by omega)]
    congr 3
    simp only [hu]
    field_simp
  have hG1 : G 1 < 1 := by
    simp only [hG, abs_one, Real.one_rpow, mul_one]
    exact Real.exp_lt_one_iff.2 hc0neg
  apply tendsto_of_subseq_tendsto
  intro ns hns
  set v : ℕ → ℝ := fun n => u (ns n) / (1 + u (ns n)) with hv
  have hvmem : ∃ᶠ n in atTop, v n ∈ Icc (0 : ℝ) 1 := by
    apply Eventually.frequently
    filter_upwards [hns.eventually hupos] with n hn
    exact ⟨div_nonneg hn.le (by linarith), (div_le_one (by linarith)).2 (by linarith)⟩
  obtain ⟨w, hw, φ, hφ, hvφ⟩ := tendsto_subseq_of_frequently_bounded
    (Metric.isBounded_Icc 0 1) hvmem
  rw [closure_Icc] at hw
  set ψ : ℕ → ℕ := ns ∘ φ with hψ
  have hψtop : Tendsto ψ atTop atTop := hns.comp hφ.tendsto_atTop
  have huψpos : ∀ᶠ n in atTop, 0 < u (ψ n) := hψtop.eventually hupos
  have hrecov : ∀ᶠ n in atTop, u (ψ n) = v (φ n) / (1 - v (φ n)) := by
    filter_upwards [huψpos] with n hn
    simp only [hv, hψ, Function.comp]
    have h2 : 1 - u (ns (φ n)) / (1 + u (ns (φ n))) = 1 / (1 + u (ns (φ n))) := by
      have hupos' : 0 < u (ns (φ n)) := by simpa [ψ] using hn
      have hd : 1 + u (ns (φ n)) ≠ 0 := by linarith
      field_simp [hd]
      ring
    rw [h2]
    have hd : 1 + u (ns (φ n)) ≠ 0 := by
      have hupos' : 0 < u (ns (φ n)) := by simpa [ψ] using hn
      linarith
    field_simp [hd]
  have hratio : Tendsto (fun n => (m' (ψ n) : ℝ) / ψ n) atTop (𝓝 κ) := hm'.comp hψtop
  rcases hw.2.lt_or_eq with hw1 | hw1
  · set ustar : ℝ := w / (1 - w) with hustar
    have hu_t : Tendsto (fun n => u (ψ n)) atTop (𝓝 ustar) := by
      have ht : Tendsto (fun n => v (φ n) / (1 - v (φ n))) atTop (𝓝 (w / (1 - w))) :=
        hvφ.div (tendsto_const_nhds.sub hvφ) (by linarith)
      exact ht.congr' (hrecov.mono fun n hn => hn.symm)
    have hustar0 : 0 ≤ ustar := div_nonneg hw.1 (by linarith)
    have L1 : Tendsto (fun n => ‖centeredCF ν m (1 / a (m' (ψ n)))‖ ^ m' (ψ n))
        atTop (𝓝 (G 1)) := by
      have ht := tendsto_norm_centeredCF_pow ν h (hm'top.comp hψtop)
        (s := fun _ : ℕ => (1 : ℝ)) (t := 1) tendsto_const_nhds
      simpa [hG, hc0] using ht
    have L2 : Tendsto
        (fun n => (‖centeredCF ν m (u (ψ n) / a (ψ n))‖ ^ ψ n) ^
          ((m' (ψ n) : ℝ) / ψ n)) atTop (𝓝 (G ustar ^ κ)) := by
      have ht := (tendsto_norm_centeredCF_pow ν h hψtop
        (s := fun n => u (ψ n)) (t := ustar) hu_t).rpow hratio
        (Or.inl (Real.exp_pos _).ne')
      simpa [hG, hc0] using ht
    have heq : G 1 = G ustar ^ κ := tendsto_nhds_unique L1
      (L2.congr' ((hψtop.eventually E1).mono fun n hn => hn.symm))
    have hval : ustar = κ ^ (-(1 / θ)) := by
      simp only [hG, abs_one, Real.one_rpow, mul_one, ← Real.exp_mul] at heq
      have h1 : c0 = c0 * |ustar| ^ θ * κ := Real.exp_injective heq
      have h2 : |ustar| ^ θ * κ = 1 := by
        have h3 : c0 * (|ustar| ^ θ * κ - 1) = 0 := by linarith
        rcases mul_eq_zero.1 h3 with h3 | h3
        · exact absurd h3 hc0neg.ne
        · linarith
      rw [abs_of_nonneg hustar0] at h2
      have h3 : ustar ^ θ = κ⁻¹ := by field_simp; linarith
      calc ustar = (ustar ^ θ) ^ (1 / θ) := by
              rw [← Real.rpow_mul hustar0, mul_one_div_cancel hθ0.ne', Real.rpow_one]
        _ = κ ^ (-(1 / θ)) := by rw [h3, Real.rpow_neg hκ.le, Real.inv_rpow hκ.le]
    refine ⟨φ, ?_⟩
    rw [← hval]
    exact hu_t
  · exfalso
    have hinv : Tendsto (fun n => 1 / u (ψ n)) atTop (𝓝 0) := by
      have ht : Tendsto (fun n => (1 - v (φ n)) / v (φ n)) atTop
          (𝓝 ((1 - w) / w)) :=
        (tendsto_const_nhds.sub hvφ).div hvφ (by rw [hw1]; norm_num)
      rw [hw1, sub_self, zero_div] at ht
      refine ht.congr' ?_
      filter_upwards [hrecov, huψpos] with n hn hnpos
      rw [hn]
      have hv1 : v (φ n) ≠ 1 := by
        intro h1
        rw [h1, sub_self, div_zero] at hn
        linarith
      have hv0 : v (φ n) ≠ 0 := by
        intro h0
        rw [h0, zero_div] at hn
        linarith
      have hden : 1 - v (φ n) ≠ 0 := sub_ne_zero.2 (Ne.symm hv1)
      field_simp [hv0, hden]
    have L1 : Tendsto (fun n => ‖centeredCF ν m (1 / a (ψ n))‖ ^ ψ n)
        atTop (𝓝 (G 1)) := by
      have ht := tendsto_norm_centeredCF_pow ν h hψtop
        (s := fun _ : ℕ => (1 : ℝ)) (t := 1) tendsto_const_nhds
      simpa [hG, hc0] using ht
    have hratio' : Tendsto (fun n => (ψ n : ℝ) / m' (ψ n)) atTop (𝓝 κ⁻¹) := by
      have ht := hratio.inv₀ hκ.ne'
      refine ht.congr fun n => ?_
      simp [inv_div]
    have L2 : Tendsto
        (fun n => (‖centeredCF ν m ((1 / u (ψ n)) / a (m' (ψ n)))‖ ^ m' (ψ n)) ^
          ((ψ n : ℝ) / m' (ψ n))) atTop (𝓝 (G 0 ^ κ⁻¹)) := by
      have ht := (tendsto_norm_centeredCF_pow ν h (hm'top.comp hψtop)
        (s := fun n => 1 / u (ψ n)) (t := 0) hinv).rpow hratio'
        (Or.inl (Real.exp_pos _).ne')
      simpa [hG, hc0] using ht
    have heq : G 1 = G 0 ^ κ⁻¹ := tendsto_nhds_unique L1
      (L2.congr' ((hψtop.eventually E2).mono fun n hn => hn.symm))
    have hG0 : G 0 = 1 := by simp [hG, Real.zero_rpow hθ0.ne']
    rw [hG0, Real.one_rpow] at heq
    linarith

private theorem tendsto_div_of_tendsto_div' (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a)
    (hpos : ∀ n, 1 ≤ n → 0 < a n) {m' : ℕ → ℕ} {κ : ℝ} (hκ : 0 < κ)
    (hm' : Tendsto (fun n : ℕ => (m' n : ℝ) / n) atTop (𝓝 κ)) :
    Tendsto (fun n => a (m' n) / a n) atTop (𝓝 (κ ^ (1 / θ))) := by
  have ht := (tendsto_div_of_tendsto_div ν h hpos hκ hm').inv₀
    (Real.rpow_pos_of_pos hκ _).ne'
  rw [Real.rpow_neg hκ.le, inv_inv] at ht
  exact ht.congr fun n => by simp

private theorem regularlyVaryingSeq (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a)
    (hpos : ∀ n, 1 ≤ n → 0 < a n) : BGW.StableTrees.RegularlyVaryingSeq (1 / θ) a := by
  intro c hc
  apply tendsto_div_of_tendsto_div' ν h hpos hc
  exact (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc.le).comp tendsto_natCast_atTop_atTop

private theorem regularize_norming (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (hmono : Monotone a)
    (h : IsStableAttracted ν θ m a) :
    ∃ a' : ℕ → ℝ, Monotone a' ∧ (∀ᶠ n : ℕ in atTop, a' n = a n) ∧
      (∀ n : ℕ, 1 ≤ n → 0 < a' n) ∧ IsStableAttracted ν θ m a' := by
  obtain ⟨N, hN⟩ := h.pos
  let a' : ℕ → ℝ := fun n => a (max n N)
  have hmono' : Monotone a' := fun n k hnk => hmono (max_le_max hnk le_rfl)
  have heq : ∀ᶠ n : ℕ in atTop, a' n = a n := by
    filter_upwards [eventually_ge_atTop N] with n hn
    simp [a', max_eq_left hn]
  have hpos' : ∀ n : ℕ, 1 ≤ n → 0 < a' n := by
    intro n hn
    exact hN (max n N) (le_max_right _ _)
  obtain ⟨X, hX, hL, hconv⟩ := h.converges
  have h' : IsStableAttracted ν θ m a' := by
    refine ⟨h.alpha_mem, ⟨1, fun n hn => ?_⟩, X, hX, hL, fun f => ?_⟩
    · exact hN (max n N) (le_max_right _ _)
    · have hh := hconv f
      refine hh.congr' ?_
      filter_upwards [eventually_ge_atTop N] with n hn
      simp [a', max_eq_left hn]
  exact ⟨a', hmono', heq, hpos', h'⟩

private theorem tendsto_succ_div (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ m : ℝ} {a : ℕ → ℝ} (h : IsStableAttracted ν θ m a)
    (hpos : ∀ n, 1 ≤ n → 0 < a n) :
    Tendsto (fun n => a (n + 1) / a n) atTop (𝓝 1) := by
  have h1 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have ht : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) := by
      exact tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
    rw [add_zero] at ht
    refine ht.congr' ?_
    filter_upwards [eventually_ne_atTop 0] with n hn
    push_cast
    field_simp
  have ht := tendsto_div_of_tendsto_div' ν h hpos one_pos h1
  rwa [Real.one_rpow] at ht

private theorem exists_norm_centeredCF_pow_le_of_mem_Icc
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ m : ℝ} {a : ℕ → ℝ}
    (h : IsStableAttracted ν θ m a) {K : ℝ} :
    ∃ q : ℝ, q < 1 ∧ ∃ N : ℕ, ∀ j : ℕ, N ≤ j → ∀ s : ℝ, s ∈ Icc 1 K →
      ‖centeredCF ν m (s / a j)‖ ^ j ≤ q := by
  have hθ := h.alpha_mem
  have hθ0 : 0 < θ := by linarith
  set c0 : ℝ := Real.cos (Real.pi * θ / 2) with hc0
  have hc0neg : c0 < 0 := cos_pi_mul_div_two_neg hθ
  set G : ℝ → ℝ := fun s => Real.exp (c0 * |s| ^ θ) with hG
  have hG1 : G 1 < 1 := by
    simp only [hG, abs_one, Real.one_rpow, mul_one]
    exact Real.exp_lt_one_iff.2 hc0neg
  have hGle : ∀ s, 1 ≤ |s| → G s ≤ G 1 := by
    intro s hs
    simp only [hG, abs_one, Real.one_rpow, mul_one]
    apply Real.exp_le_exp.2
    have hsθ : 1 ≤ |s| ^ θ := Real.one_le_rpow hs hθ0.le
    nlinarith [c0]
  refine ⟨(1 + G 1) / 2, by linarith, ?_⟩
  by_contra hbad
  push Not at hbad
  choose j hj s hs hviol using hbad
  have hjtop : Tendsto j atTop atTop := tendsto_atTop_mono hj tendsto_id
  obtain ⟨sstar, hsstar, φ, hφ, hsφ⟩ := tendsto_subseq_of_bounded
    (Metric.isBounded_Icc 1 K) hs
  have hlim := tendsto_norm_centeredCF_pow ν h (hjtop.comp hφ.tendsto_atTop)
    (s := s ∘ φ) (t := sstar) hsφ
  rw [closure_Icc] at hsstar
  have hle : G sstar ≤ G 1 := hGle sstar (by
    rw [abs_of_pos (by linarith [hsstar.1])]
    exact hsstar.1)
  have hge : (1 + G 1) / 2 ≤ G sstar := by
    apply ge_of_tendsto hlim
    exact Eventually.of_forall fun j' => (hviol (φ j')).le
  linarith

private theorem exists_norm_centeredCF_pow_le_exp
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ m : ℝ} {a : ℕ → ℝ}
    (h : IsStableAttracted ν θ m a) (hmono : Monotone a)
    (hpos : ∀ n, 1 ≤ n → 0 < a n)
    (hrv : BGW.StableTrees.RegularlyVaryingSeq (1 / θ) a) :
    ∃ γ c A δ : ℝ, 0 < γ ∧ 0 < c ∧ 0 < δ ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ t : ℝ, A ≤ |t| → |t| ≤ δ * a n →
        ‖centeredCF ν m (t / a n)‖ ^ n ≤ Real.exp (-c * |t| ^ γ) := by
  have hθ := h.alpha_mem
  have hθ0 : 0 < θ := by linarith
  obtain ⟨q, hq1, N₀, hN₀⟩ := exists_norm_centeredCF_pow_le_of_mem_Icc ν h (K := 2)
  let q' : ℝ := max q (1 / 2)
  have hq'1 : q' < 1 := max_lt hq1 (by norm_num)
  have hq'0 : 0 < q' := lt_max_of_lt_right (by norm_num)
  obtain ⟨C, hC, hCP⟩ := hrv.exists_potter_global hmono hpos
    (by positivity : (0 : ℝ) ≤ 1 / θ) one_pos
  let β : ℝ := 1 / θ + 1
  have hβ0 : 0 < β := by positivity
  obtain ⟨N₂, hN₂⟩ := ((tendsto_succ_div ν h hpos).eventually
    (gt_mem_nhds (by norm_num : (1 : ℝ) < 2))).exists_forall_of_atTop
  let N₁ : ℕ := max (max N₀ N₂) 1
  have haN₁ : 0 < a N₁ := hpos _ (le_max_right _ _)
  let δ : ℝ := 1 / (2 * a N₁)
  have hδ0 : 0 < δ := by positivity
  let A : ℝ := 4 * C
  let γ : ℝ := 1 / β
  have hγ0 : 0 < γ := by positivity
  let c : ℝ := -Real.log q' / 2 * (2 * C) ^ (-γ)
  have hlogq : Real.log q' < 0 := Real.log_neg hq'0 hq'1
  have hc0 : 0 < c := by
    apply mul_pos (by linarith) (Real.rpow_pos_of_pos (by positivity) _)
  refine ⟨γ, c, A, δ, hγ0, hc0, hδ0, N₁, fun n hn t hAt htδ => ?_⟩
  have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hn
  have han := hpos n hn1
  let τ : ℝ := |t| / a n
  have hτ0 : 0 < τ := div_pos (lt_of_lt_of_le (by positivity) hAt) han
  have hτδ : τ ≤ δ := by
    change |t| / a n ≤ δ
    exact (div_le_iff₀ han).2 htδ
  have hnorm : ‖centeredCF ν m (t / a n)‖ = ‖centeredCF ν m τ‖ := by
    rw [norm_centeredCF, norm_centeredCF]
    dsimp [τ]
    rcases le_or_gt 0 t with ht | ht
    · rw [abs_of_nonneg ht]
    · rw [abs_of_neg ht, neg_div, norm_stepCF_neg]
  rw [hnorm]
  have hex : ∃ j : ℕ, 1 ≤ τ * a j := by
    obtain ⟨j, hj⟩ := (hrv.tendsto_atTop hmono hpos
      (one_div_pos.2 (by linarith : 0 < θ))).eventually_ge_atTop (1 / τ) |>.exists
    exact ⟨j, by simpa [mul_comm] using (div_le_iff₀ hτ0).1 hj⟩
  classical
  let j := Nat.find hex
  have hj1 : 1 ≤ τ * a j := Nat.find_spec hex
  have hjN : N₁ < j := by
    by_contra hle
    have hjle : j ≤ N₁ := le_of_not_gt hle
    have h1 : τ * a j ≤ τ * a N₁ := mul_le_mul_of_nonneg_left (hmono hjle) hτ0.le
    have h2 : τ * a N₁ ≤ 1 / 2 := by
      calc τ * a N₁ ≤ δ * a N₁ := mul_le_mul_of_nonneg_right hτδ haN₁.le
        _ = 1 / 2 := by dsimp [δ]; field_simp
    linarith
  have hjpred : τ * a (j - 1) < 1 := by
    have := Nat.find_min hex (show j - 1 < j by omega)
    push Not at this
    exact this
  have hj2 : τ * a j ≤ 2 := by
    have hN₂j : N₂ ≤ j - 1 := by
      have : N₂ ≤ N₁ := le_trans (le_max_right _ _) (le_max_left _ _)
      omega
    have hsucc := hN₂ (j - 1) hN₂j
    have hpospred : 0 < a (j - 1) := hpos _ (by omega)
    rw [show j - 1 + 1 = j by omega, div_lt_iff₀ hpospred] at hsucc
    nlinarith
  have hj0 : 1 ≤ j := by omega
  have haj : 0 < a j := hpos j hj0
  have hN₀j : N₀ ≤ j := by
    have : N₀ ≤ N₁ := le_trans (le_max_left _ _) (le_max_left _ _)
    omega
  have hqj : ‖centeredCF ν m τ‖ ^ j ≤ q' := by
    have ht := hN₀ j hN₀j (τ * a j) ⟨hj1, hj2⟩
    have heq : τ * a j / a j = τ := by field_simp
    rw [heq] at ht
    exact ht.trans (le_max_left _ _)
  have hjn : j ≤ n := by
    by_contra hlt
    have hjn' : n ≤ j := by omega
    have hanj : a n ≤ a j := hmono hjn'
    have htbound : |t| ≤ 2 := by
      have htau : |t| = τ * a n := by dsimp [τ]; field_simp
      rw [htau]
      nlinarith
    have hA2 : (2 : ℝ) < A := by
      have hC1 : 1 ≤ C := by
        have ht := (hCP 1 1 le_rfl le_rfl).1
        norm_num at ht
        have ha1 := hpos 1 le_rfl
        nlinarith
      dsimp [A]
      linarith
    linarith
  have hPot := (hCP j n hj0 hjn).1
  have hratio : |t| / (2 * C) ≤ ((n : ℝ) / j) ^ β := by
    have htau : |t| = τ * a n := by dsimp [τ]; field_simp
    rw [div_le_iff₀ (by positivity), htau]
    calc τ * a n ≤ τ * (C * ((n : ℝ) / j) ^ β * a j) := by
          apply mul_le_mul_of_nonneg_left hPot hτ0.le
      _ = C * ((n : ℝ) / j) ^ β * (τ * a j) := by ring
      _ ≤ C * ((n : ℝ) / j) ^ β * 2 := by
          apply mul_le_mul_of_nonneg_left hj2 (by positivity)
      _ = ((n : ℝ) / j) ^ β * (2 * C) := by ring
  have hnm1 : (1 : ℝ) ≤ (n : ℝ) / j := by
    rw [le_div_iff₀ (by positivity), one_mul]
    exact_mod_cast hjn
  let k := n / j
  have hk_le : j * k ≤ n := Nat.mul_div_le n j
  have hk_ge : (n : ℝ) / j / 2 ≤ k := by
    have := BGW.StableTrees.half_le_natFloor hnm1
    rwa [Nat.floor_div_eq_div] at this
  have hφ1 : ‖centeredCF ν m τ‖ ≤ 1 := by
    rw [norm_centeredCF]
    exact (norm_stepCF_le ν τ)
  have hpow : ‖centeredCF ν m τ‖ ^ n ≤ q' ^ k := by
    calc ‖centeredCF ν m τ‖ ^ n ≤ ‖centeredCF ν m τ‖ ^ (j * k) :=
          pow_le_pow_of_le_one (norm_nonneg _) hφ1 hk_le
      _ = (‖centeredCF ν m τ‖ ^ j) ^ k := pow_mul _ _ _
      _ ≤ q' ^ k := pow_le_pow_left₀ (by positivity) hqj k
  calc ‖centeredCF ν m τ‖ ^ n ≤ q' ^ k := hpow
    _ = Real.exp (Real.log q' * k) := by rw [← Real.rpow_natCast, Real.rpow_def_of_pos hq'0]
    _ ≤ Real.exp (-c * |t| ^ γ) := by
      apply Real.exp_le_exp.2
      have h1 : (|t| / (2 * C)) ^ γ ≤ (n : ℝ) / j := by
        calc (|t| / (2 * C)) ^ γ ≤ (((n : ℝ) / j) ^ β) ^ γ :=
              Real.rpow_le_rpow (by positivity) hratio (by positivity)
          _ = (n : ℝ) / j := by
              rw [← Real.rpow_mul (by positivity), show β * γ = 1 by dsimp [β, γ]; field_simp,
                Real.rpow_one]
      have h2 : (|t| / (2 * C)) ^ γ = |t| ^ γ * (2 * C) ^ (-γ) := by
        rw [Real.div_rpow (abs_nonneg _) (by positivity), Real.rpow_neg (by positivity),
          div_eq_mul_inv]
      have h3 : -c * |t| ^ γ = Real.log q' / 2 * (|t| / (2 * C)) ^ γ := by
        rw [h2, show c = -Real.log q' / 2 * (2 * C) ^ (-γ) by rfl]
        ring
      rw [h3]
      calc Real.log q' / 2 * (|t| / (2 * C)) ^ γ ≥
            Real.log q' / 2 * ((n : ℝ) / j) := by
              apply mul_le_mul_of_nonpos_left h1 (by linarith)
        _ = Real.log q' * ((n : ℝ) / j / 2) := by ring
        _ ≥ Real.log q' * k := by
              apply mul_le_mul_of_nonpos_left hk_ge hlogq.le

private def supportDiffs (ν : Measure ℤ) : Set ℤ :=
  {d | ∃ x y : ℤ, ν {x} ≠ 0 ∧ ν {y} ≠ 0 ∧ d = x - y}

private noncomputable def supportDiffGenerator (ν : Measure ℤ) : ℤ :=
  Submodule.IsPrincipal.generator (Ideal.span (supportDiffs ν))

private theorem supportDiffGenerator_dvd (ν : Measure ℤ) {x y : ℤ}
    (hx : ν {x} ≠ 0) (hy : ν {y} ≠ 0) :
    supportDiffGenerator ν ∣ x - y := by
  have hmem : x - y ∈ Ideal.span (supportDiffs ν) :=
    Ideal.subset_span ⟨x, y, hx, hy, rfl⟩
  rw [Submodule.IsPrincipal.mem_iff_eq_smul_generator] at hmem
  obtain ⟨c, hc⟩ := hmem
  rw [hc, smul_eq_mul]
  exact Dvd.intro_left c rfl

private theorem exists_two_atoms (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnl : ¬ IsLatticeLaw ν) :
    ∃ x y : ℤ, x ≠ y ∧ 0 < ν {x} ∧ 0 < ν {y} := by
  have hcover : ν (⋃ x : ℤ, ({x} : Set ℤ)) ≠ 0 := by
    have hset : (⋃ x : ℤ, ({x} : Set ℤ)) = Set.univ := by ext y; simp
    rw [hset]
    simp
  obtain ⟨x, hx⟩ := exists_measure_pos_of_not_measure_iUnion_null hcover
  have hcompl : ν ({x}ᶜ) ≠ 0 := by
    intro hzero
    have hxa : ∀ᵐ y ∂ν, y = x := by
      rw [ae_iff_of_countable]
      intro y hy
      by_cases hyx : y = x
      · exact hyx
      · have hsub : ({y} : Set ℤ) ⊆ ({x}ᶜ) := by
          intro z hz
          simp only [Set.mem_singleton_iff] at hz
          simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
          exact fun hzx => hyx (hz.symm.trans hzx)
        have hyzero : ν {y} = 0 := by
          apply le_antisymm _ bot_le
          calc ν {y} ≤ ν ({x}ᶜ) := measure_mono hsub
            _ = 0 := hzero
        exact (hy hyzero).elim
    apply hnl
    refine ⟨x, 2, by norm_num, ?_⟩
    filter_upwards [hxa] with y hy
    simp [hy]
  have hcomplpos : 0 < ν ({x}ᶜ) := bot_lt_iff_ne_bot.mpr hcompl
  have hcover' : (⋃ y : ℤ, (if y = x then (∅ : Set ℤ) else {y})) = ({x}ᶜ) := by
    ext y
    simp
  have hunion : ν (⋃ y : ℤ, (if y = x then (∅ : Set ℤ) else {y})) ≠ 0 := by
    rw [hcover']
    exact hcompl
  obtain ⟨y, hy⟩ := exists_measure_pos_of_not_measure_iUnion_null hunion
  have hyx : y ≠ x := by
    by_contra h
    subst y
    simp at hy
  refine ⟨x, y, Ne.symm hyx, hx, ?_⟩
  simpa [hyx] using hy

private theorem supportDiffGenerator_natAbs_eq_one
    (ν : Measure ℤ) [IsProbabilityMeasure ν] (hnl : ¬ IsLatticeLaw ν) :
    (supportDiffGenerator ν).natAbs = 1 := by
  obtain ⟨b, y, hby, hb, hy⟩ := exists_two_atoms ν hnl
  have hg0 : supportDiffGenerator ν ≠ 0 := by
    intro hg
    have hae : ∀ᵐ x ∂ν, x = b := by
      rw [ae_iff_of_countable]
      intro x hx
      have hd := supportDiffGenerator_dvd ν hx (ne_of_gt hb)
      rw [hg] at hd
      have hzero : x - b = 0 := by simpa using hd
      omega
    apply hnl
    refine ⟨b, 2, by norm_num, ?_⟩
    filter_upwards [hae] with x hx
    simp [hx]
  have hpos : 0 < (supportDiffGenerator ν).natAbs := Int.natAbs_pos.mpr hg0
  by_contra hne
  have htwo : 2 ≤ (supportDiffGenerator ν).natAbs := by omega
  have hdvd : ((supportDiffGenerator ν).natAbs : ℤ) ∣ supportDiffGenerator ν := by
    rw [Int.natCast_natAbs]
    rw [abs_dvd]
  exact hnl (by
    refine ⟨b, (supportDiffGenerator ν).natAbs, htwo, ?_⟩
    rw [ae_iff_of_countable]
    intro x hx
    exact dvd_trans hdvd (supportDiffGenerator_dvd ν hx (ne_of_gt hb)))

private theorem exists_int_of_norm_stepCF_eq_one (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnl : ¬ IsLatticeLaw ν) {θ : ℝ} (h : ‖stepCF ν θ‖ = 1) :
    ∃ n : ℤ, θ * (supportDiffGenerator ν : ℝ) = n * (2 * Real.pi) := by
  obtain ⟨z, w, hzw, hzpos, hwpos⟩ := exists_two_atoms ν hnl
  set e : ℤ → ℂ := fun k => cexp (θ * (k : ℂ) * I) with he
  have hen : ∀ k, ‖e k‖ = 1 := by
    intro k
    simp only [he]
    rw [show θ * (k : ℂ) * I = ((θ * (k : ℝ) : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I]
  have hφ : stepCF ν θ = ∫ k, e k ∂ν := by rfl
  set u : ℂ := starRingEnd ℂ (stepCF ν θ) with hu
  have hun : ‖u‖ = 1 := by rw [hu, Complex.norm_conj, h]
  have huφ : u * stepCF ν θ = 1 := by
    rw [hu, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, h]
    simp
  have hint : Integrable e ν :=
    Integrable.of_bound (C := 1) (measurable_of_countable _).aestronglyMeasurable
      (Eventually.of_forall fun k => (hen k).le)
  let g : ℤ → ℝ := fun k => 1 - (u * e k).re
  have hg0 : 0 ≤ g := by
    intro k
    change 0 ≤ 1 - (u * e k).re
    rw [sub_nonneg]
    calc (u * e k).re ≤ ‖u * e k‖ := Complex.re_le_norm _
      _ = 1 := by rw [norm_mul, hun, hen, one_mul]
  have hgi : Integrable g ν := (integrable_const 1).sub ((hint.const_mul u).re)
  have hre : ∫ k, (u * e k).re ∂ν = (∫ k, u * e k ∂ν).re := integral_re (hint.const_mul u)
  have hgint : ∫ k, g k ∂ν = 0 := by
    change ∫ k, (1 - (u * e k).re) ∂ν = 0
    rw [integral_sub (f := fun _ : ℤ => (1 : ℝ)) (g := fun k => (u * e k).re)
      (integrable_const 1) ((hint.const_mul u).re), integral_const, probReal_univ,
      one_smul, hre, integral_const_mul, ← hφ, huφ, Complex.one_re, sub_self]
  have hae := (integral_eq_zero_iff_of_nonneg hg0 hgi).1 hgint
  rw [Filter.EventuallyEq, ae_iff_of_countable] at hae
  have heAtom : ∀ k : ℤ, ν {k} ≠ 0 → u * e k = 1 := by
    intro k hk
    have hkr : ν {k} ≠ 0 := hk
    have hz := hae k hkr
    simp only [g, Pi.zero_apply, sub_eq_zero] at hz
    exact eq_one_of_norm_eq_one_of_re_eq_one (by rw [norm_mul, hun, hen, one_mul]) hz.symm
  have hu0 : u ≠ 0 := by
    intro hzero
    have := heAtom z (ne_of_gt hzpos)
    rw [hzero, zero_mul] at this
    exact zero_ne_one this
  have hezw : e z = e w := by
    exact mul_left_cancel₀ hu0 ((heAtom z (ne_of_gt hzpos)).trans (heAtom w (ne_of_gt hwpos)).symm)
  have hphase : cexp (θ * ((z - w : ℤ) : ℂ) * I) = 1 := by
    have hezw' : cexp (θ * (z : ℂ) * I) = cexp (θ * (w : ℂ) * I) := by
      simpa [e] using hezw
    have hsub : cexp (θ * (z : ℂ) * I - θ * (w : ℂ) * I) = 1 := by
      calc cexp (θ * (z : ℂ) * I - θ * (w : ℂ) * I) =
          cexp (θ * (z : ℂ) * I) / cexp (θ * (w : ℂ) * I) := by rw [Complex.exp_sub]
        _ = 1 := by rw [hezw']; exact div_self (Complex.exp_ne_zero _)
    convert hsub using 1
    congr 2
    push_cast
    ring
  have hzw' : ∃ n : ℤ, θ * ((z - w : ℤ) : ℝ) = n * (2 * Real.pi) := by
    rw [Complex.exp_eq_one_iff] at hphase
    obtain ⟨n, hn⟩ := hphase
    refine ⟨n, ?_⟩
    have him := congrArg Complex.im hn
    simpa using him
  have hmem : ∀ d ∈ Ideal.span (supportDiffs ν), cexp (θ * (d : ℂ) * I) = 1 := by
    intro d hd
    induction hd using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨x, y, hx', hy', rfl⟩ := hx
        have h1 := heAtom x hx'
        have h2 := heAtom y hy'
        have hxy : e x = e y := mul_left_cancel₀ hu0 (h1.trans h2.symm)
        have hyne : e y ≠ 0 := by
          intro hz
          have := hen y
          rw [hz, norm_zero] at this
          exact zero_ne_one this
        have : cexp (θ * ((x - y : ℤ) : ℂ) * I) = e x / e y := by
          simp only [he]
          rw [← Complex.exp_sub]
          congr 1
          push_cast
          ring
        rw [this, hxy, div_self hyne]
    | zero => simp
    | add x y _ _ hx hy =>
        rw [show θ * ((x + y : ℤ) : ℂ) * I = θ * (x : ℂ) * I + θ * (y : ℂ) * I by
          push_cast; ring, Complex.exp_add, hx, hy, one_mul]
    | smul c x _ hx =>
        rw [smul_eq_mul,
          show θ * ((c * x : ℤ) : ℂ) * I = (c : ℂ) * (θ * (x : ℂ) * I) by
            push_cast; ring,
          Complex.exp_int_mul, hx, one_zpow]
  have hgmem := hmem _ (Submodule.IsPrincipal.generator_mem (Ideal.span (supportDiffs ν)))
  rw [Complex.exp_eq_one_iff] at hgmem
  obtain ⟨n, hn⟩ := hgmem
  refine ⟨n, ?_⟩
  have hnIm := congrArg Complex.im hn
  simpa [supportDiffGenerator] using hnIm

private theorem norm_stepCF_lt_one (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hnl : ¬ IsLatticeLaw ν) {θ : ℝ} (h0 : θ ≠ 0) (hθ : |θ| ≤ Real.pi) :
    ‖stepCF ν θ‖ < 1 := by
  rcases (norm_stepCF_le ν θ).lt_or_eq with hlt | heq
  · exact hlt
  · exfalso
    obtain ⟨n, hn⟩ := exists_int_of_norm_stepCF_eq_one ν hnl heq
    have hg := supportDiffGenerator_natAbs_eq_one ν hnl
    have hsq : supportDiffGenerator ν * supportDiffGenerator ν = 1 := by
      have hh : (supportDiffGenerator ν).natAbs = (1 : ℤ).natAbs := by simpa using hg
      have hsquare := (Int.natAbs_eq_iff_sq_eq).1 hh
      nlinarith [hsquare]
    have hg0 : supportDiffGenerator ν ≠ 0 := by
      intro hz
      rw [hz, Int.natAbs_zero] at hg
      norm_num at hg
    have hgpm : supportDiffGenerator ν = 1 ∨ supportDiffGenerator ν = -1 := by
      by_cases hposg : 0 < supportDiffGenerator ν
      · left
        nlinarith
      · right
        have hnegg : supportDiffGenerator ν < 0 :=
          lt_of_le_of_ne (le_of_not_gt hposg) hg0
        nlinarith
    have hval : |θ| = |(n : ℝ)| * (2 * Real.pi) := by
      have hh := congrArg abs hn
      rcases hgpm with hgpm | hgpm
      · rw [hgpm, Int.cast_one, mul_one] at hh
        simpa [abs_mul] using hh
      · rw [hgpm, Int.cast_neg, Int.cast_one] at hh
        simpa [abs_mul] using hh
    have hn0 : n ≠ 0 := by
      intro hnz
      rw [hnz] at hval
      have hθzero : |θ| = 0 := by simpa using hval
      exact h0 (abs_eq_zero.mp hθzero)
    have hn1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hnZ : (1 : ℤ) ≤ |n| := Int.one_le_abs hn0
      exact_mod_cast hnZ
    nlinarith [Real.pi_pos]

private theorem exists_norm_stepCF_le_of_le_abs
    (ν : Measure ℤ) [IsProbabilityMeasure ν] (hnl : ¬ IsLatticeLaw ν) {δ : ℝ}
    (hδ : 0 < δ) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ θ : ℝ, δ ≤ |θ| → |θ| ≤ Real.pi →
      ‖stepCF ν θ‖ ≤ q := by
  let K : Set ℝ := {θ | δ ≤ |θ|} ∩ {θ | |θ| ≤ Real.pi}
  have hKc : IsCompact K := by
    apply Metric.isCompact_of_isClosed_isBounded
    · exact (isClosed_le continuous_const continuous_abs).inter
        (isClosed_le continuous_abs continuous_const)
    · refine (Metric.isBounded_closedBall (x := (0 : ℝ)) (r := Real.pi)).subset ?_
      intro θ hθ
      simpa [Metric.mem_closedBall, Real.dist_eq] using hθ.2
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · refine ⟨0, le_rfl, one_pos, fun θ h1 h2 => ?_⟩
    have : θ ∈ K := ⟨h1, h2⟩
    rw [hKe] at this
    exact absurd this (Set.notMem_empty θ)
  · obtain ⟨θ₀, hθ₀, hmax⟩ := hKc.exists_isMaxOn hKne
      (continuous_norm.comp (continuous_stepCF ν)).continuousOn
    have h0 : θ₀ ≠ 0 := by
      intro h
      change δ ≤ |θ₀| ∧ |θ₀| ≤ Real.pi at hθ₀
      have := hθ₀.1
      rw [h, abs_zero] at this
      linarith
    change δ ≤ |θ₀| ∧ |θ₀| ≤ Real.pi at hθ₀
    refine ⟨‖stepCF ν θ₀‖, norm_nonneg _, norm_stepCF_lt_one ν hnl h0 hθ₀.2,
      fun θ h1 h2 => ?_⟩
    exact hmax ⟨h1, h2⟩


private noncomputable def truncCF (ν : Measure ℤ) (m : ℝ) (a : ℕ → ℝ)
    (n : ℕ) (t : ℝ) : ℂ :=
  (Ioc (-(Real.pi * a n)) (Real.pi * a n)).indicator
    (fun t => centeredCF ν m (t / a n) ^ n) t

private theorem integrable_truncCF (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m : ℝ) (a : ℕ → ℝ) (n : ℕ) : Integrable (truncCF ν m a n) := by
  unfold truncCF
  rw [integrable_indicator_iff measurableSet_Ioc]
  have hc : Continuous fun t : ℝ => centeredCF ν m (t / a n) ^ n := by
    have := continuous_centeredCF ν m
    fun_prop
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

private theorem tendsto_integral_norm_truncCF_sub
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {α m : ℝ} {a : ℕ → ℝ}
    (h : IsStableAttracted ν α m a) (hmono : Monotone a)
    (hpos : ∀ n, 1 ≤ n → 0 < a n) (hnl : ¬ IsLatticeLaw ν) :
    Tendsto (fun n => ∫ t, ‖truncCF ν m a n t - stableCF α t‖) atTop (𝓝 0) := by
  have hα := h.alpha_mem
  have hrv := regularlyVaryingSeq ν h hpos
  have hat := hrv.tendsto_atTop hmono hpos (one_div_pos.2 (by linarith [hα.1]))
  obtain ⟨γ, c, A, δ, hγ, hc0, hδ, N₃, hN₃⟩ := exists_norm_centeredCF_pow_le_exp ν h hmono hpos hrv
  set δ' : ℝ := min δ (Real.pi) with hδ'
  have hδ'0 : 0 < δ' := lt_min hδ (by positivity)
  obtain ⟨q, hq0, hq1, hq⟩ := exists_norm_stepCF_le_of_le_abs ν hnl hδ'0
  have hcont : ∀ n : ℕ, Continuous fun t : ℝ => centeredCF ν m (t / a n) ^ n := fun n => by
    have := continuous_centeredCF ν m; fun_prop
  -- the central part
  set S : ℕ → Set ℝ := fun n => Ioc (-(δ' * a n)) (δ' * a n) with hS
  set hn : ℕ → ℝ → ℂ := fun n t =>
    (S n).indicator (fun t => centeredCF ν m (t / a n) ^ n) t - stableCF α t with hhn
  set rn : ℕ → ℝ → ℂ := fun n t =>
    truncCF ν m a n t - (S n).indicator (fun t => centeredCF ν m (t / a n) ^ n) t with hrn
  set D : ℝ → ℝ := fun t => (Icc (-A) A).indicator (fun _ => (1 : ℝ)) t +
    Real.exp (-c * |t| ^ γ) + ‖stableCF α t‖ with hD
  have hDint : Integrable D := by
    refine ((integrable_indicator_iff measurableSet_Icc).2 (integrableOn_const ?_ ?_)).add ?_
      |>.add (integrable_stableCF hα).norm
    · simp
    · simp
    · have := integrable_rpow_abs_mul_exp_neg (s := 0) (p := γ) (c := c) (by norm_num) hγ hc0
      simpa using this
  have hcentral : Tendsto (fun n => ∫ t, ‖hn n t‖) atTop (𝓝 0) := by
    have h0 : (0 : ℝ) = ∫ t : ℝ, (fun _ => (0 : ℝ)) t := by simp
    rw [h0]
    apply tendsto_integral_filter_of_dominated_convergence D
    · refine Eventually.of_forall fun n => ?_
      exact (((hcont n).aestronglyMeasurable (μ := volume).indicator measurableSet_Ioc).sub
        (continuous_stableCF (by linarith)).aestronglyMeasurable).norm
    · filter_upwards [eventually_ge_atTop N₃, eventually_ge_atTop 1] with n hn3 hn1
      refine Eventually.of_forall fun t => ?_
      have han := hpos n hn1
      rw [norm_norm]
      refine (norm_sub_le _ _).trans ?_
      simp only [hD]
      gcongr
      by_cases ht : t ∈ S n
      · rw [indicator_of_mem ht, norm_pow]
        have htS : |t| ≤ δ * a n := by
          have := ht; simp only [hS, mem_Ioc] at this
          rw [abs_le]; constructor
          · nlinarith [min_le_left δ (Real.pi)]
          · nlinarith [min_le_left δ (Real.pi)]
        by_cases htA : |t| ≤ A
        · have : t ∈ Icc (-A) A := abs_le.1 htA
          rw [indicator_of_mem this]
          have hb : ‖centeredCF ν m (t / a n)‖ ≤ 1 := by
            rw [norm_centeredCF]; exact norm_stepCF_le ν _
          have := pow_le_one₀ (norm_nonneg _) hb (n := n)
          linarith [Real.exp_pos (-c * |t| ^ γ)]
        · push Not at htA
          have := hN₃ n hn3 t htA.le htS
          linarith [indicator_nonneg (fun _ _ => zero_le_one) t (s := Icc (-A) A)
            (f := fun _ => (1 : ℝ))]
      · rw [indicator_of_notMem ht, norm_zero]
        exact add_nonneg (indicator_nonneg (fun _ _ => zero_le_one) _) (Real.exp_pos _).le
    · exact hDint
    · refine Eventually.of_forall fun t => ?_
      have hev : ∀ᶠ n in atTop, t ∈ S n := by
        have h1 := (hat.const_mul_atTop hδ'0).eventually_gt_atTop |t|
        filter_upwards [h1] with n hn
        simp only [hS, mem_Ioc]
        constructor <;> [linarith [neg_abs_le t]; linarith [le_abs_self t]]
      have hlim := tendsto_centeredCF_pow ν h (ψ := id) tendsto_id (tendsto_const_nhds (x := t))
      have : Tendsto (fun n => hn n t) atTop (𝓝 0) := by
        rw [show (0 : ℂ) = stableCF α t - stableCF α t by ring]
        refine (hlim.sub_const (stableCF α t)).congr' ?_
        filter_upwards [hev] with n hn'
        simp only [hhn, id, indicator_of_mem hn']
      have := (continuous_norm.tendsto _).comp this
      simpa [Function.comp_def] using this
  -- the annulus
  have hann : ∀ n, 1 ≤ n → ∫ t, ‖rn n t‖ ≤ 2 * (Real.pi) * (a n * q ^ n) := by
    intro n hn1
    have han := hpos n hn1
    set L : ℝ := Real.pi * a n with hL
    have hbd : ∀ t, ‖rn n t‖ ≤ (Ioc (-L) L).indicator (fun _ => q ^ n) t := by
      intro t
      simp only [hrn, truncCF]
      by_cases ht : t ∈ Ioc (-L) L
      · rw [indicator_of_mem ht, indicator_of_mem ht]
        by_cases ht' : t ∈ S n
        · rw [indicator_of_mem ht', sub_self, norm_zero]; positivity
        · rw [indicator_of_notMem ht', sub_zero, norm_pow]
          apply pow_le_pow_left₀ (norm_nonneg _)
          rw [norm_centeredCF]
          apply hq
          · simp only [hS, mem_Ioc, not_and_or, not_lt, not_le] at ht'
            rw [abs_div, abs_of_pos han, le_div_iff₀ han]
            rcases ht' with h1 | h1
            · rw [abs_of_neg (by nlinarith)]; linarith
            · rw [abs_of_pos (by nlinarith)]; linarith
          · rw [abs_div, abs_of_pos han, div_le_iff₀ han]
            have := ht; simp only [mem_Ioc] at this
            rw [abs_le]; constructor
            · have : -L ≤ t := this.1.le; rw [hL] at this; linarith [show Real.pi * a n = Real.pi * a n by ring]
            · have : t ≤ L := this.2; rw [hL] at this; linarith [show Real.pi * a n = Real.pi * a n by ring]
      · rw [indicator_of_notMem ht, indicator_of_notMem ht]
        have : t ∉ S n := by
          intro ht'
          apply ht
          simp only [hS, mem_Ioc] at ht' ⊢
          have hle : δ' * a n ≤ L := by
            rw [hL]
            have := min_le_right δ (Real.pi)
            calc δ' * a n ≤ Real.pi * a n := by gcongr
              _ = Real.pi * a n := by ring
          constructor <;> linarith [ht'.1, ht'.2]
        rw [indicator_of_notMem this, sub_self, norm_zero]
    calc ∫ t, ‖rn n t‖ ≤ ∫ t, (Ioc (-L) L).indicator (fun _ => q ^ n) t := by
          apply integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) _
            (Eventually.of_forall hbd)
          exact (integrable_indicator_iff measurableSet_Ioc).2 (integrableOn_const (by simp))
      _ = 2 * (Real.pi) * (a n * q ^ n) := by
          rw [integral_indicator_const _ measurableSet_Ioc, Real.volume_real_Ioc,
            smul_eq_mul, max_eq_left (by
              have : 0 ≤ Real.pi * a n := by positivity
              rw [hL]; linarith)]
          rw [hL]; ring
  have hann0 : Tendsto (fun n => 2 * (Real.pi) * (a n * q ^ n)) atTop (𝓝 0) := by
    obtain ⟨C, hC, hCn⟩ := hrv.exists_le_mul hmono hpos
      (by have := hα.1; positivity) (by rw [div_lt_one (by linarith)]; exact hα.1)
    have h1 : Tendsto (fun n : ℕ => C * ((n : ℝ) * q ^ n)) atTop (𝓝 (C * 0)) :=
      (tendsto_self_mul_const_pow_of_lt_one hq0 hq1).const_mul C
    rw [mul_zero] at h1
    have h2 : Tendsto (fun n => a n * q ^ n) atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ h1
      · filter_upwards [eventually_ge_atTop 1] with n hn
        exact mul_nonneg (hpos n hn).le (pow_nonneg hq0 n)
      · filter_upwards [eventually_ge_atTop 1] with n hn
        have := hCn n hn
        calc a n * q ^ n ≤ C * n * q ^ n := by gcongr
          _ = C * ((n : ℝ) * q ^ n) := by ring
    have := h2.const_mul (2 * (Real.pi))
    rwa [mul_zero] at this
  -- combine
  have hsplit : ∀ n, 1 ≤ n → ∫ t, ‖truncCF ν m a n t - stableCF α t‖ ≤
      (∫ t, ‖hn n t‖) + ∫ t, ‖rn n t‖ := by
    intro n hn1
    have hi1 : Integrable (fun t => ‖hn n t‖) :=
      ((((integrable_indicator_iff measurableSet_Ioc).2
        ((hcont n).integrableOn_Icc.mono_set Ioc_subset_Icc_self))).sub
        (integrable_stableCF hα)).norm
    have hi2 : Integrable (fun t => ‖rn n t‖) :=
      ((integrable_truncCF ν m a n).sub ((integrable_indicator_iff measurableSet_Ioc).2
        ((hcont n).integrableOn_Icc.mono_set Ioc_subset_Icc_self))).norm
    rw [← integral_add hi1 hi2]
    apply integral_mono_of_nonneg (Eventually.of_forall fun t => norm_nonneg _) (hi1.add hi2)
    refine Eventually.of_forall fun t => ?_
    simp only [hhn, hrn]
    rw [show truncCF ν m a n t - stableCF α t =
      ((S n).indicator (fun t => centeredCF ν m (t / a n) ^ n) t - stableCF α t) +
      (truncCF ν m a n t - (S n).indicator (fun t => centeredCF ν m (t / a n) ^ n) t) by ring]
    exact norm_add_le _ _
  have hsum := (hcentral.add hann0)
  rw [add_zero] at hsum
  refine squeeze_zero' (Eventually.of_forall fun n => integral_nonneg fun t => norm_nonneg _) ?_
    hsum
  filter_upwards [eventually_ge_atTop 1] with n hn1
  exact (hsplit n hn1).trans (by linarith [hann n hn1])


private theorem intWalk_real_singleton (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) (k : ℤ) :
    (((intWalk ν n).real {k} : ℝ) : ℂ) =
      (1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, stepCF ν θ ^ n * cexp (-(θ * k * I)) := by
  rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  have hswap : ∫ θ in Ioc (-Real.pi) Real.pi, stepCF ν θ ^ n * cexp (-(θ * k * I)) =
      ∫ z, ∫ θ in Ioc (-Real.pi) Real.pi, cexp (θ * ((z - k : ℤ) : ℝ) * I) ∂volume
        ∂(intWalk ν n) := by
    have h1 : ∀ θ : ℝ, stepCF ν θ ^ n * cexp (-(θ * k * I)) =
        ∫ z, cexp (θ * ((z - k : ℤ) : ℝ) * I) ∂(intWalk ν n) := by
      intro θ
      rw [← walkCF_eq_pow, walkCF, ← integral_mul_const]
      congr 1; funext z
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    simp_rw [h1]
    apply integral_integral_swap
    apply Integrable.of_bound (C := 1)
    · apply Measurable.aestronglyMeasurable
      apply measurable_from_prod_countable_left
      intro z
      fun_prop
    · refine Eventually.of_forall fun p => ?_
      obtain ⟨x, y⟩ := p
      simp only [Function.uncurry_apply_pair]
      rw [show ((x : ℂ) * (((y - k : ℤ) : ℝ) : ℂ) * I) = ((x * ((y - k : ℤ) : ℝ) : ℝ) : ℂ) * I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
  rw [hswap]
  have h2 : ∀ z : ℤ, ∫ θ in Ioc (-Real.pi) Real.pi, cexp (θ * ((z - k : ℤ) : ℝ) * I) =
      ({k} : Set ℤ).indicator (fun _ => ((2 * Real.pi : ℝ) : ℂ)) z := by
    intro z
    rw [← intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    have := intervalIntegral_cexp_int_mul_I (z - k)
    push_cast at this ⊢
    rw [this]
    by_cases hz : z = k
    · simp [hz]
    · simp [hz, sub_eq_zero]
  simp_rw [h2]
  rw [integral_indicator_const _ (measurableSet_singleton k)]
  rw [Complex.real_smul]
  push_cast
  field_simp


/-- Centering cancels against the translated Fourier phase. -/
private theorem centeredCF_pow_mul_phase (ν : Measure ℤ) (m : ℝ)
    (a : ℕ → ℝ) (n : ℕ) (k : ℤ) (t : ℝ) :
    centeredCF ν m (t / a n) ^ n *
        cexp (-(t * (((k : ℝ) - n * m) / a n) * I)) =
      stepCF ν (t / a n) ^ n * cexp (-((t / a n) * k * I)) := by
  rw [centeredCF, mul_pow, ← Complex.exp_nat_mul]
  calc
    _ = stepCF ν (t / a n) ^ n *
        (cexp ((n : ℂ) * (-(((t / a n) * m : ℝ) * I))) *
          cexp (-(t * (((k : ℝ) - n * m) / a n) * I))) := by ring
    _ = _ := by
      rw [← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- Fourier inversion after scaling, with the real centering retained in the phase. -/
private theorem mul_intWalk_real_eq (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (m : ℝ) {a : ℕ → ℝ} {n : ℕ} (han : 0 < a n) (k : ℤ) :
    ((a n * (intWalk ν n).real {k} : ℝ) : ℂ) = (1 / (2 * Real.pi)) *
      ∫ t, truncCF ν m a n t *
        cexp (-(t * (((k : ℝ) - n * m) / a n) * I)) := by
  let F : ℝ → ℂ := fun t => stepCF ν t ^ n * cexp (-(t * k * I))
  rw [Complex.ofReal_mul, intWalk_real_singleton]
  set L : ℝ := Real.pi * a n with hL
  have hL0 : 0 ≤ L := by positivity
  have h1 : ∫ θ in (-Real.pi)..Real.pi, F θ =
      (a n)⁻¹ • ∫ t in (-L)..L, F (t / a n) := by
    rw [intervalIntegral.integral_comp_div _ han.ne', smul_smul,
      inv_mul_cancel₀ han.ne', one_smul]
    congr 1 <;> dsimp [L] <;> field_simp
  have h2 : ∫ t in (-L)..L, F (t / a n) =
      ∫ t, truncCF ν m a n t *
        cexp (-(t * (((k : ℝ) - n * m) / a n) * I)) := by
    rw [intervalIntegral.integral_of_le (by linarith), ← integral_indicator measurableSet_Ioc]
    congr 1
    funext t
    unfold truncCF
    by_cases ht : t ∈ Ioc (-L) L
    · rw [indicator_of_mem ht, indicator_of_mem ht]
      simpa only [F, Complex.ofReal_div] using
        (centeredCF_pow_mul_phase ν m a n k t).symm
    · rw [indicator_of_notMem ht, indicator_of_notMem ht, zero_mul]
  change (a n : ℂ) * ((1 / (2 * Real.pi)) * ∫ θ in (-Real.pi)..Real.pi, F θ) = _
  rw [h1, h2, Complex.real_smul]
  have ha : (a n : ℂ) ≠ 0 := by exact_mod_cast han.ne'
  push_cast
  field_simp
  congr 1
  funext t
  congr 2
  ring

/-- A bound independent of the integer endpoint. -/
private theorem abs_mul_intWalk_real_sub_le
    (ν : Measure ℤ) [IsProbabilityMeasure ν] {α m : ℝ} {a : ℕ → ℝ}
    (hα : 1 < α ∧ α ≤ 2) {n : ℕ} (han : 0 < a n) (k : ℤ) :
    |a n * (intWalk ν n).real {k} - stableDensity α (((k : ℝ) - n * m) / a n)| ≤
      (1 / (2 * Real.pi)) * ∫ t, ‖truncCF ν m a n t - stableCF α t‖ := by
  set x : ℝ := ((k : ℝ) - n * m) / a n
  set E : ℝ → ℂ := fun t => cexp (-(t * x * I)) with hE
  have hEn : ∀ t, ‖E t‖ = 1 := fun t => norm_cexp_neg_mul_I' t x
  have hi1 : Integrable (fun t => truncCF ν m a n t * E t) :=
    (integrable_truncCF ν m a n).mul_bdd (c := 1) (by fun_prop)
      (Eventually.of_forall fun t => (hEn t).le)
  have hi2 : Integrable (fun t => stableCF α t * E t) :=
    (integrable_stableCF hα).mul_bdd (c := 1) (by fun_prop)
      (Eventually.of_forall fun t => (hEn t).le)
  have h1 := mul_intWalk_real_eq ν m han k
  have hre : a n * (intWalk ν n).real {k} = (1 / (2 * Real.pi)) *
      (∫ t, truncCF ν m a n t * E t).re := by
    have hh := congrArg Complex.re h1
    rw [Complex.ofReal_re] at hh
    rw [hh]
    simp only [hE, x]
    rw [show (1 / (2 * (Real.pi : ℂ))) = (((1 / (2 * Real.pi) : ℝ)) : ℂ) by
      push_cast; ring, re_ofReal_mul]
    push_cast
    rfl
  have hd : stableDensity α x = (1 / (2 * Real.pi)) *
      (∫ t, stableCF α t * E t).re := by
    rw [stableDensity]
  rw [hre, hd, ← mul_sub, ← Complex.sub_re, ← integral_sub hi1 hi2, abs_mul,
    abs_of_nonneg (by positivity)]
  gcongr
  calc |(∫ t, (truncCF ν m a n t * E t - stableCF α t * E t)).re|
      ≤ ‖∫ t, (truncCF ν m a n t * E t - stableCF α t * E t)‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ t, ‖truncCF ν m a n t * E t - stableCF α t * E t‖ := norm_integral_le_integral_norm _
    _ = ∫ t, ‖truncCF ν m a n t - stableCF α t‖ := by
      congr 1
      funext t
      rw [← sub_mul, norm_mul, hEn, mul_one]

/-- The abstract local limit theorem, uniformly over all integer endpoints. -/
theorem llt_abstract (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ}
    (_hint : Integrable (fun z : ℤ => (z : ℝ)) ν) (hnl : ¬ IsLatticeLaw ν)
    {a : ℕ → ℝ} (hmono : Monotone a) (h : IsStableAttracted ν θ (mean ν) a)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ k : ℤ,
      |a n * intWalkProb ν n k - stableDensity θ (((k : ℝ) - n * mean ν) / a n)| ≤ ε := by
  obtain ⟨a', hmono', heq, hpos', h'⟩ := regularize_norming ν hmono h
  have hlim := (tendsto_integral_norm_truncCF_sub ν h' hmono' hpos' hnl).const_mul
    (1 / (2 * Real.pi))
  rw [mul_zero] at hlim
  have hev : ∀ᶠ n in atTop, (1 / (2 * Real.pi)) *
      (∫ t, ‖truncCF ν (mean ν) a' n t - stableCF θ t‖) < ε :=
    hlim.eventually (gt_mem_nhds hε)
  obtain ⟨N, hN⟩ := (hev.and (heq.and (eventually_ge_atTop 1))).exists_forall_of_atTop
  refine ⟨N, fun n hn k => ?_⟩
  obtain ⟨hbound, heqn, hn1⟩ := hN n hn
  rw [← heqn]
  exact (abs_mul_intWalk_real_sub_le ν h.alpha_mem (hpos' n hn1) k).trans hbound.le

end BGWLeaves.StableAnalysis.LocalLimit

end
