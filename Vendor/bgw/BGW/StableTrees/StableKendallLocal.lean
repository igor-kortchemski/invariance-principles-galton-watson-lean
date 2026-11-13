/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.StableTrees.WalkPassage
public import BGW.StableTrees.StablePassageSubordinator
public import BGW.StableTrees.StableDensityAPI
public import BGW.StableTrees.Scalar.LocalLimit
public import BGW.StableTrees.Scalar.Lattice
public import BGW.StableTrees.Scalar.Normalization

/-! # Local limit for walk passage times

Local limit for the first-hit probabilities of the stable-domain walk, used in Kendall's
identity.

References: (D. G. Kendall, Some problems in the theory of dams, J. Roy. Statist. Soc. Ser. B 19
(1957), 207–212; A. A. Borovkov, *Stochastic Processes in Queueing Theory*, Springer, 1976; J.
Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VII, Corollary 3; local limit
theorem: B. V. Gnedenko and A. N. Kolmogorov, *Limit Distributions for Sums of Independent Random
Variables*, Addison-Wesley, 1954, §50).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory Complex
open scoped NNReal ENNReal BigOperators
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees.Scalar

variable {μ : PMF ℕ} {α : ℝ} {a : ℕ → ℝ}

private theorem tendsto_div_base (h : StableDomain μ α a) {q m' : ℕ → ℕ}
    (hq : Tendsto q atTop atTop) {κ : ℝ} (hκ : 0 < κ)
    (hm' : Tendsto (fun n : ℕ => (m' n : ℝ) / q n) atTop (𝓝 κ)) :
    Tendsto (fun n => a (q n) / a (m' n)) atTop (𝓝 (κ ^ (-(1 / α)))) := by
  have hα := h.alpha_mem
  have hα0 : 0 < α := by linarith
  set c0 : ℝ := Real.cos (Real.pi * α / 2) with hc0
  have hc0neg : c0 < 0 := cos_pi_mul_div_two_neg hα
  set G : ℝ → ℝ := fun s => Real.exp (c0 * |s| ^ α) with hG
  have hmtop : Tendsto m' atTop atTop := by
    have h1 : Tendsto (fun n : ℕ => (m' n : ℝ) / q n * q n) atTop atTop :=
      Tendsto.pos_mul_atTop hκ hm' (tendsto_natCast_atTop_atTop.comp hq)
    have h2 : Tendsto (fun n : ℕ => (m' n : ℝ)) atTop atTop := by
      refine h1.congr' ?_
      filter_upwards [hq.eventually (eventually_ne_atTop 0)] with n hn
      field_simp
    exact tendsto_natCast_atTop_iff.1 h2
  have hm'top := hmtop
  set u : ℕ → ℝ := fun n => a (q n) / a (m' n) with hu
  have hpos : ∀ᶠ n in atTop, 1 ≤ q n ∧ 1 ≤ m' n :=
    (hq.eventually (eventually_ge_atTop 1)).and (hm'top.eventually (eventually_ge_atTop 1))
  have hupos : ∀ᶠ n in atTop, 0 < u n := by
    filter_upwards [hpos] with n hn
    exact div_pos (h.pos (q n) hn.1) (h.pos _ hn.2)
  -- the two identities
  have E1 : ∀ᶠ n in atTop, ‖stepCF μ (1 / a (m' n))‖ ^ m' n =
      (‖stepCF μ (u n / a (q n))‖ ^ q n) ^ ((m' n : ℝ) / q n) := by
    filter_upwards [hpos] with n hn
    have ha := (h.pos (q n) hn.1).ne'
    have ha' := (h.pos _ hn.2).ne'
    rw [rpow_pow_div (norm_nonneg _) (by omega)]
    congr 3
    simp only [hu]; field_simp
  have E2 : ∀ᶠ n in atTop, ‖stepCF μ (1 / a (q n))‖ ^ q n =
      (‖stepCF μ ((1 / u n) / a (m' n))‖ ^ m' n) ^ ((q n : ℝ) / m' n) := by
    filter_upwards [hpos] with n hn
    have ha := (h.pos (q n) hn.1).ne'
    have ha' := (h.pos _ hn.2).ne'
    rw [rpow_pow_div (norm_nonneg _) (by omega)]
    congr 3
    simp only [hu]; field_simp
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
  have hratio : Tendsto (fun k => (m' (ψ k) : ℝ) / q (ψ k)) atTop (𝓝 κ) := hm'.comp hψtop
  rcases hw.2.lt_or_eq with hw1 | hw1
  · -- bounded case
    set ustar : ℝ := w / (1 - w) with hustar
    have hu_t : Tendsto (fun k => u (ψ k)) atTop (𝓝 ustar) := by
      have : Tendsto (fun k => v (φ k) / (1 - v (φ k))) atTop (𝓝 (w / (1 - w))) :=
        hvφ.div (tendsto_const_nhds.sub hvφ) (by linarith)
      exact this.congr' (hrecov.mono fun k hk => hk.symm)
    have hustar0 : 0 ≤ ustar := div_nonneg hw.1 (by linarith)
    have L1 : Tendsto (fun k => ‖stepCF μ (1 / a (m' (ψ k)))‖ ^ m' (ψ k)) atTop (𝓝 (G 1)) :=
      tendsto_norm_stepCF_pow h (hm'top.comp hψtop) tendsto_const_nhds
    have L2 : Tendsto (fun k =>
        (‖stepCF μ (u (ψ k) / a (q (ψ k)))‖ ^ q (ψ k)) ^ ((m' (ψ k) : ℝ) / q (ψ k)))
        atTop (𝓝 (G ustar ^ κ)) :=
      (tendsto_norm_stepCF_pow h (hq.comp hψtop) hu_t).rpow hratio (Or.inl (Real.exp_pos _).ne')
    have heq : G 1 = G ustar ^ κ :=
      tendsto_nhds_unique L1 (L2.congr' ((hψtop.eventually E1).mono fun k hk => hk.symm))
    have hval : ustar = κ ^ (-(1 / α)) := by
      simp only [hG, abs_one, Real.one_rpow, mul_one, ← Real.exp_mul] at heq
      have h1 : c0 = c0 * |ustar| ^ α * κ := Real.exp_injective heq
      have h2 : |ustar| ^ α * κ = 1 := by
        have : c0 * (|ustar| ^ α * κ - 1) = 0 := by linarith
        rcases mul_eq_zero.1 this with h | h
        · exact absurd h hc0neg.ne
        · linarith
      rw [abs_of_nonneg hustar0] at h2
      have h3 : ustar ^ α = κ⁻¹ := by field_simp; linarith
      calc ustar = (ustar ^ α) ^ (1 / α) := by
            rw [← Real.rpow_mul hustar0, mul_one_div_cancel hα0.ne', Real.rpow_one]
        _ = κ ^ (-(1 / α)) := by rw [h3, Real.rpow_neg hκ.le, Real.inv_rpow hκ.le]
    refine ⟨φ, ?_⟩
    rw [← hval]
    exact hu_t
  · -- unbounded case: contradiction
    exfalso
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
    have L1 : Tendsto (fun k => ‖stepCF μ (1 / a (q (ψ k)))‖ ^ q (ψ k)) atTop (𝓝 (G 1)) :=
      tendsto_norm_stepCF_pow h (hq.comp hψtop) tendsto_const_nhds
    have hratio' : Tendsto (fun k => (q (ψ k) : ℝ) / m' (ψ k)) atTop (𝓝 κ⁻¹) := by
      have := hratio.inv₀ hκ.ne'
      refine this.congr fun k => ?_
      simp [inv_div]
    have L2 : Tendsto (fun k => (‖stepCF μ ((1 / u (ψ k)) / a (m' (ψ k)))‖ ^ m' (ψ k)) ^
        ((q (ψ k) : ℝ) / m' (ψ k))) atTop (𝓝 (G 0 ^ κ⁻¹)) :=
      (tendsto_norm_stepCF_pow h (hm'top.comp hψtop) hinv).rpow hratio'
        (Or.inl (Real.exp_pos _).ne')
    have heq : G 1 = G 0 ^ κ⁻¹ :=
      tendsto_nhds_unique L1 (L2.congr' ((hψtop.eventually E2).mono fun k hk => hk.symm))
    have hG0 : G 0 = 1 := by simp [hG, Real.zero_rpow hα0.ne']
    rw [hG0, Real.one_rpow] at heq
    linarith

end BGW.StableTrees.Scalar

namespace BGW.StableTrees

/-- The Kendall kernel `s ↦ (x/s) p_s(-x)`, `s > 0`, `x > 0` (junk elsewhere). -/
noncomputable def kendallKernel (θ x s : ℝ) : ℝ := x / s * stableDensityAt θ s (-x)

/-- The kernel is nonnegative for `x ≥ 0`, `s > 0`. -/
theorem kendallKernel_nonneg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x s : ℝ} (hx : 0 ≤ x) (hs : 0 < s) :
    0 ≤ kendallKernel θ x s := by
  exact mul_nonneg (div_nonneg hx hs.le) (stableDensityAt_nonneg hθ hs _)

/-- Continuity of the Kendall density in time (and jointly in the level) for `s > 0`. -/
theorem kendallKernel_continuousOn {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ContinuousOn (fun z : ℝ × ℝ => kendallKernel θ z.1 z.2) {z | 0 < z.2} := by
  have hdens : ContinuousOn (fun z : ℝ × ℝ => stableDensityAt θ z.2 (-z.1))
      {z | 0 < z.2} := by
    exact (stableDensityAt_jointContinuous hθ).comp
      (continuousOn_snd.prodMk continuousOn_fst.neg) (fun z hz => hz)
  exact (continuousOn_fst.div continuousOn_snd (fun z hz => ne_of_gt hz)).mul hdens

theorem continuousOn_kendallKernel_time {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    ContinuousOn (kendallKernel θ x) (Ioi 0) := by
  exact (kendallKernel_continuousOn hθ).comp (continuousOn_const.prodMk continuousOn_id)
    (fun s hs => hs)

private theorem tendsto_local_mass_seq {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {x κ : ℝ} (hx : 0 < x) (hκ : 0 < κ) {ℓ : ℕ → ℕ}
    (hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n)
    (hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 x)) {q k : ℕ → ℕ}
    (hq : Tendsto q atTop atTop)
    (hk : Tendsto (fun j : ℕ => (k j : ℝ) / q j) atTop (𝓝 κ))
    (hdiv : ∀ j, (Scalar.latticeSpan μ : ℤ) ∣ (k j : ℤ) - ℓ (q j)) :
    Tendsto (fun j : ℕ => (q j : ℝ) *
        (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
          {w | walkHitTime (ℓ (q j)) w = (k j : ℕ∞)} -
      Scalar.latticeSpan μ * kendallKernel θ x ((k j : ℝ) / q j)) atTop (𝓝 0) := by
  have _hx := hx  -- keeps the hypothesis used (unused-variable linter)
  have hmtop : Tendsto k atTop atTop := by
    have h1 : Tendsto (fun j : ℕ => (k j : ℝ) / q j * q j) atTop atTop :=
      Tendsto.pos_mul_atTop hκ hk (tendsto_natCast_atTop_atTop.comp hq)
    have h2 : Tendsto (fun j : ℕ => (k j : ℝ)) atTop atTop := by
      refine h1.congr' ?_
      filter_upwards [hq.eventually (eventually_ne_atTop 0)] with j hj
      field_simp
    exact tendsto_natCast_atTop_iff.1 h2
  have hratio : Tendsto (fun j => B (q j) / B (k j)) atTop (𝓝 (κ ^ (-(1 / θ)))) :=
    Scalar.tendsto_div_base h hq hκ hk
  have harg : Tendsto (fun j => (ℓ (q j) : ℝ) / B (k j)) atTop
      (𝓝 (x * κ ^ (-(1 / θ)))) := by
    have hb := (hscale.comp hq).mul hratio
    refine hb.congr' ?_
    filter_upwards [hq.eventually (eventually_ge_atTop 1),
      hmtop.eventually (eventually_ge_atTop 1)] with j hqj hkj
    have hBq := (h.pos (q j) hqj).ne'
    have hBk := (h.pos (k j) hkj).ne'
    dsimp only [Function.comp_apply]
    field_simp
  have hden : Tendsto (fun j => B (k j) * walkProb μ (k j) (-(ℓ (q j) : ℤ))) atTop
      (𝓝 (Scalar.latticeSpan μ * Scalar.stableDensity θ
        (-(x * κ ^ (-(1 / θ)))))) := by
    have hsmall : Tendsto (fun j => B (k j) * walkProb μ (k j) (-(ℓ (q j) : ℤ)) -
        Scalar.latticeSpan μ * Scalar.stableDensity θ
          (((-(ℓ (q j) : ℤ)) : ℝ) / B (k j))) atTop (𝓝 0) := by
      apply Metric.tendsto_atTop.mpr
      intro ε hε
      obtain ⟨N, hN⟩ := Scalar.localLimit h (half_pos hε)
      obtain ⟨J, hJ⟩ := eventually_atTop.1 (hmtop.eventually (eventually_ge_atTop N))
      refine ⟨J, fun j hj => ?_⟩
      have hkj := hJ j hj
      rw [Real.dist_eq, sub_zero]
      simpa only [Int.cast_neg, Int.cast_natCast] using (hN (k j) hkj (-(ℓ (q j) : ℤ))
        (by simpa [sub_eq_add_neg, add_comm] using hdiv j)).trans_lt (half_lt_self_iff.mpr hε)
    have hdens : Tendsto (fun j => Scalar.stableDensity θ
        (((-(ℓ (q j) : ℤ)) : ℝ) / B (k j))) atTop
        (𝓝 (Scalar.stableDensity θ (-(x * κ ^ (-(1 / θ)))))) := by
      apply (Scalar.continuous_stableDensity h.alpha_mem).continuousAt.tendsto.comp
      simpa only [Int.cast_neg, Int.cast_natCast, neg_div] using harg.neg
    have H := hsmall.add (hdens.const_mul (Scalar.latticeSpan μ : ℝ))
    simp only [zero_add] at H
    refine H.congr fun j => ?_
    ring
  have hfactor : Tendsto (fun j => (ℓ (q j) : ℝ) /
      (((k j : ℝ) / q j) * B (k j))) atTop
      (𝓝 (x * κ ^ (-(1 / θ)) / κ)) := by
    refine ((hscale.comp hq).mul hratio).div hk hκ.ne' |>.congr' ?_
    filter_upwards [hq.eventually (eventually_ge_atTop 1),
      hmtop.eventually (eventually_ge_atTop 1)] with j hqj hkj
    have hBq := (h.pos (q j) hqj).ne'
    have hBk := (h.pos (k j) hkj).ne'
    have hq0 : (q j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqj)
    dsimp only [Function.comp_apply, Pi.div_apply]
    field_simp
  have hmass : Tendsto (fun j => (q j : ℝ) *
      (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
        {w | walkHitTime (ℓ (q j)) w = (k j : ℕ∞)}) atTop
      (𝓝 ((x * κ ^ (-(1 / θ)) / κ) * (Scalar.latticeSpan μ *
        Scalar.stableDensity θ (-(x * κ ^ (-(1 / θ))))))) := by
    refine (hfactor.mul hden).congr' ?_
    filter_upwards [hq.eventually (eventually_ge_atTop 1),
      hmtop.eventually (eventually_ge_atTop 1), hq.eventually hℓ] with j hqj hkj hℓj
    rw [walkHitTime_mass_toReal hℓj hkj]
    have hq0 : (q j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hqj)
    have hk0 : (k j : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hkj)
    have hBk := (h.pos (k j) hkj).ne'
    field_simp
  have hker : Tendsto (fun j => kendallKernel θ x ((k j : ℝ) / q j)) atTop
      (𝓝 (kendallKernel θ x κ)) := by
    have hc : ContinuousAt (fun z : ℝ × ℝ => kendallKernel θ z.1 z.2) (x, κ) :=
      (kendallKernel_continuousOn h.alpha_mem).continuousAt
        ((isOpen_Ioi.preimage continuous_snd).mem_nhds
          (show (x, κ) ∈ {z : ℝ × ℝ | 0 < z.2} from hκ))
    exact hc.tendsto.comp (tendsto_const_nhds.prodMk_nhds hk)
  have H := hmass.sub (hker.const_mul (Scalar.latticeSpan μ : ℝ))
  convert H using 1
  simp only [kendallKernel, stableDensityAt]
  have hθ : θ ≠ 0 := by linarith [h.alpha_mem.1]
  rw [show κ ^ (-1 / θ) * -x = -(x * κ ^ (-(1 / θ))) by rw [neg_div]; ring]
  congr 1
  field_simp
  ring

/-- **Local density limit for the walk passage time, with lattice cancellation.**
Let `d = latticeSpan μ`, `ℓ n / B n → x > 0`, `0 < a ≤ b`. Uniformly over `k ∈ [a n, b n]`
with `d ∣ k - ℓ n`, `n P(first hit of -ℓ n at time k) → d · (x/(k/n)) p_{k/n}(-x)`. -/
theorem tendsto_local_walkHitTime_mass {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {x : ℝ} (hx : 0 < x) {ℓ : ℕ → ℕ} (hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n)
    (hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 x)) {a b : ℝ} (ha : 0 < a)
    (hab : a ≤ b) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k : ℕ, a * (n : ℝ) ≤ k → (k : ℝ) ≤ b * (n : ℝ) →
      ((Scalar.latticeSpan μ : ℤ) ∣ (k : ℤ) - ℓ n) →
        |(n : ℝ) * (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real
              {w | walkHitTime (ℓ n) w = (k : ℕ∞)} -
            Scalar.latticeSpan μ * kendallKernel θ x ((k : ℝ) / n)| ≤ ε := by
  have _hab := hab  -- keeps the hypothesis used (unused-variable linter)
  by_contra H
  rw [eventually_atTop] at H
  push Not at H
  choose q hq k hka hkb hkdiv herr using fun n => H (n + 1)
  have hqpos (j : ℕ) : 0 < q j := by
    have := hq j
    omega
  have hqtop : Tendsto q atTop atTop := tendsto_atTop_mono
    (fun j => by simpa only [id_eq] using (Nat.le_trans (Nat.le_succ j) (hq j))) tendsto_id
  have hmem (j : ℕ) : (k j : ℝ) / q j ∈ Icc a b := by
    have hqR : 0 < (q j : ℝ) := by exact_mod_cast hqpos j
    constructor
    · exact (le_div_iff₀ hqR).2 (by simpa [mul_comm] using hka j)
    · exact (div_le_iff₀ hqR).2 (hkb j)
  obtain ⟨κ, hκmem, φ, hφ, hκ⟩ := isCompact_Icc.tendsto_subseq hmem
  have hκpos : 0 < κ := ha.trans_le hκmem.1
  have Hlim := tendsto_local_mass_seq h hx hκpos hℓ hscale
    (hqtop.comp hφ.tendsto_atTop)
    (show Tendsto (fun j : ℕ => (k (φ j) : ℝ) / q (φ j)) atTop (𝓝 κ) by
      simpa only [Function.comp_def] using hκ)
    (fun j => hkdiv (φ j))
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 Hlim ε hε
  have hsmall := hJ J le_rfl
  rw [Real.dist_eq, sub_zero] at hsmall
  exact (not_lt_of_ge (herr (φ J)).le) (by simpa only [Function.comp_def] using hsmall)

end BGW.StableTrees
