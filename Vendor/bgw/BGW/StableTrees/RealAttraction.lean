/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Probability.RealWalk
public import BGW.StableTrees.Attraction.Defs
public import BGW.StableTrees.Scalar.FiniteVariance
public import BGW.StableTrees.StableLaw
public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Real scalar stable attraction

This module packages weak attraction of real iid sums, proves the convergence-of-types theorem
for arbitrary eventually positive normalizers, and connects the real formulation to the existing
integer walk and offspring stable-domain predicates.

References: W. Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
ch. XVII; N. H. Bingham, C. M. Goldie and J. L. Teugels, *Regular Variation* (1987), §1.5
(Potter bounds).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Complex
open scoped Topology

namespace BGW.StableTrees

open BGW.Probability.RealWalk

/-- Real scalar attraction (audit correction 1): `B n > 0` only eventually; no monotonicity, no
centering, and no moment assumption. -/
structure IsRealStableAttracted (ν : ProbabilityMeasure ℝ) (θ : ℝ) (B : ℕ → ℝ) : Prop where
  index_mem : 1 < θ ∧ θ ≤ 2
  pos : ∀ᶠ n in atTop, 0 < B n
  converges : Tendsto (fun n => scaledSumLaw ν B n) atTop (𝓝 (stableLaw θ))

private lemma rpow_pow_div {x : ℝ} (hx : 0 ≤ x) {n m : ℕ} (hn : n ≠ 0) :
    (x ^ n) ^ ((m : ℝ) / n) = x ^ m := by
  rw [← Real.rpow_natCast x n, ← Real.rpow_mul hx, mul_div_cancel₀ _ (by exact_mod_cast hn),
    Real.rpow_natCast]

private theorem tendsto_natCast_of_div {m q : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hq : Tendsto q atTop atTop)
    (hmq : Tendsto (fun j => (m j : ℝ) / q j) atTop (𝓝 c)) :
    Tendsto m atTop atTop := by
  have h1 : Tendsto (fun j => ((m j : ℝ) / q j) * q j) atTop atTop :=
    Tendsto.pos_mul_atTop hc hmq (tendsto_natCast_atTop_atTop.comp hq)
  have h2 : Tendsto (fun j => (m j : ℝ)) atTop atTop := by
    refine h1.congr' ?_
    filter_upwards [hq.eventually (eventually_ne_atTop 0)] with j hj
    field_simp
  exact tendsto_natCast_atTop_iff.1 h2

private theorem tendsto_norm_charFun_pow_moving {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) {s : ℕ → ℝ} {t : ℝ}
    (hs : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun j => ‖charFun (ν : Measure ℝ) (s j / B (m j))‖ ^ m j) atTop
      (𝓝 (Real.exp (Real.cos (Real.pi * θ / 2) * |t| ^ θ))) := by
  have hc := Scalar.tendsto_charFun_moving (h.converges.comp hm) hs
  have hc' : Tendsto
      (fun j => charFun (scaledSumLaw ν B (m j) : Measure ℝ) (s j)) atTop
      (𝓝 (charFun (stableLaw θ : Measure ℝ) t)) := by
    simpa only [Function.comp_apply] using hc
  rw [show (fun j => charFun (scaledSumLaw ν B (m j) : Measure ℝ) (s j)) =
      (fun j => charFun (ν : Measure ℝ) (s j / B (m j)) ^ m j) from by
        funext j
        exact charFun_scaledSumLaw ν B (m j) (s j)] at hc'
  rw [charFun_stableLaw h.index_mem] at hc'
  have hn := hc'.norm
  simpa only [norm_pow, Scalar.norm_stableCF (by linarith [h.index_mem.1] : θ ≠ 0)] using hn

/-- Invariance under eventual equality of normalizers. -/
theorem IsRealStableAttracted.congr_eventually {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B B' : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) (hBB' : ∀ᶠ n in atTop, B n = B' n) :
    IsRealStableAttracted ν θ B' := by
  refine ⟨h.index_mem, ?_, ?_⟩
  · filter_upwards [h.pos, hBB'] with n hn hEq
    rw [← hEq]
    exact hn
  · refine h.converges.congr' ?_
    filter_upwards [hBB'] with n hEq
    change (sumLaw ν n).map (fun x : ℝ => x / B n) =
      (sumLaw ν n).map (fun x : ℝ => x / B' n)
    rw [hEq]

/-- Moving-argument characteristic-function convergence (Node 4): along `m j → ∞` and
`u j → u₀`, `φ_ν (u j / B (m j)) ^ (m j) → φ_{stableLaw θ} u₀`. -/
theorem IsRealStableAttracted.tendsto_charFun_pow_moving {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {m : ℕ → ℕ}
    (hm : Tendsto m atTop atTop) {u : ℕ → ℝ} {u₀ : ℝ} (hu : Tendsto u atTop (𝓝 u₀)) :
    Tendsto (fun j => charFun (ν : Measure ℝ) (u j / B (m j)) ^ m j) atTop
      (𝓝 (charFun (stableLaw θ : Measure ℝ) u₀)) := by
  have hc := Scalar.tendsto_charFun_moving (h.converges.comp hm) hu
  have hc' : Tendsto
      (fun j => charFun (scaledSumLaw ν B (m j) : Measure ℝ) (u j)) atTop
      (𝓝 (charFun (stableLaw θ : Measure ℝ) u₀)) := by
    simpa only [Function.comp_apply] using hc
  have heq : (fun j => charFun (scaledSumLaw ν B (m j) : Measure ℝ) (u j)) =
      (fun j => charFun (ν : Measure ℝ) (u j / B (m j)) ^ m j) := by
    funext j
    exact charFun_scaledSumLaw ν B (m j) (u j)
  exact heq ▸ hc'

/-- The ratio theorem (Node 4): no monotonicity, no lattice, no criticality. -/
theorem IsRealStableAttracted.tendsto_norming_ratio {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {m q : ℕ → ℕ} {c : ℝ} (hc : 0 < c)
    (hq : Tendsto q atTop atTop)
    (hmq : Tendsto (fun j => (m j : ℝ) / q j) atTop (𝓝 c)) :
    Tendsto (fun j => B (m j) / B (q j)) atTop (𝓝 (c ^ (1 / θ))) := by
  have hθ := h.index_mem
  have hθ0 : 0 < θ := by linarith
  set c₀ : ℝ := Real.cos (Real.pi * θ / 2) with hc₀
  have hc₀neg : c₀ < 0 := Scalar.cos_pi_mul_div_two_neg hθ
  set G : ℝ → ℝ := fun x => Real.exp (c₀ * |x| ^ θ) with hG
  have hmtop := tendsto_natCast_of_div hc hq hmq
  set u : ℕ → ℝ := fun j => B (m j) / B (q j) with hu
  have hposq : ∀ᶠ j in atTop, 0 < B (q j) := hq.eventually h.pos
  have hposm : ∀ᶠ j in atTop, 0 < B (m j) := hmtop.eventually h.pos
  have hidx : ∀ᶠ j in atTop, 1 ≤ q j ∧ 1 ≤ m j :=
    (hq.eventually (eventually_ge_atTop 1)).and
      (hmtop.eventually (eventually_ge_atTop 1))
  have hupos : ∀ᶠ j in atTop, 0 < u j := by
    filter_upwards [hposq, hposm] with j hqj hmj
    exact div_pos hmj hqj
  have E1 : ∀ᶠ j in atTop,
      ‖charFun (ν : Measure ℝ) (1 / B (q j))‖ ^ q j =
        (‖charFun (ν : Measure ℝ) (u j / B (m j))‖ ^ m j) ^ ((q j : ℝ) / m j) := by
    filter_upwards [hposq, hposm, hidx] with j hqj hmj hj
    have hqne : q j ≠ 0 := by omega
    have hmne : m j ≠ 0 := by omega
    rw [rpow_pow_div (norm_nonneg _) hmne]
    congr 3
    simp only [hu]
    field_simp
  have E2 : ∀ᶠ j in atTop,
      ‖charFun (ν : Measure ℝ) (1 / B (m j))‖ ^ m j =
        (‖charFun (ν : Measure ℝ) ((1 / u j) / B (q j))‖ ^ q j) ^ ((m j : ℝ) / q j) := by
    filter_upwards [hposq, hposm, hidx, hupos] with j hqj hmj hj huj
    have hqne : q j ≠ 0 := by omega
    have hmne : m j ≠ 0 := by omega
    rw [rpow_pow_div (norm_nonneg _) hqne]
    congr 3
    simp only [hu]
    field_simp
  have hG1 : G 1 < 1 := by
    simp only [hG, abs_one, Real.one_rpow, mul_one]
    exact Real.exp_lt_one_iff.2 hc₀neg
  apply tendsto_of_subseq_tendsto
  intro ns hns
  set v : ℕ → ℝ := fun k => u (ns k) / (1 + u (ns k)) with hv
  have hvmem : ∃ᶠ k in atTop, v k ∈ Set.Icc (0 : ℝ) 1 := by
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
    have h2 : 1 - u (ns (φ k)) / (1 + u (ns (φ k))) =
        1 / (1 + u (ns (φ k))) := by
      change 0 < u (ns (φ k)) at hk
      have hden : 1 + u (ns (φ k)) ≠ 0 := by linarith
      field_simp [hden]
      ring
    simp only [hv, hψ, Function.comp]
    rw [h2]
    change 0 < u (ns (φ k)) at hk
    have hden : 1 + u (ns (φ k)) ≠ 0 := by linarith
    field_simp [hden]
  have hratio : Tendsto (fun k => (q (ψ k) : ℝ) / m (ψ k)) atTop (𝓝 c⁻¹) := by
    have ht := hmq.comp hψtop
    have ht' := ht.inv₀ hc.ne'
    refine ht'.congr fun k => ?_
    simp [inv_div]
  rcases hw.2.lt_or_eq with hw1 | hw1
  · set ustar : ℝ := w / (1 - w) with hustar
    have hustar_t : Tendsto (fun k => u (ψ k)) atTop (𝓝 ustar) := by
      have ht : Tendsto (fun k => v (φ k) / (1 - v (φ k))) atTop
          (𝓝 (w / (1 - w))) :=
        hvφ.div (tendsto_const_nhds.sub hvφ) (by linarith)
      exact ht.congr' (hrecov.mono fun k hk => hk.symm)
    have hustar0 : 0 ≤ ustar := div_nonneg hw.1 (by linarith)
    have L1 : Tendsto (fun k => ‖charFun (ν : Measure ℝ) (1 / B (q (ψ k)))‖ ^ q (ψ k))
        atTop (𝓝 (G 1)) := by
      have ht := tendsto_norm_charFun_pow_moving h (hq.comp hψtop)
        (s := fun _ : ℕ => (1 : ℝ)) (t := 1) tendsto_const_nhds
      simpa [G, c₀] using ht
    have L2 : Tendsto
        (fun k => (‖charFun (ν : Measure ℝ) (u (ψ k) / B (m (ψ k)))‖ ^ m (ψ k)) ^
          ((q (ψ k) : ℝ) / m (ψ k))) atTop (𝓝 (G ustar ^ c⁻¹)) := by
      have ht := (tendsto_norm_charFun_pow_moving h (hmtop.comp hψtop)
        (s := fun k => u (ψ k)) (t := ustar) hustar_t).rpow hratio
        (Or.inl (Real.exp_pos _).ne')
      simpa [G, c₀] using ht
    have heq : G 1 = G ustar ^ c⁻¹ :=
      tendsto_nhds_unique L1 (L2.congr' ((hψtop.eventually E1).mono fun k hk => hk.symm))
    have hval : ustar = c ^ (1 / θ) := by
      simp only [G, abs_one, Real.one_rpow, mul_one, ← Real.exp_mul] at heq
      have h1 : c₀ = c₀ * |ustar| ^ θ * c⁻¹ := Real.exp_injective heq
      have h2 : |ustar| ^ θ * c⁻¹ = 1 := by
        have hz : c₀ * (|ustar| ^ θ * c⁻¹ - 1) = 0 := by linarith
        rcases mul_eq_zero.1 hz with hz | hz
        · exact absurd hz hc₀neg.ne
        · linarith
      rw [abs_of_nonneg hustar0] at h2
      have h3 : ustar ^ θ = c := by
        have hmul := congrArg (fun x : ℝ => x * c) h2
        simpa [mul_assoc, inv_mul_cancel₀ hc.ne'] using hmul
      calc
        ustar = (ustar ^ θ) ^ (1 / θ) := by
          rw [← Real.rpow_mul hustar0, mul_one_div_cancel hθ0.ne', Real.rpow_one]
        _ = c ^ (1 / θ) := by rw [h3]
    refine ⟨φ, ?_⟩
    rw [← hval]
    exact hustar_t
  · exfalso
    have hinv : Tendsto (fun k => 1 / u (ψ k)) atTop (𝓝 0) := by
      have ht : Tendsto (fun k => (1 - v (φ k)) / v (φ k)) atTop
          (𝓝 ((1 - w) / w)) :=
        (tendsto_const_nhds.sub hvφ).div hvφ (by rw [hw1]; norm_num)
      rw [hw1, sub_self, zero_div] at ht
      refine ht.congr' ?_
      filter_upwards [hrecov, huψpos] with k hk hkpos
      rw [hk]
      have hv1 : v (φ k) ≠ 1 := by
        intro h1
        rw [h1, sub_self, div_zero] at hk
        linarith
      have hv0 : v (φ k) ≠ 0 := by
        intro h0
        rw [h0, zero_div] at hk
        linarith
      have hden : 1 - v (φ k) ≠ 0 := sub_ne_zero.2 (Ne.symm hv1)
      field_simp
    have L1 : Tendsto (fun k => ‖charFun (ν : Measure ℝ) (1 / B (m (ψ k)))‖ ^ m (ψ k))
        atTop (𝓝 (G 1)) := by
      have ht := tendsto_norm_charFun_pow_moving h (hmtop.comp hψtop)
        (s := fun _ : ℕ => (1 : ℝ)) (t := 1) tendsto_const_nhds
      simpa [G, c₀] using ht
    have hratio' : Tendsto (fun k => (m (ψ k) : ℝ) / q (ψ k)) atTop (𝓝 c) :=
      hmq.comp hψtop
    have L2 : Tendsto
        (fun k => (‖charFun (ν : Measure ℝ) ((1 / u (ψ k)) / B (q (ψ k)))‖ ^ q (ψ k)) ^
          ((m (ψ k) : ℝ) / q (ψ k))) atTop (𝓝 (G 0 ^ c)) := by
      have ht := (tendsto_norm_charFun_pow_moving h (hq.comp hψtop)
        (s := fun k => 1 / u (ψ k)) (t := 0) hinv).rpow hratio'
        (Or.inl (Real.exp_pos _).ne')
      simpa [G, c₀] using ht
    have heq : G 1 = G 0 ^ c :=
      tendsto_nhds_unique L1 (L2.congr' ((hψtop.eventually E2).mono fun k hk => hk.symm))
    have hG0 : G 0 = 1 := by simp [G, Real.zero_rpow hθ0.ne']
    rw [hG0, Real.one_rpow] at heq
    linarith

/-! ### Bridge from the integer predicate -/

/-- The cast pushforward of an integer step law to `ℝ`. -/
noncomputable def castLaw (ν : Measure ℤ) [IsProbabilityMeasure ν] : ProbabilityMeasure ℝ :=
  ⟨ν.map (fun z : ℤ => (z : ℝ)), inferInstance⟩

private theorem map_intWalk_cast_succ (ν : Measure ℤ) (n : ℕ) :
    ((Attraction.intWalk ν (n + 1)).map (fun z : ℤ => (z : ℝ))) =
      ((Attraction.intWalk ν n).map (fun z : ℤ => (z : ℝ))) ∗
        (ν.map (fun z : ℤ => (z : ℝ))) := by
  simpa only [Attraction.intWalk, Int.coe_castAddHom] using
    (Measure.map_conv_addMonoidHom (Int.castAddHom ℝ) (by fun_prop) :
      ((Attraction.intWalk ν n ∗ ν).map (fun z : ℤ => (z : ℝ))) =
        ((Attraction.intWalk ν n).map (fun z : ℤ => (z : ℝ))) ∗
          (ν.map (fun z : ℤ => (z : ℝ))))

/-- The real sum law of cast integer steps is the cast of the integer walk law. -/
theorem sumLaw_castLaw (ν : Measure ℤ) [IsProbabilityMeasure ν] (n : ℕ) :
    (sumLaw (castLaw ν) n : Measure ℝ) =
      (Attraction.intWalk ν n).map (fun z : ℤ => (z : ℝ)) := by
  induction n with
  | zero =>
      rw [sumLaw_zero]
      simp [Attraction.intWalk]
  | succ n ih =>
      rw [sumLaw_succ, map_intWalk_cast_succ, ih]
      change Measure.map (fun z : ℤ => (z : ℝ)) (Attraction.intWalk ν n) ∗
          (ν.map (fun z : ℤ => (z : ℝ))) =
        Measure.map (fun z : ℤ => (z : ℝ)) (Attraction.intWalk ν n) ∗
          (ν.map (fun z : ℤ => (z : ℝ)))
      rfl

/-- (b) The existing integer attraction predicate (`Attraction/Defs.lean`, centering `0`)
implies the real one for the cast step law, with the same normalizer; uses
`eq_stableLaw_of_laplace` to identify the limit. -/
theorem Attraction.IsStableAttracted.isRealStableAttracted {ν : Measure ℤ}
    [IsProbabilityMeasure ν] {θ : ℝ} {B : ℕ → ℝ}
    (h : Attraction.IsStableAttracted ν θ 0 B) :
    IsRealStableAttracted (castLaw ν) θ B := by
  obtain ⟨X, hX, hL, hconv⟩ := h.converges
  have hXeq : X = (stableLaw θ : Measure ℝ) :=
    eq_stableLaw_of_laplace h.alpha_mem hL
  have hpos : ∀ᶠ n in atTop, 0 < B n := by
    obtain ⟨N, hN⟩ := h.pos
    exact (eventually_ge_atTop N).mono hN
  refine ⟨h.alpha_mem, hpos, ?_⟩
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro f
  have hconv' : Tendsto
      (fun n => ∫ x, f x ∂(scaledSumLaw (castLaw ν) B n : Measure ℝ)) atTop
      (𝓝 (∫ x, f x ∂X)) := by
    refine (hconv f).congr' ?_
    filter_upwards [] with n
    have hmap : (scaledSumLaw (castLaw ν) B n : Measure ℝ) =
        (Attraction.intWalk ν n).map (fun z : ℤ => (z : ℝ) / B n) := by
      change Measure.map (fun x : ℝ => x / B n) (sumLaw (castLaw ν) n : Measure ℝ) = _
      rw [sumLaw_castLaw]
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    rw [hmap]
    have hfun : (fun z : ℤ => ((z : ℝ) - (n : ℝ) * 0) / B n) =
        (fun z : ℤ => (z : ℝ) / B n) := by
      funext z
      simp
    rw [hfun]
  simpa [hXeq] using hconv'

/-- The real offspring step law `K - 1`, as a cast of `stepLaw μ`. -/
noncomputable def realOffspringStepLaw (μ : PMF ℕ) : ProbabilityMeasure ℝ :=
  castLaw (stepLaw μ)

/-- (c) Offspring bridge, through `stableDomain_isStableAttracted` and (b). -/
theorem StableDomain.isRealStableAttracted {μ : PMF ℕ} {θ : ℝ} {a : ℕ → ℝ}
    (h : StableDomain μ θ a) :
    IsRealStableAttracted (realOffspringStepLaw μ) θ a := by
  exact Attraction.IsStableAttracted.isRealStableAttracted
    (Attraction.stableDomain_isStableAttracted h)

end BGW.StableTrees
