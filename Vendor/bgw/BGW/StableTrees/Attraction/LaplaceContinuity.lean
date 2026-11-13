/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.TransformConvergence
public import BGW.StableTrees.Attraction.Defs
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric

/-!
# Laplace continuity with existence for centered laws

If probability laws `P n` on `ℝ` have mean zero (and integrable identity) and
`E_{P n} exp(-λ x) → exp(λ ^ θ)` for every `λ > 0`, then `P n` converges weakly to a probability
law `Q` with `E_Q exp(-λ x) = exp(λ ^ θ)`.

* Tightness: the identity `|x| ≤ x + 2 exp(-x)` together with mean zero bounds the first absolute
  moment by `2 E exp(-x)`, which is bounded along the sequence.
* Prokhorov (`isCompact_closure_of_isTightMeasureSet`) gives convergent subsequences. In any
  weakly convergent subsequence the Laplace transform passes to the limit: truncate
  `exp(-s x)` at height `R`, control the truncation error by `E exp(-2 s x) / R`, then use
  Fatou/monotone convergence in `R`.
* The Laplace transform determines the law (`Scalar.limitLaw_unique`), so every subsequential limit
  is the same and the whole sequence converges.

`isStableAttracted_of_laplace_limit` specializes to the centered scaled integer walk, using the
Laplace identity of `centeredScaledWalk`.
Ported from `BGWLeaves/StableAnalysis/LaplaceContinuity.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.LaplaceContinuity

open BGW.StableTrees.Attraction
open BGW.StableTrees.Attraction.TransformConvergence
open BGW.StableTrees.Scalar

/-! ### Passing the Laplace transform to a weak limit -/

/-- The bounded continuous truncation of `exp(-s x)` at height `k + 1`. -/
private noncomputable def truncExp (s : ℝ) (k : ℕ) : BoundedContinuousFunction ℝ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup
    (fun x : ℝ => min (Real.exp (-s * x)) ((k : ℝ) + 1))
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).min continuous_const)
    ((k : ℝ) + 1) (fun x => by
      rw [Real.norm_of_nonneg (le_min (Real.exp_nonneg _) (by positivity))]
      exact min_le_right _ _)

private theorem truncExp_apply (s : ℝ) (k : ℕ) (x : ℝ) :
    truncExp s k x = min (Real.exp (-s * x)) ((k : ℝ) + 1) := rfl

private theorem truncExp_nonneg (s : ℝ) (k : ℕ) (x : ℝ) : 0 ≤ truncExp s k x := by
  rw [truncExp_apply]
  exact le_min (Real.exp_nonneg _) (by positivity)

private theorem exp_sub_trunc_le (s : ℝ) (k : ℕ) (x : ℝ) :
    Real.exp (-s * x) - truncExp s k x ≤ Real.exp (-(2 * s) * x) / ((k : ℝ) + 1) := by
  have hR : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hF2 : Real.exp (-(2 * s) * x) = Real.exp (-s * x) ^ 2 := by
    have := Real.exp_nat_mul (-s * x) 2
    push_cast at this
    rw [show -(2 * s) * x = 2 * (-s * x) by ring, this]
  rw [hF2, truncExp_apply, le_div_iff₀ hR]
  set F := Real.exp (-s * x)
  set R := (k : ℝ) + 1
  rcases le_total F R with h | h
  · rw [min_eq_left h]
    simp only [sub_self, zero_mul]
    positivity
  · rw [min_eq_right h]
    nlinarith [sq_nonneg (F - R / 2), sq_nonneg R]

/-- Weak limits of laws with convergent Laplace transforms inherit the limiting Laplace transform
(the transforms are integrable under the limit). -/
theorem laplace_eq_of_tendsto {θ : ℝ} {P : ℕ → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hPQ : Tendsto P atTop (𝓝 Q))
    (hL : ∀ s : ℝ, 0 < s →
      Tendsto (fun n => ∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)) atTop
        (𝓝 (Real.exp (s ^ θ))))
    {s : ℝ} (hs : 0 < s) :
    Integrable (fun x : ℝ => Real.exp (-s * x)) (Q : Measure ℝ) ∧
      ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) = Real.exp (s ^ θ) := by
  have hint : ∀ t : ℝ, 0 < t →
      ∀ᶠ n in atTop, Integrable (fun x : ℝ => Real.exp (-t * x)) (P n : Measure ℝ) := by
    intro t ht
    filter_upwards [(hL t ht).eventually_ne (Real.exp_pos _).ne'] with n hn
    by_contra h
    exact hn (integral_undef h)
  set E := Real.exp (s ^ θ) with hE
  set D := Real.exp ((2 * s) ^ θ) + 1 with hD
  have hD2 : ∀ᶠ n in atTop,
      ∫ x, Real.exp (-(2 * s) * x) ∂(P n : Measure ℝ) ≤ D :=
    ((hL (2 * s) (by positivity)).eventually
      (gt_mem_nhds (by simp [hD] : Real.exp ((2 * s) ^ θ) < D))).mono fun n hn => hn.le
  have hconv : ∀ k : ℕ, Tendsto (fun n => ∫ x, truncExp s k x ∂(P n : Measure ℝ)) atTop
      (𝓝 (∫ x, truncExp s k x ∂(Q : Measure ℝ))) :=
    fun k => ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hPQ (truncExp s k)
  have hgint : ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (k : ℕ), Integrable (truncExp s k) μ :=
    fun μ _ k => (truncExp s k).integrable μ
  have hup : ∀ k : ℕ, ∫ x, truncExp s k x ∂(Q : Measure ℝ) ≤ E := by
    intro k
    refine le_of_tendsto_of_tendsto (hconv k) (hL s hs) ?_
    filter_upwards [hint s hs] with n hn
    exact integral_mono (hgint _ k) hn (fun x => min_le_left _ _)
  have hlow : ∀ k : ℕ, E - D / ((k : ℝ) + 1) ≤ ∫ x, truncExp s k x ∂(Q : Measure ℝ) := by
    intro k
    refine le_of_tendsto_of_tendsto ((hL s hs).sub_const _) (hconv k) ?_
    filter_upwards [hint s hs, hint (2 * s) (by positivity), hD2] with n h1 h2 h3
    have hmono := integral_mono (h1.sub (hgint _ k)) (h2.div_const _) (exp_sub_trunc_le s k)
    simp only [Pi.sub_apply] at hmono
    rw [integral_sub h1 (hgint _ k), integral_div] at hmono
    have h4 : (∫ x, Real.exp (-(2 * s) * x) ∂(P n : Measure ℝ)) / ((k : ℝ) + 1) ≤
        D / ((k : ℝ) + 1) := div_le_div_of_nonneg_right h3 (by positivity)
    linarith
  have hFint : Integrable (fun x : ℝ => Real.exp (-s * x)) (Q : Measure ℝ) := by
    refine integrable_of_tendsto (G := fun k x => truncExp s k x) ?_ ?_ ?_
    · refine Eventually.of_forall fun x => ?_
      obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp (-s * x))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with k hk
      have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
      rw [truncExp_apply, min_eq_left (by linarith)]
    · exact fun k => (truncExp s k).continuous.aestronglyMeasurable
    · refine ne_top_of_le_ne_top (ENNReal.ofReal_ne_top (r := E)) ?_
      refine liminf_le_of_frequently_le' (Frequently.of_forall fun k => ?_)
      rw [← ofReal_integral_norm_eq_lintegral_enorm (hgint _ k)]
      apply ENNReal.ofReal_le_ofReal
      have : ∫ x, ‖truncExp s k x‖ ∂(Q : Measure ℝ) = ∫ x, truncExp s k x ∂(Q : Measure ℝ) :=
        integral_congr_ae (Eventually.of_forall fun x =>
          Real.norm_of_nonneg (truncExp_nonneg s k x))
      rw [this]
      exact hup k
  have hmt := integral_tendsto_of_tendsto_of_monotone (μ := (Q : Measure ℝ))
    (f := fun k x => truncExp s k x) (F := fun x => Real.exp (-s * x))
    (fun k => hgint _ k) hFint
    (Eventually.of_forall fun x k l hkl => by
      simp only [truncExp_apply]
      refine min_le_min le_rfl ?_
      have : (k : ℝ) ≤ l := by exact_mod_cast hkl
      linarith)
    (Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp (-s * x))
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop N] with k hk
      have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
      rw [truncExp_apply, min_eq_left (by linarith)])
  have hlim0 : Tendsto (fun k : ℕ => D / ((k : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
  have hsq : Tendsto (fun k : ℕ => ∫ x, truncExp s k x ∂(Q : Measure ℝ)) atTop (𝓝 E) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le ?_ tendsto_const_nhds hlow hup
    simpa using (tendsto_const_nhds (x := E)).sub hlim0
  exact ⟨hFint, tendsto_nhds_unique hmt hsq⟩

/-! ### Tightness from a uniform first-moment bound -/

private theorem isTight_of_moment {S : Set (ProbabilityMeasure ℝ)} (M : ℝ)
    (hint : ∀ P ∈ S, Integrable (fun x : ℝ => |x|) (P : Measure ℝ))
    (hM : ∀ P ∈ S, ∫ x, |x| ∂(P : Measure ℝ) ≤ M) :
    IsTightMeasureSet {((P : ProbabilityMeasure ℝ) : Measure ℝ) | P ∈ S} := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  by_cases hεt : ε = ⊤
  · exact ⟨∅, isCompact_empty, fun μ _ => by simp [hεt]⟩
  have hεpos : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' hεt
  set R : ℝ := (|M| + 1) / ε.toReal with hR
  have hRpos : 0 < R := by positivity
  refine ⟨Metric.closedBall 0 R, isCompact_closedBall 0 R, ?_⟩
  rintro μ ⟨P, hP, rfl⟩
  have hmk := mul_meas_ge_le_integral_of_nonneg (μ := (P : Measure ℝ))
    (f := fun x : ℝ => |x|) (Eventually.of_forall fun x => abs_nonneg x) (hint P hP) R
  have hsub : (Metric.closedBall (0 : ℝ) R)ᶜ ⊆ {x : ℝ | R ≤ |x|} := by
    intro x hx
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs,
      not_le] at hx
    exact hx.le
  have hreal : (P : Measure ℝ).real (Metric.closedBall (0 : ℝ) R)ᶜ ≤ ε.toReal := by
    have h1 := measureReal_mono hsub (measure_ne_top (P : Measure ℝ) _)
    have h2 : R * (P : Measure ℝ).real {x : ℝ | R ≤ |x|} ≤ M := hmk.trans (hM P hP)
    have h3 : R * (P : Measure ℝ).real (Metric.closedBall (0 : ℝ) R)ᶜ ≤ M :=
      le_trans (mul_le_mul_of_nonneg_left h1 hRpos.le) h2
    have h4 : (P : Measure ℝ).real (Metric.closedBall (0 : ℝ) R)ᶜ * R ≤ M := by linarith
    have h5 : (P : Measure ℝ).real (Metric.closedBall (0 : ℝ) R)ᶜ ≤ M / R :=
      (le_div_iff₀ hRpos).2 h4
    refine h5.trans ?_
    rw [div_le_iff₀ hRpos, hR, mul_div_assoc', le_div_iff₀ hεpos]
    nlinarith [le_abs_self M, hεpos]
  calc (P : Measure ℝ) (Metric.closedBall (0 : ℝ) R)ᶜ
      = ENNReal.ofReal ((P : Measure ℝ).real (Metric.closedBall (0 : ℝ) R)ᶜ) :=
        (ofReal_measureReal (measure_ne_top _ _)).symm
    _ ≤ ENNReal.ofReal ε.toReal := ENNReal.ofReal_le_ofReal hreal
    _ = ε := ENNReal.ofReal_toReal hεt

/-! ### Abstract Laplace continuity -/

private theorem exists_tendsto_of_laplace_tendsto_aux {θ : ℝ} (hθ : 0 < θ)
    (P : ℕ → ProbabilityMeasure ℝ)
    (hint : ∀ n, Integrable (fun x : ℝ => x) (P n : Measure ℝ))
    (hmean : ∀ n, ∫ x, x ∂(P n : Measure ℝ) = 0)
    (hexp : ∀ n, Integrable (fun x : ℝ => Real.exp (-x)) (P n : Measure ℝ))
    (hL : ∀ s : ℝ, 0 < s →
      Tendsto (fun n => ∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)) atTop
        (𝓝 (Real.exp (s ^ θ)))) :
    ∃ Q : ProbabilityMeasure ℝ,
      (∀ s : ℝ, 0 < s → ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) = Real.exp (s ^ θ)) ∧
      Tendsto P atTop (𝓝 Q) := by
  -- first moment bound
  have h1 : (fun x : ℝ => Real.exp (-1 * x)) = fun x : ℝ => Real.exp (-x) := by
    funext x; simp
  obtain ⟨C, hC⟩ := (h1 ▸ hL 1 one_pos : Tendsto (fun n => ∫ x, Real.exp (-x) ∂(P n : Measure ℝ))
    atTop _).bddAbove_range
  have hCn : ∀ n, ∫ x, Real.exp (-x) ∂(P n : Measure ℝ) ≤ C := fun n => hC ⟨n, rfl⟩
  have habs : ∀ n, ∫ x, |x| ∂(P n : Measure ℝ) ≤ 2 * C := by
    intro n
    have hpt : ∀ x : ℝ, |x| ≤ x + 2 * Real.exp (-x) := by
      intro x
      have := Real.add_one_le_exp (-x)
      rcases le_total 0 x with h | h
      · rw [abs_of_nonneg h]; linarith [Real.exp_pos (-x)]
      · rw [abs_of_nonpos h]; linarith
    have hle := integral_mono (hint n).abs ((hint n).add ((hexp n).const_mul 2)) hpt
    simp only [Pi.add_apply] at hle
    rw [integral_add (hint n) ((hexp n).const_mul 2), integral_const_mul, hmean n] at hle
    linarith [hCn n]
  have htight : IsTightMeasureSet
      {((P' : ProbabilityMeasure ℝ) : Measure ℝ) | P' ∈ Set.range P} :=
    isTight_of_moment (2 * C) (by rintro _ ⟨n, rfl⟩; exact (hint n).abs)
      (by rintro _ ⟨n, rfl⟩; exact habs n)
  have hK : IsCompact (closure (Set.range P)) := isCompact_closure_of_isTightMeasureSet htight
  have hmem : ∀ n, P n ∈ closure (Set.range P) := fun n => subset_closure ⟨n, rfl⟩
  -- Laplace identification along any convergent subsequence
  have hsub : ∀ (φ : ℕ → ℕ) (Q : ProbabilityMeasure ℝ), Tendsto φ atTop atTop →
      Tendsto (fun n => P (φ n)) atTop (𝓝 Q) →
      ∀ s : ℝ, 0 < s → ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) = Real.exp (s ^ θ) :=
    fun φ Q hφ hQ s hs =>
      (laplace_eq_of_tendsto (P := fun n => P (φ n)) hQ
        (fun s hs => (hL s hs).comp hφ) hs).2
  obtain ⟨Q, -, φ, hφ, hlim⟩ := hK.tendsto_subseq hmem
  have hQL := hsub φ Q hφ.tendsto_atTop hlim
  refine ⟨Q, hQL, tendsto_of_subseq_tendsto fun ns hns => ?_⟩
  obtain ⟨Q', -, ψ, hψ, hlim'⟩ := hK.tendsto_subseq (x := fun n => P (ns n))
    (fun n => hmem _)
  have hQ'L := hsub (ns ∘ ψ) Q' (hns.comp hψ.tendsto_atTop) hlim'
  have hQQ : (Q' : Measure ℝ) = (Q : Measure ℝ) :=
    limitLaw_unique hθ hQ'L hQL
  have : Q' = Q := ProbabilityMeasure.toMeasure_injective hQQ
  exact ⟨ψ, this ▸ hlim'⟩

/-- **Centered Laplace continuity with existence.** Let `P n` be probability laws on `ℝ` which are
eventually integrable with mean zero and satisfy `E_{P n} exp(-s x) → exp(s ^ θ)` for every
`s > 0`. Then `P n` converges weakly to a probability law `Q` with Laplace transform
`E_Q exp(-s x) = exp(s ^ θ)`. Finite negative exponential moments of `P n` (eventually) are
automatic from the convergence of the Laplace transforms. -/
theorem exists_tendsto_of_laplace_tendsto {θ : ℝ} (hθ : 0 < θ)
    (P : ℕ → ProbabilityMeasure ℝ)
    (hint : ∀ᶠ n in atTop, Integrable (fun x : ℝ => x) (P n : Measure ℝ))
    (hmean : ∀ᶠ n in atTop, ∫ x, x ∂(P n : Measure ℝ) = 0)
    (hL : ∀ s : ℝ, 0 < s →
      Tendsto (fun n => ∫ x, Real.exp (-s * x) ∂(P n : Measure ℝ)) atTop
        (𝓝 (Real.exp (s ^ θ)))) :
    ∃ Q : ProbabilityMeasure ℝ,
      (∀ s : ℝ, 0 < s → ∫ x, Real.exp (-s * x) ∂(Q : Measure ℝ) = Real.exp (s ^ θ)) ∧
      Tendsto P atTop (𝓝 Q) := by
  have hexp : ∀ᶠ n in atTop, Integrable (fun x : ℝ => Real.exp (-x)) (P n : Measure ℝ) := by
    have h1 : (fun x : ℝ => Real.exp (-1 * x)) = fun x : ℝ => Real.exp (-x) := by
      funext x; simp
    filter_upwards [(hL 1 one_pos).eventually_ne (Real.exp_pos _).ne'] with n hn
    rw [← h1]
    by_contra h
    exact hn (integral_undef h)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hint.and (hmean.and hexp))
  obtain ⟨Q, hQ, hlim⟩ := exists_tendsto_of_laplace_tendsto_aux hθ (fun k => P (k + N))
    (fun k => (hN (k + N) (by omega)).1) (fun k => (hN (k + N) (by omega)).2.1)
    (fun k => (hN (k + N) (by omega)).2.2)
    (fun s hs => (hL s hs).comp (tendsto_add_atTop_nat N))
  exact ⟨Q, hQ, (tendsto_add_atTop_iff_nat N).1 hlim⟩

/-! ### The centered scaled integer walk -/

private theorem cast_integrable_conv {μ ν : Measure ℤ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν]
    (hμ : Integrable (fun z : ℤ => (z : ℝ)) μ)
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) :
    Integrable (fun z : ℤ => (z : ℝ)) (μ ∗ ν) := by
  rw [Measure.conv]
  apply (integrable_map_measure (measurable_of_countable _).aestronglyMeasurable
    (measurable_of_countable _).aemeasurable).2
  have hprod : Integrable (fun p : ℤ × ℤ => ((p.1 + p.2 : ℤ) : ℝ)) (μ.prod ν) := by
    convert (hμ.comp_fst ν).add (hν.comp_snd μ) using 1
    ext p
    simp
  exact hprod

private instance intWalk_isProbabilityMeasure' (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (n : ℕ) : IsProbabilityMeasure (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using
      (inferInstance : IsProbabilityMeasure ((intWalk ν n) ∗ ν))

private theorem intWalk_integrable_cast' (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) (n : ℕ) :
    Integrable (fun z : ℤ => (z : ℝ)) (intWalk ν n) := by
  induction n with
  | zero => simpa [intWalk] using (integrable_dirac (a := 0) (by simp) :
      Integrable (fun z : ℤ => (z : ℝ)) (Measure.dirac 0))
  | succ n ih => simpa only [intWalk] using cast_integrable_conv ih hν

/-- The identity is integrable under the centered scaled walk. -/
theorem centeredScaledWalk_integrable_id (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) (m a : ℝ) (n : ℕ) :
    Integrable (fun x : ℝ => x) (centeredScaledWalk ν m a n) := by
  rw [centeredScaledWalk_eq_map]
  apply (integrable_map_measure aestronglyMeasurable_id
    (measurable_of_countable _).aemeasurable).2
  exact (((intWalk_integrable_cast' ν hν n).sub (integrable_const ((n : ℝ) * m))).div_const a)

/-- **Attraction from the Laplace limit.** Let `ν` be a step law on `ℤ` with `ν {z < -1} = 0` and
finite mean, and `b` eventually positive with
`stepLaplace ν (λ / b n) ^ n * exp (λ n mean ν / b n) → exp (λ ^ θ)` for every `λ > 0` (this is
the Laplace transform of `centeredScaledWalk ν (mean ν) (b n) n`). Then `ν` is attracted to the
spectrally positive stable law with this centering and norming `b`. -/
theorem isStableAttracted_of_laplace_limit (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hstep : ν {z : ℤ | z < -1} = 0)
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) {b : ℕ → ℝ}
    (hb : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < b n)
    (hL : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun n : ℕ => stepLaplace ν (lam / b n) ^ n *
        Real.exp (lam * n * mean ν / b n)) atTop (𝓝 (Real.exp (lam ^ θ)))) :
    IsStableAttracted ν θ (mean ν) b := by
  obtain ⟨N, hN⟩ := hb
  have hev : ∀ᶠ n in atTop, 0 < b n := eventually_atTop.2 ⟨N, hN⟩
  have hL' : ∀ s : ℝ, 0 < s →
      Tendsto (fun n => ∫ x, Real.exp (-s * x)
        ∂(centeredScaledWalkProb ν (mean ν) b n : Measure ℝ)) atTop
        (𝓝 (Real.exp (s ^ θ))) := by
    intro s hs
    refine (hL s hs).congr' ?_
    filter_upwards [hev] with n hn
    exact (centeredScaledWalk_laplace ν hstep (mean ν) (b n) s n hn hs.le).symm
  obtain ⟨Q, hQ, hlim⟩ := exists_tendsto_of_laplace_tendsto (by linarith [hθ.1])
    (centeredScaledWalkProb ν (mean ν) b)
    (Eventually.of_forall fun n => centeredScaledWalk_integrable_id ν hν (mean ν) (b n) n)
    (Eventually.of_forall fun n =>
      centeredScaledWalk_integral_eq_zero ν hν (mean ν) (b n) n rfl) hL'
  refine ⟨hθ, ⟨N, hN⟩, (Q : Measure ℝ), inferInstance, hQ, fun f => ?_⟩
  have := ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hlim f
  simpa [centeredScaledWalkProb, centeredScaledWalk_eq_map] using this

/-- The same, with the centered one-step Laplace transform
`ℓ(s) = stepLaplace ν s * exp (s * mean ν)` raised to the power `n`. -/
theorem isStableAttracted_of_centered_laplace_limit (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hstep : ν {z : ℤ | z < -1} = 0)
    (hν : Integrable (fun z : ℤ => (z : ℝ)) ν) {b : ℕ → ℝ}
    (hb : ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 0 < b n)
    (hL : ∀ lam : ℝ, 0 < lam →
      Tendsto (fun n : ℕ => (stepLaplace ν (lam / b n) *
        Real.exp ((lam / b n) * mean ν)) ^ n) atTop (𝓝 (Real.exp (lam ^ θ)))) :
    IsStableAttracted ν θ (mean ν) b := by
  refine isStableAttracted_of_laplace_limit ν hθ hstep hν hb fun lam hlam => (hL lam hlam).congr
    fun n => ?_
  rw [mul_pow, ← Real.exp_nat_mul]
  congr 2
  ring

end BGW.StableTrees.Attraction.LaplaceContinuity
