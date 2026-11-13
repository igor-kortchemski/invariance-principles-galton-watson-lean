/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.Defs
public import BGW.StableTrees.Attraction.SlowVariation
public import BGW.StableTrees.Attraction.CanonicalAttraction
public import BGW.StableTrees.Attraction.DomainCriterion
public import BGW.StableTrees.Attraction.QuantileAnalysis
public import BGW.StableTrees.Attraction.TransformConvergence


/-!
# Canonical norming

Ported from `BGWLeaves/StableAnalysis/Norming.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/
@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace BGW.StableTrees.Attraction.Norming

open BGW.StableTrees

/-!
# Canonical norming and Theorem 1.10(i)--(ii)

The domain criterion selects the tail, infinite-variance Gaussian, or finite-variance
Gaussian branch. Canonical attraction and convergence of types identify the norming.
Monotonicity and sequence regular variation give the slowly varying real floor
extension. The earlier finite-variance helpers are retained below.
-/

private theorem norming_monotone_of_integrable_sq {ν : Measure ℤ}
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) (θ : ℝ) :
    Monotone (norming ν θ) := by
  intro m n hmn
  simp only [norming_of_integrable_sq hfin]
  exact mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (div_le_div_of_nonneg_right (by exact_mod_cast hmn) (by norm_num)))
    (Real.sqrt_nonneg _)

/-- Identification in the critical finite-variance setting covered by BGW.
Both sequences are compared with the same Gaussian CLT scale. -/
private theorem norming_isEquivalent_stableDomain_finiteVariance
    {μ : PMF ℕ} {θ : ℝ} {b : ℕ → ℝ} (hb : StableDomain μ θ b)
    (hfin : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    Tendsto (fun n => norming (stepLaw μ) θ n / b n) atTop (𝓝 1) := by
  have hθ := Scalar.alpha_eq_two_of_finiteVariance hb hfin
  subst θ
  have ha := stableDomain_norming_finiteVariance hb.critical hb.nondegenerate hfin
  let σ := Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ)
  have hσ : 0 < σ := Real.sqrt_pos.2
    (Scalar.step_secondMoment_pos hb.critical hb.nondegenerate hfin)
  have hσsq : σ ^ 2 = ∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ :=
    Real.sq_sqrt (integral_nonneg fun z => sq_nonneg (z : ℝ))
  let q : ℝ := ((-1 / 2 : ℝ) / Real.cos (Real.pi * 2 / 2)) ^ (1 / (2 : ℝ))
  have hq : 0 < q := Real.rpow_pos_of_pos
    (div_pos_of_neg_of_neg (by norm_num)
      (Scalar.cos_pi_mul_div_two_neg (by norm_num : (1 : ℝ) < 2 ∧ (2 : ℝ) ≤ 2))) _
  have ht := (Scalar.finiteVariance_norming_ratio ha hfin hσ hσsq).div
    (Scalar.finiteVariance_norming_ratio hb hfin hσ hσsq) hq.ne'
  change Tendsto (fun n =>
    (norming (stepLaw μ) 2 n / (σ * Real.sqrt n)) /
      (b n / (σ * Real.sqrt n))) atTop (𝓝 (q / q)) at ht
  rw [div_self hq.ne'] at ht
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hd : σ * Real.sqrt n ≠ 0 :=
    (mul_pos hσ (Real.sqrt_pos.2 (by exact_mod_cast hn))).ne'
  exact div_div_div_cancel_right₀ hd _ _

private theorem norming_isEquivalent_attracted_finiteVariance
    {μ : PMF ℕ} {θ : ℝ} {b : ℕ → ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hmono : Monotone b)
    (hb : IsStableAttracted (stepLaw μ) θ 0 b)
    (hfin : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    Tendsto (fun n => norming (stepLaw μ) θ n / b n) atTop (𝓝 1) := by
  obtain ⟨b', heq, hb'⟩ := hb.exists_stableDomain hc hne hmono
  apply (norming_isEquivalent_stableDomain_finiteVariance hb' hfin).congr'
  filter_upwards [heq] with n hn
  rw [hn]

private theorem locallimit_i_finiteVariance
    {μ : PMF ℕ} {θ : ℝ} {b : ℕ → ℝ} (hb : StableDomain μ θ b)
    (hfin : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) (norming (stepLaw μ) θ) := by
  have hθ := Scalar.alpha_eq_two_of_finiteVariance hb hfin
  subst θ
  rw [mean_stepLaw hb.critical]
  exact stableDomain_isStableAttracted
    (stableDomain_norming_finiteVariance hb.critical hb.nondegenerate hfin)

private theorem locallimit_ii_finiteVariance
    {μ : PMF ℕ} {θ : ℝ} {b : ℕ → ℝ} (hb : StableDomain μ θ b)
    (hfin : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) :
    Monotone (norming (stepLaw μ) θ) ∧
      SlowlyVarying (fun x : ℝ => norming (stepLaw μ) θ ⌊x⌋₊ / x ^ (1 / θ)) := by
  have hθ := Scalar.alpha_eq_two_of_finiteVariance hb hfin
  subst θ
  have ha := stableDomain_norming_finiteVariance hb.critical hb.nondegenerate hfin
  exact ⟨ha.monotone, Scalar.slowlyVarying ha⟩

private theorem canonical_attraction_of_attracted
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ : ℝ} {b : ℕ → ℝ}
    (hstep : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hb : IsStableAttracted ν θ (mean ν) b) :
    IsStableAttracted ν θ (mean ν) (norming ν θ) := by
  by_cases hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν
  · have hθ := DomainCriterion.index_eq_two_of_integrable_sq hb hint hsq
    subst θ
    exact CanonicalAttraction.isStableAttracted_of_finiteVariance hint hsq
      (DomainCriterion.variance_pos_of_integrable_sq hb hint hsq)
  · by_cases hθ : θ < 2
    · exact CanonicalAttraction.isStableAttracted_of_regVary_tail hstep hint
        hb.alpha_mem.1 hθ (DomainCriterion.rightTail_regularlyVarying hb hstep hint hsq hθ)
    · have hθeq : θ = 2 := le_antisymm hb.alpha_mem.2 (not_lt.1 hθ)
      subst θ
      obtain ⟨hK, hKinf⟩ := DomainCriterion.truncSecondMoment_slowlyVarying_unbounded hb hint hsq
      exact CanonicalAttraction.isStableAttracted_of_slowlyVarying_moment hstep hint hK hKinf

/-- The monotone floor-extension argument from `Scalar.slowlyVarying`, adapted to
an arbitrary centered attracting integer law with eventual positive scales. -/
private theorem slowlyVarying_floor_of_attracted
    {ν : Measure ℤ} [IsProbabilityMeasure ν] {θ m : ℝ} {a : ℕ → ℝ}
    (hmono : Monotone a) (h : IsStableAttracted ν θ m a) :
    SlowlyVarying (fun x : ℝ => a ⌊x⌋₊ / x ^ (1 / θ)) := by
  intro c hc
  let ρ : ℝ := 1 / θ
  have hrv := TransformConvergence.regularlyVaryingSeq ν h
  have f1 : Tendsto (fun n : ℕ => a ⌊c * n⌋₊ / a n) atTop (𝓝 (c ^ ρ)) := hrv c hc
  have f2 : Tendsto (fun n : ℕ => a ⌊c * (n + 1 : ℕ)⌋₊ / a n) atTop (𝓝 (c ^ ρ)) := by
    apply TransformConvergence.tendsto_div_of_tendsto_div' ν h h hc
    have g1 := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hc.le).comp tendsto_natCast_atTop_atTop
    have g2 : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
      have ht : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 (1 + 0)) :=
        tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
      rw [add_zero] at ht
      apply ht.congr'
      filter_upwards [eventually_ne_atTop 0] with n hn
      push_cast
      field_simp
    have g3 := (g1.comp (tendsto_add_atTop_nat 1)).mul g2
    rw [mul_one] at g3
    apply g3.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    simp only [Function.comp_def]
    have : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have hfl := tendsto_nat_floor_atTop (α := ℝ)
  have hpos : ∀ᶠ n in atTop, 0 < a n := eventually_atTop.2 h.pos
  have hratio : Tendsto (fun x : ℝ => a ⌊c * x⌋₊ / a ⌊x⌋₊) atTop (𝓝 (c ^ ρ)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (f1.comp hfl) (f2.comp hfl)
    · filter_upwards [eventually_ge_atTop (1 : ℝ), hfl.eventually hpos] with x hx hax
      simp only [Function.comp_def]
      apply div_le_div_of_nonneg_right _ hax.le
      apply hmono
      apply Nat.floor_le_floor
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (by linarith)) hc.le
    · filter_upwards [eventually_ge_atTop (1 : ℝ), hfl.eventually hpos] with x hx hax
      simp only [Function.comp_def]
      apply div_le_div_of_nonneg_right _ hax.le
      apply hmono
      apply Nat.floor_le_floor
      apply mul_le_mul_of_nonneg_left _ hc.le
      push_cast
      exact (Nat.lt_floor_add_one x).le
  have hfin := hratio.mul_const (c ^ (-ρ))
  rw [← Real.rpow_add hc, add_neg_cancel, Real.rpow_zero] at hfin
  apply hfin.congr'
  filter_upwards [eventually_ge_atTop (1 : ℝ), hfl.eventually hpos] with x hx hax
  have hx0 : 0 < x := by linarith
  have ha := hax.ne'
  rw [Real.mul_rpow hc.le hx0.le, Real.rpow_neg hc.le]
  have h1 : 0 < c ^ ρ := Real.rpow_pos_of_pos hc _
  have h2 : 0 < x ^ ρ := Real.rpow_pos_of_pos hx0 _
  field_simp
  rfl

section LocalLimit

variable (ν : Measure ℤ) [IsProbabilityMeasure ν] {θ : ℝ}

/-- Theorem 1.10(i), with the corrected canonical norming. -/
theorem locallimit_i (hstep : ν {z | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) :
    IsStableAttracted ν θ (mean ν) (norming ν θ) := by
  obtain ⟨b, hb⟩ := hDA
  exact canonical_attraction_of_attracted hstep hint hb

/-- The corrected canonical norming is equivalent to every attracting norming. -/
theorem norming_isEquivalent (hstep : ν {z | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {b : ℕ → ℝ}
    (hb : IsStableAttracted ν θ (mean ν) b) :
    Tendsto (fun n => norming ν θ n / b n) atTop (𝓝 1) :=
  TransformConvergence.norming_ratio_tendsto_one ν
    (canonical_attraction_of_attracted hstep hint hb) hb

/-- Theorem 1.10(ii): monotonicity and a slowly varying real floor extension. -/
theorem locallimit_ii (hstep : ν {z | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hDA : ∃ b, IsStableAttracted ν θ (mean ν) b) :
    Monotone (norming ν θ) ∧
      SlowlyVarying (fun x : ℝ => norming ν θ ⌊x⌋₊ / x ^ (1 / θ)) := by
  have ha := locallimit_i ν hstep hint hDA
  have hmono : Monotone (norming ν θ) := by
    by_cases hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν
    · exact norming_monotone_of_integrable_sq hsq θ
    · exact QuantileAnalysis.norming_monotone_of_infinite_variance hstep hint hsq θ ha.alpha_mem
  exact ⟨hmono, slowlyVarying_floor_of_attracted hmono ha⟩

end LocalLimit

end BGW.StableTrees.Attraction.Norming
