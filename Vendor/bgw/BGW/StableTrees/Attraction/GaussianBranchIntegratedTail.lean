/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.GaussianBranchCore
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Integrated tail of the Gaussian branch

The integrated-tail asymptotic is the B3-b result for the index-two branch.
Ported from `BGWLeaves/StableAnalysis/GaussianBranch.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set intervalIntegral
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.GaussianBranch

open BGW.StableTrees.Attraction BGW.StableTrees.Attraction.MonotoneDensity BGW.StableTrees

/-! ## 5. (B3-b) The integrated tail -/

section B3b

private theorem integrableOn_sq_trunc_local {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun z : ℤ => (z : ℝ) ^ 2) {z : ℤ | |(z : ℝ)| ≤ x} ν := by
  refine IntegrableOn.of_bound ?_ ?_ (x ^ 2) ?_
  · calc
      ν {z : ℤ | |(z : ℝ)| ≤ x} ≤ ν Set.univ := measure_mono (subset_univ _)
      _ < ∞ := by simp
  · exact (measurable_of_countable _).aestronglyMeasurable.restrict
  · filter_upwards [ae_restrict_mem (s := {z : ℤ | |(z : ℝ)| ≤ x})
      MeasurableSet.of_discrete] with z hz
    change |(z : ℝ)| ≤ x at hz
    rw [Real.norm_of_nonneg (sq_nonneg (z : ℝ))]
    have hsq : |(z : ℝ)| ^ 2 ≤ x ^ 2 := (sq_le_sq₀ (abs_nonneg _) hx).2 hz
    simpa [sq_abs] using hsq

private theorem truncSecondMoment_natFloor_local {ν : Measure ℤ}
    {x : ℝ} (hx : 0 ≤ x) :
    truncSecondMoment ν x = truncSecondMoment ν (⌊x⌋₊ : ℝ) := by
  rw [truncSecondMoment_floor]
  congr 1
  rw [← Int.natCast_floor_eq_floor hx]
  simp

private theorem potter_real_local {ν : Measure ℤ} [IsProbabilityMeasure ν]
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ y : ℝ, 1 ≤ y →
      truncSecondMoment ν (y * x) ≤ C * y ^ ε * truncSecondMoment ν x := by
  obtain ⟨C, hC1, N, hN⟩ := SlowVariation.slow_potter_nat (L := truncSecondMoment ν)
    (truncSecondMoment_mono (ν := ν)).measurable (fun x _ => truncSecondMoment_nonneg' x) hK hε
  obtain ⟨N', hN'⟩ := eventually_atTop.1
    ((hKinf.comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 0)
  refine ⟨C * 2 ^ ε, by positivity, ((max N N' + 1 : ℕ) : ℝ), ?_, ?_⟩
  · have : (1 : ℝ) ≤ ((max N N' + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_left 1 _
    exact this
  intro x hx y hy
  set n := ⌊x⌋₊ with hn
  have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx
  have hnge : max N N' + 1 ≤ n := Nat.le_floor hx
  have hnN : N ≤ n := by omega
  have hnN' : N' ≤ n := by omega
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hKn : 0 < truncSecondMoment ν (n : ℝ) := hN' n hnN'
  have hxn : x < n + 1 := Nat.lt_floor_add_one x
  have hKx : truncSecondMoment ν x = truncSecondMoment ν (n : ℝ) :=
    truncSecondMoment_natFloor_local hx0
  have hy0 : 0 ≤ y := by linarith
  have h1 : y * x ≤ (n : ℝ) * (2 * y) := by nlinarith
  have h2 := (hN n hnN (2 * y) (by linarith)).2
  rw [div_le_iff₀ hKn, Real.mul_rpow (by norm_num) hy0] at h2
  calc truncSecondMoment ν (y * x) ≤ truncSecondMoment ν ((n : ℝ) * (2 * y)) :=
        truncSecondMoment_mono h1
    _ ≤ C * (2 ^ ε * y ^ ε) * truncSecondMoment ν (n : ℝ) := h2
    _ = C * 2 ^ ε * y ^ ε * truncSecondMoment ν x := by rw [hKx]; ring

private theorem psi_integral {x : ℝ} (hx : 0 ≤ x) (z : ℝ) :
    ∫ u in (0 : ℝ)..x, max (z - u) 0 =
      if z ≤ 0 then 0 else if z ≤ x then z ^ 2 / 2 else x * z - x ^ 2 / 2 := by
  have hcont : Continuous (fun u : ℝ => max (z - u) 0) :=
    (continuous_const.sub continuous_id).max continuous_const
  have hlin : ∀ a b : ℝ, ∫ u in a..b, (z - u) = z * (b - a) - (b ^ 2 - a ^ 2) / 2 := by
    intro a b
    rw [intervalIntegral.integral_sub (by simp) (by simp)]
    simp [integral_id]
    ring
  split_ifs with h1 h2
  · rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
    · simp
    · intro u hu
      rw [uIcc_of_le hx] at hu
      exact max_eq_right (by linarith [hu.1])
  · have hz : 0 ≤ z := by linarith
    rw [← intervalIntegral.integral_add_adjacent_intervals (b := z)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
    have e1 : ∫ u in (0 : ℝ)..z, max (z - u) 0 = z ^ 2 / 2 := by
      rw [intervalIntegral.integral_congr (g := fun u => z - u), hlin]
      · ring
      · intro u hu
        rw [uIcc_of_le hz] at hu
        exact max_eq_left (by linarith [hu.2])
    have e2 : ∫ u in z..x, max (z - u) 0 = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ))]
      · simp
      · intro u hu
        rw [uIcc_of_le (by linarith)] at hu
        exact max_eq_right (by linarith [hu.1])
    rw [e1, e2, add_zero]
  · push Not at h1 h2
    rw [intervalIntegral.integral_congr (g := fun u => z - u), hlin]
    · ring
    · intro u hu
      rw [uIcc_of_le hx] at hu
      exact max_eq_left (by linarith [hu.2])


variable {ν : Measure ℤ} [IsProbabilityMeasure ν]

omit [IsProbabilityMeasure ν] in
private theorem excess_fubini (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {x : ℝ} (hx : 0 ≤ x) :
    ∫ u in (0 : ℝ)..x, ∫ z, max ((z : ℝ) - u) 0 ∂ν =
      ∫ z, (∫ u in (0 : ℝ)..x, max ((z : ℝ) - u) 0) ∂ν := by
  have hcast : Measurable (fun z : ℤ => (z : ℝ)) := Measurable.of_discrete
  have hfm : Measurable (Function.uncurry (fun (u : ℝ) (z : ℤ) => max ((z : ℝ) - u) 0)) :=
    ((hcast.comp measurable_snd).sub measurable_fst).max measurable_const
  have hfin : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) x)) := by
    rw [uIoc_of_le hx]; infer_instance
  have hg : Integrable (fun p : ℝ × ℤ => |(p.2 : ℝ)|) ((volume.restrict (uIoc (0 : ℝ) x)).prod ν) :=
    (hint.abs.comp_snd (volume.restrict (uIoc (0 : ℝ) x)))
  have hint2 : Integrable (Function.uncurry (fun (u : ℝ) (z : ℤ) => max ((z : ℝ) - u) 0))
      ((volume.restrict (uIoc (0 : ℝ) x)).prod ν) := by
    refine hg.mono' hfm.aestronglyMeasurable ?_
    have hms : MeasurableSet {p : ℝ × ℤ |
        ‖Function.uncurry (fun (u : ℝ) (z : ℤ) => max ((z : ℝ) - u) 0) p‖ ≤ |(p.2 : ℝ)|} :=
      measurableSet_le hfm.norm (continuous_abs.measurable.comp (hcast.comp measurable_snd))
    rw [Measure.ae_prod_iff_ae_ae hms]
    rw [uIoc_of_le hx]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr
      (ae_of_all _ (fun u hu => ae_of_all _ (fun z => ?_)))
    simp only [Function.uncurry]
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (abs_nonneg _)
    linarith [le_abs_self (z : ℝ), hu.1]
  exact intervalIntegral_integral_swap hint2


private theorem excess_decomp (hneg : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {x : ℝ} (hx : 1 ≤ x) :
    ∫ u in (0 : ℝ)..x, ∫ z, max ((z : ℝ) - u) 0 ∂ν =
      truncSecondMoment ν x / 2 - ν.real {(-1 : ℤ)} / 2 +
        ∫ z in {z : ℤ | x < (z : ℝ)}, ((x * (z : ℝ) - x ^ 2 / 2)) ∂ν := by
  have hx0 : 0 ≤ x := by linarith
  rw [excess_fubini hint hx0]
  have hnull : ∀ᵐ z ∂ν, ¬ z < -1 := by
    rw [ae_iff]; simpa using hneg
  set a : ℤ → ℝ := ({z : ℤ | |(z : ℝ)| ≤ x}).indicator (fun z => (z : ℝ) ^ 2) with ha
  set b : ℤ → ℝ := ({z : ℤ | x < (z : ℝ)}).indicator (fun z => x * (z : ℝ) - x ^ 2 / 2) with hb
  set c : ℤ → ℝ := ({(-1 : ℤ)} : Set ℤ).indicator (fun _ => (1 : ℝ)) with hc
  have hpt : ∀ᵐ z : ℤ ∂ν, (∫ u in (0 : ℝ)..x, max ((z : ℝ) - u) 0) = a z / 2 - c z / 2 + b z := by
    filter_upwards [hnull] with z hz
    have hz' : (-1 : ℤ) ≤ z := not_lt.mp hz
    rw [psi_integral hx0]
    obtain rfl | rfl | h1 : z = -1 ∨ z = 0 ∨ 1 ≤ z := by omega
    · simp [ha, hb, hc, Set.indicator_apply, hx]
      intro h; linarith
    · simp [ha, hb, hc, Set.indicator_apply]
      intro h; linarith
    · have hz1 : (1 : ℝ) ≤ z := by exact_mod_cast h1
      have hne : ¬ (z = -1) := by omega
      have hza : |(z : ℝ)| = z := abs_of_nonneg (by linarith)
      have hc0 : ¬ ((z : ℝ) ≤ 0) := by linarith
      simp only [hc0, ↓reduceIte]
      by_cases hzx : (z : ℝ) ≤ x
      · simp only [hzx, ↓reduceIte]
        simp [ha, hb, hc, hza, hzx, not_lt.mpr hzx, hne]
      · simp only [hzx, ↓reduceIte]
        push Not at hzx
        simp [ha, hb, hc, hza, hzx, not_le.mpr hzx, hne]
  have hbd : ∀ z : ℤ, ‖a z‖ ≤ x ^ 2 := by
    intro z
    simp only [ha, Set.indicator_apply, Set.mem_ofPred_eq]
    split_ifs with h
    · rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      nlinarith [abs_nonneg (z : ℝ), sq_abs (z : ℝ)]
    · simp; positivity
  have hia : Integrable a ν :=
    Integrable.of_bound (Measurable.of_discrete).aestronglyMeasurable (x ^ 2) (ae_of_all _ hbd)
  have hib : Integrable b ν :=
    ((hint.const_mul x).sub (integrable_const (x ^ 2 / 2))).indicator MeasurableSet.of_discrete
  have hic : Integrable c ν := (integrable_const _).indicator MeasurableSet.of_discrete
  have hi1 : Integrable (fun z => a z / 2 - c z / 2) ν := (hia.div_const 2).sub (hic.div_const 2)
  have hi2 : Integrable (fun z => a z / 2) ν := hia.div_const 2
  have hi3 : Integrable (fun z => c z / 2) ν := hic.div_const 2
  rw [integral_congr_ae hpt, integral_add hi1 hib, integral_sub hi2 hi3,
    MeasureTheory.integral_div, MeasureTheory.integral_div]
  have e1 : ∫ z, a z ∂ν = truncSecondMoment ν x := by
    rw [ha, MeasureTheory.integral_indicator MeasurableSet.of_discrete]; rfl
  have e2 : ∫ z, b z ∂ν = ∫ z in {z : ℤ | x < (z : ℝ)}, (x * (z : ℝ) - x ^ 2 / 2) ∂ν := by
    rw [hb, MeasureTheory.integral_indicator MeasurableSet.of_discrete]
  have e3 : ∫ z, c z ∂ν = ν.real {(-1 : ℤ)} := by
    rw [hc, integral_indicator_const _ MeasurableSet.of_discrete, smul_eq_mul, mul_one]
  rw [e1, e2, e3]


/-- `∫_{z > x} z dν`. -/
private noncomputable def meanAbove (ν : Measure ℤ) (x : ℝ) : ℝ :=
  ∫ z in {z : ℤ | x < (z : ℝ)}, (z : ℝ) ∂ν

omit [IsProbabilityMeasure ν] in
private theorem meanAbove_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ meanAbove ν x := by
  unfold meanAbove
  refine setIntegral_nonneg MeasurableSet.of_discrete (fun z hz => ?_)
  have : x < (z : ℝ) := hz
  linarith

/-- One dyadic step: `x · E[Z; Z > x] ≤ K(2x) - K(x) + x · E[Z; Z > 2x]` for `x ≥ 1`. -/
private theorem meanAbove_step (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {x : ℝ} (hx : 1 ≤ x) :
    x * meanAbove ν x ≤ truncSecondMoment ν (2 * x) - truncSecondMoment ν x +
      x * meanAbove ν (2 * x) := by
  have hx0 : 0 < x := by linarith
  set A : Set ℤ := {z : ℤ | x < (z : ℝ) ∧ (z : ℝ) ≤ 2 * x} with hA
  set B : Set ℤ := {z : ℤ | 2 * x < (z : ℝ)} with hB
  set S1 : Set ℤ := {z : ℤ | |(z : ℝ)| ≤ x} with hS1
  set S2 : Set ℤ := {z : ℤ | |(z : ℝ)| ≤ 2 * x} with hS2
  have hsplit : {z : ℤ | x < (z : ℝ)} = A ∪ B := by
    ext z
    simp only [hA, hB, Set.mem_union, Set.mem_ofPred_eq]
    constructor
    · intro h
      rcases le_or_gt (z : ℝ) (2 * x) with h2 | h2
      · exact Or.inl ⟨h, h2⟩
      · exact Or.inr h2
    · rintro (h | h)
      · exact h.1
      · linarith
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    have h1 : (z : ℝ) ≤ 2 * x := hzA.2
    have h2 : 2 * x < (z : ℝ) := hzB
    linarith
  have hAS2 : A ⊆ S2 := by
    intro z hz
    have h1 : x < (z : ℝ) := hz.1
    have h2 : (z : ℝ) ≤ 2 * x := hz.2
    show |(z : ℝ)| ≤ 2 * x
    rw [abs_of_pos (by linarith)]; exact h2
  have hdisj2 : Disjoint S1 A := by
    rw [Set.disjoint_left]
    intro z hz1 hzA
    have h1 : |(z : ℝ)| ≤ x := hz1
    have h2 : x < (z : ℝ) := hzA.1
    linarith [le_abs_self (z : ℝ)]
  have hS1S2 : S1 ⊆ S2 := fun z hz => le_trans (show |(z : ℝ)| ≤ x from hz) (by linarith)
  have hint1 : IntegrableOn (fun z : ℤ => (z : ℝ) ^ 2) S1 ν :=
    integrableOn_sq_trunc_local hx0.le
  have hint2 : IntegrableOn (fun z : ℤ => (z : ℝ) ^ 2) S2 ν :=
    integrableOn_sq_trunc_local (by linarith)
  have hintA : IntegrableOn (fun z : ℤ => (z : ℝ) ^ 2) A ν := hint2.mono_set hAS2
  -- the mass on `A`
  have hmassA : x * ∫ z in A, (z : ℝ) ∂ν ≤ truncSecondMoment ν (2 * x) - truncSecondMoment ν x := by
    have h1 : x * ∫ z in A, (z : ℝ) ∂ν ≤ ∫ z in A, (z : ℝ) ^ 2 ∂ν := by
      rw [← MeasureTheory.integral_const_mul]
      refine setIntegral_mono_on ((hint.const_mul x).integrableOn) hintA MeasurableSet.of_discrete
        (fun z hz => ?_)
      have h1 : x < (z : ℝ) := hz.1
      nlinarith
    have h2 : (∫ z in S1, (z : ℝ) ^ 2 ∂ν) + ∫ z in A, (z : ℝ) ^ 2 ∂ν ≤
        ∫ z in S2, (z : ℝ) ^ 2 ∂ν := by
      rw [← setIntegral_union hdisj2 MeasurableSet.of_discrete hint1 hintA]
      exact setIntegral_mono_set hint2 (ae_of_all _ fun z => sq_nonneg (z : ℝ))
        (ae_of_all _ (Set.union_subset hS1S2 hAS2))
    have e1 : truncSecondMoment ν x = ∫ z in S1, (z : ℝ) ^ 2 ∂ν := rfl
    have e2 : truncSecondMoment ν (2 * x) = ∫ z in S2, (z : ℝ) ^ 2 ∂ν := rfl
    linarith
  unfold meanAbove
  rw [hsplit, setIntegral_union hdisj MeasurableSet.of_discrete hint.integrableOn hint.integrableOn,
    mul_add]
  have : {z : ℤ | 2 * x < (z : ℝ)} = B := rfl
  rw [this]
  linarith


private theorem meanAbove_iter (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) (k : ℕ) :
    ∀ x : ℝ, 1 ≤ x → x * meanAbove ν x ≤
      ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j *
        (truncSecondMoment ν (2 ^ (j + 1) * x) - truncSecondMoment ν (2 ^ j * x)) +
      x * meanAbove ν (2 ^ k * x) := by
  induction k with
  | zero => intro x hx; simp
  | succ k ih =>
    intro x hx
    have h1 := meanAbove_step hint hx
    have h2 := ih (2 * x) (by linarith)
    simp only [show ∀ j : ℕ, (2 : ℝ) ^ (j + 1) * (2 * x) = 2 ^ (j + 1 + 1) * x from
      fun j => by ring, show ∀ j : ℕ, (2 : ℝ) ^ j * (2 * x) = 2 ^ (j + 1) * x from
      fun j => by ring] at h2
    rw [Finset.sum_range_succ']
    have e : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ (j + 1) *
        (truncSecondMoment ν (2 ^ (j + 1 + 1) * x) - truncSecondMoment ν (2 ^ (j + 1) * x)) =
        (1 / 2) * ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j *
          (truncSecondMoment ν (2 ^ (j + 1 + 1) * x) - truncSecondMoment ν (2 ^ (j + 1) * x)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [pow_succ]; ring
    rw [e]
    simp only [pow_zero, zero_add, pow_one, one_mul]
    linarith

omit [IsProbabilityMeasure ν] in
private theorem meanAbove_tendsto_zero (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {y : ℝ}
    (hy : 0 < y) : Tendsto (fun k : ℕ => meanAbove ν (2 ^ k * y)) atTop (𝓝 0) := by
  have hF : ∀ k : ℕ, meanAbove ν (2 ^ k * y) =
      ∫ z, ({z : ℤ | 2 ^ k * y < (z : ℝ)}).indicator (fun z : ℤ => (z : ℝ)) z ∂ν := by
    intro k
    unfold meanAbove
    rw [MeasureTheory.integral_indicator MeasurableSet.of_discrete]
  simp_rw [hF]
  have h := tendsto_integral_of_dominated_convergence (μ := ν)
    (F := fun (k : ℕ) (z : ℤ) => ({z : ℤ | 2 ^ k * y < (z : ℝ)}).indicator (fun z : ℤ => (z : ℝ)) z)
    (f := fun _ => (0 : ℝ)) (bound := fun z : ℤ => |(z : ℝ)|)
    (fun k => (measurable_of_countable _).aestronglyMeasurable) hint.abs
    (fun k => ae_of_all _ fun z => by
      by_cases hz : z ∈ {z : ℤ | 2 ^ k * y < (z : ℝ)}
      · rw [Set.indicator_of_mem hz]; simp
      · rw [Set.indicator_of_notMem hz]; simp)
    (ae_of_all _ fun z => by
      have hlim : Tendsto (fun k : ℕ => (2 : ℝ) ^ k * y) atTop atTop :=
        (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 2)).atTop_mul_const hy
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [hlim.eventually_ge_atTop (z : ℝ)] with k hk
      rw [Set.indicator_of_notMem (by simpa using hk)])
  simpa using h

private theorem potter_dyadic (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    ∃ C : ℝ, 0 < C ∧ ∃ X : ℝ, 1 ≤ X ∧ ∀ x : ℝ, X ≤ x → ∀ j : ℕ,
      truncSecondMoment ν (2 ^ j * x) ≤ C * (3 / 2 : ℝ) ^ j * truncSecondMoment ν x := by
  obtain ⟨C, hC, X, hX1, hX⟩ := potter_real_local hK hKinf (ε := 1 / 2) (by norm_num)
  refine ⟨C, hC, X, hX1, fun x hx j => ?_⟩
  have h := hX x hx (2 ^ j) (one_le_pow₀ (by norm_num))
  refine h.trans ?_
  have hs : ((2 : ℝ) ^ j) ^ (1 / 2 : ℝ) ≤ (3 / 2) ^ j := by
    rw [← Real.sqrt_eq_rpow]
    refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
    rw [← pow_mul, mul_comm, pow_mul]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) j
  have hK0 := truncSecondMoment_nonneg' (ν := ν) x
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hC.le) hK0


private theorem geom_three_quarters (k : ℕ) : ∑ j ∈ Finset.range k, (3 / 4 : ℝ) ^ j ≤ 4 := by
  rw [geom_sum_eq (by norm_num : (3 / 4 : ℝ) ≠ 1) k]
  have h : (0 : ℝ) ≤ (3 / 4) ^ k := by positivity
  rw [div_le_iff_of_neg (by norm_num)]
  linarith

/-- A priori bound `y E[Z; Z > y] ≤ C₁ K(y)` for `K` slowly varying. -/
private theorem meanAbove_apriori (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    ∃ C₁ : ℝ, ∃ X₁ : ℝ, 1 ≤ X₁ ∧ ∀ y : ℝ, X₁ ≤ y →
      y * meanAbove ν y ≤ C₁ * truncSecondMoment ν y := by
  obtain ⟨C, hC, X, hX1, hX⟩ := potter_dyadic hK hKinf
  refine ⟨6 * C, X, hX1, fun y hy => ?_⟩
  have hy1 : 1 ≤ y := hX1.trans hy
  have hy0 : 0 < y := by linarith
  have hK0 := truncSecondMoment_nonneg' (ν := ν) y
  have hbound : ∀ k : ℕ, y * meanAbove ν y ≤ 6 * C * truncSecondMoment ν y +
      y * meanAbove ν (2 ^ k * y) := by
    intro k
    refine (meanAbove_iter hint k y hy1).trans ?_
    have hsum : ∑ j ∈ Finset.range k, (1 / 2 : ℝ) ^ j *
        (truncSecondMoment ν (2 ^ (j + 1) * y) - truncSecondMoment ν (2 ^ j * y)) ≤
        ∑ j ∈ Finset.range k, (3 * C / 2 * truncSecondMoment ν y) * (3 / 4 : ℝ) ^ j := by
      refine Finset.sum_le_sum (fun j _ => ?_)
      have h1 := hX y hy (j + 1)
      have h2 := truncSecondMoment_nonneg' (ν := ν) (2 ^ j * y)
      have h3 : (1 / 2 : ℝ) ^ j * ((3 / 2 : ℝ) ^ (j + 1)) = 3 / 2 * (3 / 4 : ℝ) ^ j := by
        rw [pow_succ, show (3 / 4 : ℝ) = 1 / 2 * (3 / 2) by norm_num, mul_pow]; ring
      calc (1 / 2 : ℝ) ^ j *
          (truncSecondMoment ν (2 ^ (j + 1) * y) - truncSecondMoment ν (2 ^ j * y))
          ≤ (1 / 2 : ℝ) ^ j * (C * (3 / 2 : ℝ) ^ (j + 1) * truncSecondMoment ν y) :=
            mul_le_mul_of_nonneg_left (by linarith) (by positivity)
        _ = (3 * C / 2 * truncSecondMoment ν y) * (3 / 4 : ℝ) ^ j := by
            rw [← mul_assoc, mul_comm ((1 / 2 : ℝ) ^ j), mul_assoc C, ← mul_assoc C]
            calc _ = C * ((1 / 2 : ℝ) ^ j * (3 / 2 : ℝ) ^ (j + 1)) *
                truncSecondMoment ν y := by ring
              _ = _ := by rw [h3]; ring
    rw [← Finset.mul_sum] at hsum
    have := geom_three_quarters k
    have h4 : 3 * C / 2 * truncSecondMoment ν y * ∑ j ∈ Finset.range k, (3 / 4 : ℝ) ^ j ≤
        3 * C / 2 * truncSecondMoment ν y * 4 :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  have hlim : Tendsto (fun k : ℕ => 6 * C * truncSecondMoment ν y + y * meanAbove ν (2 ^ k * y))
      atTop (𝓝 (6 * C * truncSecondMoment ν y + y * 0)) :=
    tendsto_const_nhds.add ((meanAbove_tendsto_zero hint hy0).const_mul y)
  rw [mul_zero, add_zero] at hlim
  exact ge_of_tendsto' hlim hbound

/-- `x E[Z; Z > x] = o(K(x))` if `K` is slowly varying and unbounded (`ν` of finite mean). -/
private theorem meanAbove_isLittleO (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun x : ℝ => x * meanAbove ν x / truncSecondMoment ν x) atTop (𝓝 0) := by
  obtain ⟨C, hC, X, hX1, hX⟩ := potter_dyadic hK hKinf
  obtain ⟨C₁, X₁, hX₁1, hX₁⟩ := meanAbove_apriori hint hK hKinf
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- choose `J`
  have hC1 : 0 ≤ |C₁| * C := by positivity
  obtain ⟨J, hJ⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 3 / 4)
    (by norm_num : (3 / 4 : ℝ) < 1)).const_mul (|C₁| * C)).eventually
    (gt_mem_nhds (show (|C₁| * C) * 0 < ε / 2 by simpa using half_pos hε)) |>.exists
  have hJ' : |C₁| * C * (3 / 4 : ℝ) ^ J < ε / 2 := hJ
  have hS : Tendsto (fun x : ℝ => ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j *
      (truncSecondMoment ν (2 ^ (j + 1) * x) / truncSecondMoment ν x -
        truncSecondMoment ν (2 ^ j * x) / truncSecondMoment ν x)) atTop (𝓝 0) := by
    have := tendsto_finsetSum (Finset.range J) (fun j _ =>
      (((hK (2 ^ (j + 1)) (by positivity)).sub (hK (2 ^ j) (by positivity))).const_mul
        ((1 / 2 : ℝ) ^ j)))
    simpa using this
  filter_upwards [hS.eventually (gt_mem_nhds (half_pos hε)), eventually_ge_atTop (max X X₁),
    hKinf.eventually_gt_atTop 0] with x hSx hx hKx
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hxX₁ : X₁ ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ x := hX1.trans hxX
  have hR0 : 0 ≤ x * meanAbove ν x := mul_nonneg (by linarith) (meanAbove_nonneg (by linarith))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg hR0 hKx.le), div_lt_iff₀ hKx]
  have hit := meanAbove_iter hint J x hx1
  -- the remainder term
  set y := 2 ^ J * x with hy
  have hxy : x ≤ y := by
    have : (1 : ℝ) ≤ 2 ^ J := one_le_pow₀ (by norm_num)
    nlinarith
  have hrem : x * meanAbove ν y ≤ |C₁| * C * (3 / 4 : ℝ) ^ J * truncSecondMoment ν x := by
    have h1 := hX₁ y (hxX₁.trans hxy)
    have h2' : (1 / 2 : ℝ) ^ J * y = x := by
      rw [hy, ← mul_assoc, ← mul_pow]; norm_num
    have h2 : x * meanAbove ν y = (1 / 2 : ℝ) ^ J * (y * meanAbove ν y) := by
      rw [← mul_assoc, h2']
    have h3 := hX x hxX J
    have hy0 : 0 ≤ truncSecondMoment ν y := truncSecondMoment_nonneg' _
    have h4 : (1 / 2 : ℝ) ^ J * (3 / 2 : ℝ) ^ J = (3 / 4 : ℝ) ^ J := by
      rw [← mul_pow]; norm_num
    rw [h2]
    calc (1 / 2 : ℝ) ^ J * (y * meanAbove ν y)
        ≤ (1 / 2 : ℝ) ^ J * (C₁ * truncSecondMoment ν y) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ J * (|C₁| * truncSecondMoment ν y) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (le_abs_self _) hy0) (by positivity)
      _ ≤ (1 / 2 : ℝ) ^ J * (|C₁| * (C * (3 / 2 : ℝ) ^ J * truncSecondMoment ν x)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (by rw [hy]; exact h3)
            (abs_nonneg _)) (by positivity)
      _ = |C₁| * C * ((1 / 2 : ℝ) ^ J * (3 / 2 : ℝ) ^ J) * truncSecondMoment ν x := by ring
      _ = _ := by rw [h4]
  have hsumeq : ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j *
      (truncSecondMoment ν (2 ^ (j + 1) * x) - truncSecondMoment ν (2 ^ j * x)) =
      truncSecondMoment ν x * ∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j *
      (truncSecondMoment ν (2 ^ (j + 1) * x) / truncSecondMoment ν x -
        truncSecondMoment ν (2 ^ j * x) / truncSecondMoment ν x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    field_simp
  rw [hsumeq] at hit
  have hfin : x * meanAbove ν x ≤ truncSecondMoment ν x * (∑ j ∈ Finset.range J, (1 / 2 : ℝ) ^ j *
      (truncSecondMoment ν (2 ^ (j + 1) * x) / truncSecondMoment ν x -
        truncSecondMoment ν (2 ^ j * x) / truncSecondMoment ν x)) +
      |C₁| * C * (3 / 4 : ℝ) ^ J * truncSecondMoment ν x := by linarith
  nlinarith


/-- **(B3-b)** Let `ν` be a probability law on `ℤ` with `ν {z < -1} = 0` and finite mean, such that
`K = truncSecondMoment ν` is slowly varying and unbounded.  Then the integrated tail
`J(x) = ∫₀ˣ E[(Z - u)⁺] du` (`E[(Z-u)⁺] = ∫_u^∞ ν{z > v} dv`, see
`integral_max_sub_eq_integral_tail`) satisfies `J(x) / (K(x)/2) → 1`.

Use: for the Laplace transform `ℓ(s) = E e^{-s Z}` one has the exact identity
`ℓ(s) - 1 + m s = s² ∫₀^∞ e^{-su} E[(Z-u)⁺] du + (explicit atom at -1)`, so (via the
Laplace–Karamata Abelian theorem applied to `U = J`) `ℓ(s) - 1 + m s ~ s² J(1/s) ~ s² K(1/s) / 2`
as `s → 0+`. -/
theorem integratedTail_div_tendsto (hneg : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Tendsto (fun x : ℝ => (∫ u in (0 : ℝ)..x, ∫ z, max ((z : ℝ) - u) 0 ∂ν) /
      (truncSecondMoment ν x / 2)) atTop (𝓝 1) := by
  set D : ℝ → ℝ := fun x => ∫ z in {z : ℤ | x < (z : ℝ)}, ((x * (z : ℝ) - x ^ 2 / 2)) ∂ν with hD
  have hD0 : ∀ x : ℝ, 1 ≤ x → 0 ≤ D x := by
    intro x hx
    refine setIntegral_nonneg MeasurableSet.of_discrete (fun z hz => ?_)
    have : x < (z : ℝ) := hz
    nlinarith
  have hDR : ∀ x : ℝ, 1 ≤ x → D x ≤ x * meanAbove ν x := by
    intro x hx
    unfold meanAbove
    rw [← MeasureTheory.integral_const_mul]
    refine setIntegral_mono_on
      (((hint.const_mul x).sub (integrable_const (x ^ 2 / 2))).integrableOn)
      ((hint.const_mul x).integrableOn) MeasurableSet.of_discrete (fun z hz => ?_)
    have : x ^ 2 / 2 ≥ 0 := by positivity
    linarith
  have hDK : Tendsto (fun x : ℝ => D x / truncSecondMoment ν x) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (meanAbove_isLittleO hint hK hKinf) ?_ ?_
    · filter_upwards [eventually_ge_atTop (1 : ℝ), hKinf.eventually_gt_atTop 0] with x hx hKx
      exact div_nonneg (hD0 x hx) hKx.le
    · filter_upwards [eventually_ge_atTop (1 : ℝ), hKinf.eventually_gt_atTop 0] with x hx hKx
      exact div_le_div_of_nonneg_right (hDR x hx) hKx.le
  have hlim : Tendsto (fun x : ℝ => 1 - ν.real {(-1 : ℤ)} / truncSecondMoment ν x +
      2 * (D x / truncSecondMoment ν x)) atTop (𝓝 (1 - 0 + 2 * 0)) :=
    (tendsto_const_nhds.sub (tendsto_const_nhds.div_atTop hKinf)).add (hDK.const_mul 2)
  rw [sub_zero, mul_zero, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ), hKinf.eventually_gt_atTop 0] with x hx hKx
  rw [excess_decomp hneg hint hx]
  have := hKx.ne'
  simp only [hD]
  field_simp

theorem integratedTail_isEquivalent (hneg : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hK : SlowlyVarying (truncSecondMoment ν))
    (hKinf : Tendsto (truncSecondMoment ν) atTop atTop) :
    Asymptotics.IsEquivalent atTop
      (fun x : ℝ => ∫ u in (0 : ℝ)..x, ∫ z, max ((z : ℝ) - u) 0 ∂ν)
      (fun x : ℝ => truncSecondMoment ν x / 2) :=
  Asymptotics.isEquivalent_of_tendsto_one (integratedTail_div_tendsto hneg hint hK hKinf)

/-- The excess `E[(Z-u)⁺]` equals the integrated tail `∫_u^∞ ν{z > v} dv`. -/
theorem integral_max_sub_eq_integral_tail (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) (u : ℝ) :
    ∫ z, max ((z : ℝ) - u) 0 ∂ν = ∫ v in Ioi u, ν.real {z : ℤ | v < (z : ℝ)} := by
  have hf : Integrable (fun z : ℤ => max ((z : ℝ) - u) 0) ν := by
    refine Integrable.mono' (g := fun z : ℤ => |(z : ℝ)| + |u|)
      (hint.abs.add (integrable_const |u|))
      (measurable_of_countable _).aestronglyMeasurable (ae_of_all _ fun z => ?_)
    show ‖max ((z : ℝ) - u) 0‖ ≤ |(z : ℝ)| + |u|
    rw [Real.norm_of_nonneg (le_max_right _ _)]
    refine max_le ?_ (by positivity)
    linarith [abs_nonneg (z : ℝ), abs_nonneg u, neg_abs_le u, le_abs_self (z : ℝ)]
  rw [Integrable.integral_eq_integral_meas_lt hf (ae_of_all _ fun z => le_max_right _ _)]
  have h1 : ∫ t in Ioi (0 : ℝ), ν.real {z : ℤ | t < max ((z : ℝ) - u) 0} =
      ∫ t in Ioi (0 : ℝ), ν.real {z : ℤ | u + t < (z : ℝ)} := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    have ht' : 0 < t := ht
    congr 2
    ext z
    simp only [lt_max_iff]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h; left; linarith
  rw [h1]
  set g : ℝ → ℝ := fun v => ν.real {z : ℤ | v < (z : ℝ)} with hg
  have h2 : ∫ t in Ioi (0 : ℝ), g (u + t) = ∫ v in Ioi u, g v := by
    rw [← MeasureTheory.integral_indicator measurableSet_Ioi,
      ← MeasureTheory.integral_indicator measurableSet_Ioi]
    rw [← integral_add_left_eq_self (μ := volume) ((Ioi u).indicator g) u]
    refine integral_congr_ae (ae_of_all _ fun t => ?_)
    show _ = (Ioi u).indicator g (u + t)
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
        Set.indicator_of_mem (show u + t ∈ Ioi u by simp [ht])]
    · rw [Set.indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
        Set.indicator_of_notMem (show u + t ∉ Ioi u by simp [not_lt.1 ht])]
  exact h2

end B3b

end BGW.StableTrees.Attraction.GaussianBranch
