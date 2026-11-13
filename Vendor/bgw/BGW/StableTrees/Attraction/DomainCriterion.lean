/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.GaussianSmoothing
public import BGW.StableTrees.Attraction.KaramataTransforms
public import BGW.StableTrees.Attraction.MonotoneDensity
public import BGW.StableTrees.Attraction.GaussianBranch

/-!
# Consequences of the Gaussian-smoothed converse

For infinite second moment, Fubini identifies `H(s)/s` as the Laplace transform
of the squared-difference tail density. Karamata and monotone density recover
regular variation of its integrated tail. A uniform capped-moment comparison
transfers this to the original step; a second application of monotone density
recovers its squared tail, or the truncated moment at the Gaussian boundary.

The finite second moment case is obtained directly by dominated convergence,
without a Tauberian theorem or a calculation of the smoothing constant.

Main exports: `rightTail_regularlyVarying`,
`truncSecondMoment_slowlyVarying_unbounded`, `index_eq_two_of_integrable_sq`,
and `smoothing_isEquivalent_variance`.
Ported from `BGWLeaves/StableAnalysis/DomainCriterion.lean` of the author's arXiv:1110.2163v4
formalization (local snapshot of 6 November 2026).
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology ENNReal

namespace BGW.StableTrees.Attraction.DomainCriterion

open GaussianSmoothing

/-- The elementary bound used to dominate the smoothing difference quotient. -/
theorem smoothing_quotient_bounds {s x : ℝ} (hs : 0 < s) :
    0 ≤ (1 - Real.exp (-s * x ^ 2)) / s ∧
      (1 - Real.exp (-s * x ^ 2)) / s ≤ x ^ 2 := by
  have he := Real.exp_le_one_iff.mpr
    (mul_nonpos_of_nonpos_of_nonneg (by linarith : -s ≤ 0) (sq_nonneg x))
  have hl := Real.add_one_le_exp (-s * x ^ 2)
  constructor
  · exact div_nonneg (by linarith) hs.le
  · rw [div_le_iff₀ hs]
    nlinarith

private theorem smoothing_quotient_pointwise (x : ℝ) :
    Tendsto (fun s : ℝ => (1 - Real.exp (-s * x ^ 2)) / s) (𝓝[>] 0)
      (𝓝 (x ^ 2)) := by
  have hd : HasDerivAt (fun s : ℝ => 1 - Real.exp (-s * x ^ 2)) (x ^ 2) 0 := by
    convert (((hasDerivAt_id 0).neg.mul_const (x ^ 2)).exp).const_sub 1 using 1 <;> simp
  have h := hasDerivAt_iff_tendsto_slope.mp hd
  simp only [slope_fun_def_field, Real.exp_zero, zero_mul, neg_zero, sub_self, sub_zero] at h
  exact h.mono_left (nhdsWithin_mono _ fun s hs => ne_of_gt hs)

/-- If the symmetrized law has a finite second moment, `H(s)/s` tends to it. -/
theorem smoothing_div_tendsto_secondMoment (ν : Measure ℤ)
    (hD : Integrable (fun x : ℝ => x ^ 2) (symmetrizedLaw ν)) :
    Tendsto (fun s : ℝ => smoothing ν s / s) (𝓝[>] 0)
      (𝓝 (∫ x : ℝ, x ^ 2 ∂(symmetrizedLaw ν))) := by
  have h := tendsto_integral_filter_of_dominated_convergence
    (μ := symmetrizedLaw ν)
    (F := fun s x : ℝ => (1 - Real.exp (-s * x ^ 2)) / s)
    (fun x : ℝ => x ^ 2)
    (Eventually.of_forall fun s => by fun_prop)
    (by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact ae_of_all _ fun x => by
        rw [Real.norm_of_nonneg (smoothing_quotient_bounds hs).1]
        exact (smoothing_quotient_bounds hs).2)
    hD (ae_of_all _ smoothing_quotient_pointwise)
  simpa only [integral_div, smoothing] using h

private theorem integrable_difference_sq (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Integrable (fun p : ℤ × ℤ => ((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) (ν.prod ν) := by
  have h := ((hsq.comp_fst ν).add (hsq.comp_snd ν)).sub
    ((hint.mul_prod hint).const_mul 2)
  convert h using 1
  funext p
  simp only [Pi.sub_apply, Pi.add_apply]
  ring

/-- Finite second moment is preserved by independent symmetrization. -/
theorem integrable_sq_symmetrizedLaw (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Integrable (fun x : ℝ => x ^ 2) (symmetrizedLaw ν) := by
  rw [symmetrizedLaw_eq_map]
  exact (integrable_map_measure (by fun_prop) (by fun_prop)).2
    (integrable_difference_sq ν hint hsq)

/-- The independent difference has second moment twice the original variance. -/
theorem secondMoment_symmetrizedLaw (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    (∫ x : ℝ, x ^ 2 ∂(symmetrizedLaw ν)) = 2 * variance ν := by
  have hvar : variance ν = (∫ z : ℤ, (z : ℝ) ^ 2 ∂ν) - mean ν ^ 2 := by
    unfold variance
    have heq : (fun z : ℤ => ((z : ℝ) - mean ν) ^ 2) =
        fun z : ℤ => (z : ℝ) ^ 2 - 2 * mean ν * (z : ℝ) + mean ν ^ 2 := by
      funext z; ring
    rw [heq,
      integral_add (f := fun z : ℤ => (z : ℝ) ^ 2 - 2 * mean ν * (z : ℝ))
        (hsq.sub (hint.const_mul _)) (integrable_const _),
      integral_sub hsq (hint.const_mul _), integral_const_mul]
    simp [mean]
    ring
  rw [symmetrizedLaw_eq_map, integral_map (by fun_prop) (by fun_prop)]
  have heq : (fun p : ℤ × ℤ => ((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) =
      fun p => (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 - 2 * ((p.1 : ℝ) * (p.2 : ℝ)) := by
    funext p; ring
  change (∫ p : ℤ × ℤ, ((p.1 : ℝ) - (p.2 : ℝ)) ^ 2 ∂(ν.prod ν)) = _
  rw [heq,
    integral_sub (f := fun p : ℤ × ℤ => (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)
      ((hsq.comp_fst ν).add (hsq.comp_snd ν))
      ((hint.mul_prod hint).const_mul 2),
    integral_add (hsq.comp_fst ν) (hsq.comp_snd ν),
    integral_const_mul,
    integral_prod_mul]
  rw [integral_prod _ (hsq.comp_fst ν), integral_prod _ (hsq.comp_snd ν)]
  simp only [integral_const, probReal_univ, one_smul]
  rw [hvar]
  change _ = 2 * ((∫ z : ℤ, (z : ℝ) ^ 2 ∂ν) - (∫ z : ℤ, (z : ℝ) ∂ν) ^ 2)
  ring

/-- The finite-variance expansion, in a form that also includes the degenerate law. -/
theorem smoothing_div_tendsto_variance (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Tendsto (fun s : ℝ => smoothing ν s / s) (𝓝[>] 0) (𝓝 (2 * variance ν)) := by
  rw [← secondMoment_symmetrizedLaw ν hint hsq]
  exact smoothing_div_tendsto_secondMoment ν (integrable_sq_symmetrizedLaw ν hint hsq)

/-- The smoothing is bounded above by its linear finite-moment majorant. -/
theorem smoothing_div_le_secondMoment (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hD : Integrable (fun x : ℝ => x ^ 2) (symmetrizedLaw ν))
    {s : ℝ} (hs : 0 < s) :
    smoothing ν s / s ≤ ∫ x : ℝ, x ^ 2 ∂(symmetrizedLaw ν) := by
  rw [smoothing, ← integral_div]
  exact integral_mono ((integrable_smoothing ν hs.le).div_const s) hD
    fun x => (smoothing_quotient_bounds hs).2

/-- Attraction excludes a degenerate symmetrized second moment. -/
theorem secondMoment_symmetrizedLaw_pos {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b)
    (hD : Integrable (fun x : ℝ => x ^ 2) (symmetrizedLaw ν)) :
    0 < ∫ x : ℝ, x ^ 2 ∂(symmetrizedLaw ν) := by
  have hlim := tendsto_nat_mul_smoothing_div_sq hb (r := 1) one_pos
  simp only [Real.one_rpow, mul_one] at hlim
  have hp := hlim.eventually (lt_mem_nhds (smoothingConstant_pos hb.alpha_mem))
  obtain ⟨N, hN⟩ := hb.pos
  obtain ⟨n, hn, hbn⟩ := (hp.and (eventually_ge_atTop N)).exists
  have hs : 0 < 1 / b n ^ 2 := by positivity [hN n hbn]
  have hH : 0 < smoothing ν (1 / b n ^ 2) := by
    exact pos_of_mul_pos_right hn (Nat.cast_nonneg n)
  exact (div_pos hH hs).trans_le (smoothing_div_le_secondMoment ν hD hs)

/-- A finite-variance law attracted to a stable law has positive variance. -/
theorem variance_pos_of_integrable_sq {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) : 0 < variance ν := by
  have h := secondMoment_symmetrizedLaw_pos hb (integrable_sq_symmetrizedLaw ν hint hsq)
  rw [secondMoment_symmetrizedLaw ν hint hsq] at h
  linarith

/-- Finite second moment forces the Gaussian stable index. No support assumption
is needed for this direction. -/
theorem index_eq_two_of_integrable_sq {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) : θ = 2 := by
  have hlim := smoothing_div_tendsto_variance ν hint hsq
  have hv : 2 * variance ν ≠ 0 := by
    have := variance_pos_of_integrable_sq hb hint hsq
    positivity
  have hscale : Tendsto (fun s : ℝ => 2 * s) (𝓝[>] 0) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨by simpa using (tendsto_const_nhds.mul
      (tendsto_id.mono_right nhdsWithin_le_nhds : Tendsto (fun s : ℝ => s) (𝓝[>] 0) (𝓝 0))),
      by filter_upwards [self_mem_nhdsWithin] with s hs; exact mul_pos (by norm_num) hs⟩
  have hratio := ((hlim.comp hscale).div hlim hv).const_mul 2
  simp only [div_self hv, mul_one] at hratio
  have hratio' : Tendsto (fun s : ℝ => smoothing ν (2 * s) / smoothing ν s)
      (𝓝[>] 0) (𝓝 2) := by
    apply hratio.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    dsimp only [Function.comp_def, Pi.div_apply]
    have hs0 : s ≠ 0 := ne_of_gt hs
    field_simp
  have heq :=
    tendsto_nhds_unique (smoothing_regularlyVarying_zero hb (c := 2) (by norm_num)) hratio'
  have hexp : θ / 2 = 1 := (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1)).mp (by simpa using heq)
  linarith

/-- In the attracting finite-variance case the linear smoothing asymptotic is
nonzero, hence it can also be stated as asymptotic equivalence. -/
theorem smoothing_isEquivalent_variance {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hsq : Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Asymptotics.IsEquivalent (𝓝[>] 0) (smoothing ν) (fun s => 2 * variance ν * s) := by
  have hv : 2 * variance ν ≠ 0 := by
    have := variance_pos_of_integrable_sq hb hint hsq
    positivity
  have h := (smoothing_div_tendsto_variance ν hint hsq).div_const (2 * variance ν)
  rw [div_self hv] at h
  apply Asymptotics.isEquivalent_of_tendsto_one
  convert h using 1
  funext s
  simp only [Pi.div_apply]
  ring

/-- Every positive smoothing parameter has strictly positive defect under attraction. -/
theorem smoothing_pos {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b)
    {s : ℝ} (hs : 0 < s) : 0 < smoothing ν s := by
  have hlim := tendsto_nat_mul_smoothing_div_sq hb (r := 1) one_pos
  simp only [Real.one_rpow, mul_one] at hlim
  have hp := hlim.eventually (lt_mem_nhds (smoothingConstant_pos hb.alpha_mem))
  have hlarge := (TransformConvergence.tendsto_atTop ν hb).eventually_gt_atTop
    (max 1 (1 / s))
  obtain ⟨n, hn, hbn⟩ := (hp.and hlarge).exists
  have hb1 : 1 < b n := (le_max_left _ _).trans_lt hbn
  have hb2 : 1 / s < b n := (le_max_right _ _).trans_lt hbn
  have hscale : 1 / b n ^ 2 ≤ s := by
    rw [div_le_iff₀ (by positivity : 0 < b n ^ 2)]
    have hb2' : 1 < b n * s := (div_lt_iff₀ hs).mp hb2
    nlinarith
  have hH : 0 < smoothing ν (1 / b n ^ 2) :=
    pos_of_mul_pos_right hn (Nat.cast_nonneg n)
  exact hH.trans_le (smoothing_mono ν (by positivity) hscale)

/-- D3 in the positive, reciprocal-coordinate predicate expected by B1. -/
theorem smoothing_regularlyVaryingAtZero {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b) :
    KaramataTransforms.RegularlyVaryingAtZero (smoothing ν) (θ / 2) := by
  constructor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact smoothing_pos hb (by positivity : 0 < 1 / x)
  · intro c hc
    have h := (smoothing_regularlyVarying_zero hb (inv_pos.mpr hc)).comp
      tendsto_inv_atTop_nhdsGT_zero
    rw [Real.inv_rpow hc.le, ← Real.rpow_neg hc.le] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    dsimp only [Function.comp_def]
    simp only [one_div, mul_inv_rev]
    rw [mul_comm]

/-- Dividing the smoothing by its parameter gives the Laplace exponent needed
for the integrated squared-difference tail, including the boundary exponent zero. -/
theorem smoothing_quotient_regularlyVaryingAtZero {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b) :
    KaramataTransforms.RegularlyVaryingAtZero
      (fun s => smoothing ν s / s) (θ / 2 - 1) := by
  constructor
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact div_pos (smoothing_pos hb (by positivity : 0 < 1 / x)) (by positivity)
  · intro c hc
    have h := ((smoothing_regularlyVaryingAtZero hb).2 c hc).const_mul c
    have he : c * c ^ (-(θ / 2)) = c ^ (-(θ / 2 - 1)) := by
      conv_lhs => arg 1; rw [← Real.rpow_one c]
      rw [← Real.rpow_add hc]
      congr 1
      ring
    rw [he] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp

/-- Tail of the squared independent difference. -/
noncomputable def squaredTail (ν : Measure ℤ) (y : ℝ) : ℝ :=
  (symmetrizedLaw ν).real {x : ℝ | y < x ^ 2}

theorem squaredTail_antitone (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    Antitone (squaredTail ν) := by
  intro a b hab
  exact measureReal_mono (fun x hx => hab.trans_lt hx)

theorem squaredTail_bounds (ν : Measure ℤ) [IsProbabilityMeasure ν] (y : ℝ) :
    0 ≤ squaredTail ν y ∧ squaredTail ν y ≤ 1 := by
  exact ⟨measureReal_nonneg, (measureReal_mono (subset_univ _)).trans (by simp)⟩

/-- Locally finite measure whose density is the squared-difference tail. -/
noncomputable def squaredTailMeasure (ν : Measure ℤ) : Measure ℝ :=
  volume.withDensity (fun y => ENNReal.ofReal (squaredTail ν y))

instance squaredTailMeasure_locallyFinite (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    IsLocallyFiniteMeasure (squaredTailMeasure ν) := by
  apply Measure.isLocallyFiniteMeasure_of_le (μ := volume)
  have h := withDensity_mono (μ := (volume : Measure ℝ))
    (f := fun y => ENNReal.ofReal (squaredTail ν y)) (g := fun _ => 1)
    (ae_of_all _ fun y => by simpa using
      ENNReal.ofReal_le_ofReal (squaredTail_bounds ν y).2)
  change squaredTailMeasure ν ≤ volume.withDensity (1 : ℝ → ℝ≥0∞) at h
  rwa [withDensity_one] at h

theorem squaredTailMeasure_laplace_integrable (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun y => Real.exp (-s * y)) (Ici 0) (squaredTailMeasure ν) := by
  rw [IntegrableOn, squaredTailMeasure, restrict_withDensity measurableSet_Ici,
    integrable_withDensity_iff (squaredTail_antitone ν).measurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  have hi : IntegrableOn (fun y : ℝ => Real.exp (-s * y)) (Ici 0) :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0)
  simp only [ENNReal.toReal_ofReal (squaredTail_bounds ν _).1]
  apply hi.mono' (((measurable_const.mul measurable_id).exp).mul
    (squaredTail_antitone ν).measurable).aestronglyMeasurable
  exact ae_of_all _ fun y => by
    dsimp only [Pi.mul_apply, id_eq]
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_nonneg _) (squaredTail_bounds ν y).1)]
    exact mul_le_of_le_one_right (Real.exp_nonneg _) (squaredTail_bounds ν y).2

/-- The layer-cake/Fubini identity that turns D3 into the transform hypothesis of B1. -/
theorem laplace_squaredTailMeasure (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {s : ℝ} (hs : 0 < s) :
    KaramataTransforms.laplace (squaredTailMeasure ν) s = smoothing ν s / s := by
  let μ := symmetrizedLaw ν
  let η : Measure ℝ := volume.restrict (Ici 0)
  let k : ℝ × ℝ → ℝ := fun p => if p.2 < p.1 ^ 2 then Real.exp (-s * p.2) else 0
  have hkm : Measurable k :=
    (Real.measurable_exp.comp (measurable_const.mul measurable_snd)).ite
      (measurableSet_lt measurable_snd (measurable_fst.pow_const 2)) measurable_const
  have hi : Integrable (fun y => Real.exp (-s * y)) η :=
    Iff.mpr integrableOn_Ici_iff_integrableOn_Ioi
      (integrableOn_exp_mul_Ioi (neg_neg_of_pos hs) 0)
  have hslice (x : ℝ) : Integrable (fun y => k (x, y)) η := by
    change Integrable ((Iio (x ^ 2)).indicator (fun y => Real.exp (-s * y))) η
    exact hi.indicator measurableSet_Iio
  have hslice_eq (x : ℝ) :
      (∫ y, k (x, y) ∂η) = (1 - Real.exp (-s * x ^ 2)) / s := by
    have hsplit := integral_add_compl (μ := η) (s := Iio (x ^ 2)) measurableSet_Iio hi
    have hfull : (∫ y, Real.exp (-s * y) ∂η) = 1 / s := by
      rw [show η = volume.restrict (Ici 0) from rfl, integral_Ici_eq_integral_Ioi,
        integral_exp_mul_Ioi (neg_neg_of_pos hs)]
      simp
    have hrest : (∫ y in (Iio (x ^ 2))ᶜ, Real.exp (-s * y) ∂η) =
        Real.exp (-s * x ^ 2) / s := by
      rw [compl_Iio, show η = volume.restrict (Ici 0) from rfl,
        Measure.restrict_restrict measurableSet_Ici,
        inter_eq_left.mpr (Ici_subset_Ici.mpr (sq_nonneg x)),
        integral_Ici_eq_integral_Ioi, integral_exp_mul_Ioi (neg_neg_of_pos hs)]
      ring
    change (∫ y, (Iio (x ^ 2)).indicator (fun y => Real.exp (-s * y)) y ∂η) = _
    rw [integral_indicator measurableSet_Iio]
    rw [hfull, hrest] at hsplit
    rw [sub_div]
    linarith
  have hki : Integrable k (μ.prod η) := by
    apply (integrable_prod_iff hkm.aestronglyMeasurable).mpr
    refine ⟨ae_of_all _ hslice, ?_⟩
    have hb : Integrable (fun _ : ℝ => 1 / s) μ := integrable_const _
    apply hb.mono' (hkm.aestronglyMeasurable.norm.integral_prod_right')
    exact ae_of_all _ fun x => by
      have hnonneg (y : ℝ) : 0 ≤ k (x, y) := by dsimp [k]; split_ifs <;> positivity
      simp_rw [Real.norm_of_nonneg (hnonneg _)]
      rw [hslice_eq, Real.norm_of_nonneg (smoothing_quotient_bounds hs).1]
      exact div_le_div_of_nonneg_right (by linarith [Real.exp_pos (-s * x ^ 2)]) hs.le
  have hswap := integral_integral_swap (f := fun x y => k (x, y)) hki
  have hleft : (∫ x, ∫ y, k (x, y) ∂η ∂μ) = smoothing ν s / s := by
    simp_rw [hslice_eq]
    rw [integral_div]
    rfl
  have hright : (∫ y, ∫ x, k (x, y) ∂μ ∂η) =
      KaramataTransforms.laplace (squaredTailMeasure ν) s := by
    unfold KaramataTransforms.laplace squaredTailMeasure
    rw [setIntegral_withDensity_eq_setIntegral_toReal_smul
      (squaredTail_antitone ν).measurable.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Ici]
    apply integral_congr_ae
    exact ae_of_all _ fun y => by
      change (∫ x, {x : ℝ | y < x ^ 2}.indicator (fun _ => Real.exp (-s * y)) x ∂μ) = _
      rw [integral_indicator (by
        simpa only [id_eq] using measurableSet_lt measurable_const (measurable_id.pow_const 2)),
        integral_const]
      simp only [ENNReal.toReal_ofReal (squaredTail_bounds ν y).1, smul_eq_mul]
      simp only [measureReal_restrict_apply_univ]
      rfl
  rw [hleft, hright] at hswap
  exact hswap.symm

/-- The cumulative mass of the tail-density measure is the integrated tail. -/
theorem cumulative_squaredTailMeasure (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {y : ℝ} (hy : 0 ≤ y) :
    KaramataTransforms.cumulative (squaredTailMeasure ν) y =
      ∫ t in (0 : ℝ)..y, squaredTail ν t := by
  unfold KaramataTransforms.cumulative
  have hone : (squaredTailMeasure ν).real (Icc 0 y) =
      ∫ _ in Icc 0 y, (1 : ℝ) ∂(squaredTailMeasure ν) := by simp
  rw [hone, squaredTailMeasure, setIntegral_withDensity_eq_setIntegral_toReal_smul
    (squaredTail_antitone ν).measurable.ennreal_ofReal
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top) _ measurableSet_Icc]
  simp only [ENNReal.toReal_ofReal (squaredTail_bounds ν _).1, smul_eq_mul, mul_one]
  rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hy]

/-- The Tauberian output for the symmetrized squared step, valid also at index two. -/
theorem integratedSquaredTail_regularlyVarying {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b) :
    KaramataTransforms.RegularlyVarying
      (fun y => ∫ t in (0 : ℝ)..y, squaredTail ν t) (1 - θ / 2) := by
  have hF : KaramataTransforms.RegularlyVaryingAtZero
      (KaramataTransforms.laplace (squaredTailMeasure ν)) (-(1 - θ / 2)) := by
    have he : -(1 - θ / 2) = θ / 2 - 1 := by ring
    rw [he]
    have h := smoothing_quotient_regularlyVaryingAtZero hb
    constructor
    · filter_upwards [h.1, eventually_gt_atTop (0 : ℝ)] with x hx hx0
      rwa [laplace_squaredTailMeasure ν (by positivity)]
    · intro c hc
      refine (h.2 c hc).congr' ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      rw [laplace_squaredTailMeasure ν (by positivity),
        laplace_squaredTailMeasure ν (by positivity)]
  have hU := KaramataTransforms.laplace_tauberian (squaredTailMeasure ν)
    (by linarith [hb.alpha_mem.2] : 0 ≤ 1 - θ / 2)
    (fun _ hs => squaredTailMeasure_laplace_integrable ν hs) hF
  constructor
  · filter_upwards [hU.1, eventually_ge_atTop (0 : ℝ)] with y hy hy0
    rwa [cumulative_squaredTailMeasure ν hy0] at hy
  · intro c hc
    refine (hU.2 c hc).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [cumulative_squaredTailMeasure ν hy, cumulative_squaredTailMeasure ν (mul_nonneg hc.le hy)]

/-- The monotone density conclusion, including its zero limit at the Gaussian boundary. -/
theorem squaredTail_density_limit {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b) :
    Tendsto (fun y : ℝ => y * squaredTail ν y /
      ∫ t in (0 : ℝ)..y, squaredTail ν t) atTop (𝓝 (1 - θ / 2)) := by
  exact MonotoneDensity.monotone_density
    (fun y _ => (squaredTail_bounds ν y).1) ((squaredTail_antitone ν).antitoneOn _)
    (integratedSquaredTail_regularlyVarying hb).2

/-- Below the Gaussian index, the squared-difference tail itself is regularly varying. -/
theorem squaredTail_regularlyVarying {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b) (hθ : θ < 2) :
    MonotoneDensity.IsRegVaryAtTop (squaredTail ν) (-θ / 2) := by
  have hU := (integratedSquaredTail_regularlyVarying hb).of_ratio
    (by linarith : 0 < 1 - θ / 2) (squaredTail_density_limit hb)
  intro c hc
  have h := (hU.2 c hc).div_const c
  have he : c ^ (1 - θ / 2) / c = c ^ (-θ / 2) := by
    rw [← Real.rpow_sub_one hc.ne' (1 - θ / 2)]
    congr 1
    ring
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  field_simp

private theorem min_sq_sum_le (a b c : ℝ) :
    min (a ^ 2) c + min (b ^ 2) c ≤ c + |a * b| := by
  rcases le_total |a| |b| with h | h
  · have hab : a ^ 2 ≤ |a * b| := by
      have hh := mul_le_mul_of_nonneg_left h (abs_nonneg a)
      rw [← sq, sq_abs, ← abs_mul] at hh
      exact hh
    linarith [min_le_left (a ^ 2) c, min_le_right (b ^ 2) c]
  · have hab : b ^ 2 ≤ |a * b| := by
      have hh := mul_le_mul_of_nonneg_right h (abs_nonneg b)
      rw [← sq, sq_abs, ← abs_mul] at hh
      exact hh
    linarith [min_le_left (b ^ 2) c, min_le_right (a ^ 2) c]

/-- Uniform pointwise comparison of capped squared differences and capped squares. -/
theorem capped_difference_bound (a b x : ℝ) :
    |min ((a - b) ^ 2) (x ^ 2) - min (a ^ 2) (x ^ 2) - min (b ^ 2) (x ^ 2)| ≤
      2 * |a * b| := by
  have hsum := min_sq_sum_le a b (x ^ 2)
  have hab := le_abs_self (a * b)
  have hnab := neg_le_abs (a * b)
  have hn := abs_nonneg (a * b)
  rw [abs_le]
  by_cases ha : a ^ 2 ≤ x ^ 2 <;> by_cases hb : b ^ 2 ≤ x ^ 2 <;>
    by_cases hd : (a - b) ^ 2 ≤ x ^ 2 <;>
    simp only [min_def, ha, hb, hd, ite_true, ite_false] at hsum ⊢ <;>
    constructor <;> nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg (a - b)]

/-- Layer cake for a capped square. This form needs no second-moment hypothesis. -/
theorem integral_min_sq_eq_integrated_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    {y : ℝ} (hy : 0 ≤ y) :
    (∫ ω, min (X ω ^ 2) y ∂μ) = ∫ t in (0 : ℝ)..y, μ.real {ω | t < X ω ^ 2} := by
  let η : Measure ℝ := volume.restrict (Ioo 0 y)
  let k : Ω × ℝ → ℝ := fun p => if p.2 < X p.1 ^ 2 then 1 else 0
  have hm : Measurable k := measurable_const.ite
    (measurableSet_lt measurable_snd ((hX.comp measurable_fst).pow_const 2)) measurable_const
  have hk : Integrable k (μ.prod η) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact ae_of_all _ fun p => by dsimp [k]; split_ifs <;> norm_num
  have hs (ω : Ω) : (∫ t, k (ω, t) ∂η) = min (X ω ^ 2) y := by
    change (∫ t, (Iio (X ω ^ 2)).indicator (fun _ => (1 : ℝ)) t ∂η) = _
    rw [integral_indicator_const _ measurableSet_Iio]
    simp only [smul_eq_mul, mul_one]
    rw [show η = volume.restrict (Ioo 0 y) from rfl,
      measureReal_restrict_apply measurableSet_Iio, Iio_inter_Ioo,
      Real.volume_real_Ioo_of_le (le_min (sq_nonneg _) hy), sub_zero]
  have ht (t : ℝ) : (∫ ω, k (ω, t) ∂μ) = μ.real {ω | t < X ω ^ 2} := by
    change (∫ ω, {ω | t < X ω ^ 2}.indicator (fun _ => (1 : ℝ)) ω ∂μ) = _
    rw [integral_indicator_const _ (measurableSet_lt measurable_const (hX.pow_const 2))]
    simp only [smul_eq_mul, mul_one]
  have heq := integral_integral_swap (f := fun ω t => k (ω, t)) hk
  simp_rw [hs, ht] at heq
  rw [intervalIntegral.integral_of_le hy, integral_Ioc_eq_integral_Ioo]
  exact heq

private theorem integrable_min_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X : Ω → ℝ) (hX : Measurable X)
    {y : ℝ} (hy : 0 ≤ y) : Integrable (fun ω => min (X ω ^ 2) y) μ := by
  apply Integrable.of_bound ((hX.pow_const 2).min measurable_const).aestronglyMeasurable y
  exact ae_of_all _ fun ω => by
    rw [Real.norm_of_nonneg (le_min (sq_nonneg _) hy)]
    exact min_le_right _ _

/-- Capped second moment, with the cutoff in squared coordinates. -/
noncomputable def cappedSecondMoment (ν : Measure ℤ) (y : ℝ) : ℝ :=
  ∫ z : ℤ, min ((z : ℝ) ^ 2) y ∂ν

/-- The bounded-error desymmetrization estimate. -/
theorem integratedSquaredTail_sub_two_capped_bound (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) {y : ℝ} (hy : 0 ≤ y) :
    |(∫ t in (0 : ℝ)..y, squaredTail ν t) - 2 * cappedSecondMoment ν y| ≤
      2 * (∫ z : ℤ, |(z : ℝ)| ∂ν) ^ 2 := by
  have hD := integrable_min_sq (ν.prod ν) (fun p : ℤ × ℤ => (p.1 : ℝ) - (p.2 : ℝ))
    (by fun_prop) hy
  have hZ := integrable_min_sq ν (fun z : ℤ => (z : ℝ)) (by fun_prop) hy
  have hdiff : Integrable (fun p : ℤ × ℤ =>
      min (((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) y - min ((p.1 : ℝ) ^ 2) y -
        min ((p.2 : ℝ) ^ 2) y) (ν.prod ν) :=
    (hD.sub (hZ.comp_fst ν)).sub (hZ.comp_snd ν)
  have hcross := (hint.abs.mul_prod hint.abs).const_mul 2
  have hbound :
      |∫ p : ℤ × ℤ, min (((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) y -
        min ((p.1 : ℝ) ^ 2) y - min ((p.2 : ℝ) ^ 2) y ∂(ν.prod ν)| ≤
      2 * (∫ z : ℤ, |(z : ℝ)| ∂ν) ^ 2 := by
    calc
      _ ≤ ∫ p : ℤ × ℤ, |min (((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) y -
          min ((p.1 : ℝ) ^ 2) y - min ((p.2 : ℝ) ^ 2) y| ∂(ν.prod ν) :=
        abs_integral_le_integral_abs
      _ ≤ ∫ p : ℤ × ℤ, 2 * (|(p.1 : ℝ)| * |(p.2 : ℝ)|) ∂(ν.prod ν) := by
        apply integral_mono hdiff.abs hcross
        intro p
        simpa only [Real.sq_sqrt hy, abs_mul] using
          capped_difference_bound (p.1 : ℝ) (p.2 : ℝ) (Real.sqrt y)
      _ = _ := by
        rw [integral_const_mul, integral_prod_mul (fun z : ℤ => |(z : ℝ)|)
          (fun z : ℤ => |(z : ℝ)|)]
        ring
  have hU : (∫ t in (0 : ℝ)..y, squaredTail ν t) =
      ∫ p : ℤ × ℤ, min (((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) y ∂(ν.prod ν) := by
    change (∫ t in (0 : ℝ)..y, (symmetrizedLaw ν).real {ω | t < id ω ^ 2}) = _
    rw [← integral_min_sq_eq_integrated_tail (symmetrizedLaw ν) id measurable_id hy]
    rw [symmetrizedLaw_eq_map, integral_map (by fun_prop) (by fun_prop)]
    rfl
  rw [integral_sub (f := fun p : ℤ × ℤ => min (((p.1 : ℝ) - (p.2 : ℝ)) ^ 2) y -
      min ((p.1 : ℝ) ^ 2) y) (hD.sub (hZ.comp_fst ν)) (hZ.comp_snd ν),
    integral_sub hD (hZ.comp_fst ν), integral_prod _ (hZ.comp_fst ν),
    integral_prod _ (hZ.comp_snd ν)] at hbound
  simp only [integral_const, probReal_univ, one_smul] at hbound
  rw [hU]
  convert hbound using 1
  congr 1
  unfold cappedSecondMoment
  ring

/-- The truncated moment is dominated by the capped moment. -/
theorem truncSecondMoment_sqrt_le_capped (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {y : ℝ} (hy : 0 ≤ y) : truncSecondMoment ν (Real.sqrt y) ≤ cappedSecondMoment ν y := by
  rw [truncSecondMoment, ← integral_indicator MeasurableSet.of_discrete]
  refine integral_mono_of_nonneg ?_
    (integrable_min_sq ν (fun z : ℤ => (z : ℝ)) (by fun_prop) hy) ?_
  · exact ae_of_all _ fun z => Set.indicator_nonneg (fun _ _ => sq_nonneg _) z
  · exact ae_of_all _ fun z => by
      by_cases hz : |(z : ℝ)| ≤ Real.sqrt y
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hz, ite_true]
        rw [min_eq_left]
        nlinarith [Real.sq_sqrt hy, sq_abs (z : ℝ),
          (sq_le_sq₀ (abs_nonneg (z : ℝ)) (Real.sqrt_nonneg y)).mpr hz]
      · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hz, ite_false]
        exact le_min (sq_nonneg _) hy

/-- Infinite second moment forces the capped moments to diverge. -/
theorem cappedSecondMoment_tendsto_atTop (ν : Measure ℤ) [IsProbabilityMeasure ν]
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Tendsto (cappedSecondMoment ν) atTop atTop := by
  apply tendsto_atTop_mono' _ _
    ((GaussianBranch.truncSecondMoment_tendsto_atTop hinf).comp Real.tendsto_sqrt_atTop)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  exact truncSecondMoment_sqrt_le_capped ν hy

/-- Desymmetrization transfers the integrated-tail variation to the original capped moment. -/
theorem cappedSecondMoment_regularlyVarying {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    KaramataTransforms.RegularlyVarying (cappedSecondMoment ν) (1 - θ / 2) := by
  let U : ℝ → ℝ := fun y => ∫ t in (0 : ℝ)..y, squaredTail ν t
  let C : ℝ := 2 * (∫ z : ℤ, |(z : ℝ)| ∂ν) ^ 2
  have htop := cappedSecondMoment_tendsto_atTop ν hinf
  have hratio : Tendsto (fun y => U y / cappedSecondMoment ν y) atTop (𝓝 2) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hsmall := (tendsto_const_nhds.div_atTop htop (a := C)).eventually (gt_mem_nhds hε)
    filter_upwards [hsmall, htop.eventually_gt_atTop 0, eventually_ge_atTop (0 : ℝ)]
      with y hsmall hpos hy
    rw [Real.dist_eq]
    have he : |U y / cappedSecondMoment ν y - 2| =
        |U y - 2 * cappedSecondMoment ν y| / cappedSecondMoment ν y := by
      rw [show U y / cappedSecondMoment ν y - 2 =
        (U y - 2 * cappedSecondMoment ν y) / cappedSecondMoment ν y by field_simp]
      rw [abs_div, abs_of_pos hpos]
    rw [he]
    exact (div_le_div_of_nonneg_right
      (integratedSquaredTail_sub_two_capped_bound ν hint hy) hpos.le).trans_lt hsmall
  apply (integratedSquaredTail_regularlyVarying hb).of_ratio (C := 2⁻¹) (by norm_num)
  simpa only [inv_div] using hratio.inv₀ (by norm_num : (2 : ℝ) ≠ 0)

/-- Tail of the square of the original step. -/
noncomputable def stepSquaredTail (ν : Measure ℤ) (y : ℝ) : ℝ :=
  ν.real {z : ℤ | y < (z : ℝ) ^ 2}

theorem stepSquaredTail_antitone (ν : Measure ℤ) [IsProbabilityMeasure ν] :
    Antitone (stepSquaredTail ν) := by
  intro a b hab
  exact measureReal_mono fun z hz => hab.trans_lt hz

/-- Monotone density for the original capped moments. -/
theorem stepSquaredTail_density_limit {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    Tendsto (fun y => y * stepSquaredTail ν y / cappedSecondMoment ν y) atTop
      (𝓝 (1 - θ / 2)) := by
  have he (y : ℝ) (hy : 0 ≤ y) : cappedSecondMoment ν y =
      ∫ t in (0 : ℝ)..y, stepSquaredTail ν t :=
    integral_min_sq_eq_integrated_tail ν (fun z : ℤ => (z : ℝ)) (by fun_prop) hy
  have hC := cappedSecondMoment_regularlyVarying hb hint hinf
  have hU : MonotoneDensity.IsRegVaryAtTop
      (fun y => ∫ t in (0 : ℝ)..y, stepSquaredTail ν t) (1 - θ / 2) := by
    intro c hc
    refine (hC.2 c hc).congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
    rw [he y hy, he (c * y) (mul_nonneg hc.le hy)]
  refine (MonotoneDensity.monotone_density (f := stepSquaredTail ν) (fun _ _ => measureReal_nonneg)
    ((stepSquaredTail_antitone ν).antitoneOn _) hU).congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with y hy
  rw [he y hy]

/-- Below index two, monotone density identifies the tail of the original square. -/
theorem stepSquaredTail_regularlyVarying {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) (hθ : θ < 2) :
    MonotoneDensity.IsRegVaryAtTop (stepSquaredTail ν) (-θ / 2) := by
  have hU := (cappedSecondMoment_regularlyVarying hb hint hinf).of_ratio
    (by linarith : 0 < 1 - θ / 2) (stepSquaredTail_density_limit hb hint hinf)
  intro c hc
  have h := (hU.2 c hc).div_const c
  have he : c ^ (1 - θ / 2) / c = c ^ (-θ / 2) := by
    rw [← Real.rpow_sub_one hc.ne' (1 - θ / 2)]
    congr 1
    ring
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
  field_simp

/-- Bounded negative support removes the negative contribution to the squared tail. -/
theorem stepSquaredTail_sq_eq_rightTail (ν : Measure ℤ)
    (hneg : ν {z : ℤ | z < -1} = 0) {x : ℝ} (hx : 1 ≤ x) :
    stepSquaredTail ν (x ^ 2) = ν.real {z : ℤ | x < (z : ℝ)} := by
  have hnull : ∀ᵐ z ∂ν, ¬ z < -1 := by rw [ae_iff]; simpa using hneg
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hnull] with z hz
  have hz' : (-1 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (not_lt.mp hz)
  apply propext
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- **D4, non-Gaussian branch:** attraction with infinite second moment forces
regular variation of the right tail with index `-θ`. -/
theorem rightTail_regularlyVarying {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ (mean ν) b)
    (hneg : ν {z : ℤ | z < -1} = 0)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) (hθ : θ < 2) :
    MonotoneDensity.IsRegVaryAtTop (fun x : ℝ => ν.real {z : ℤ | x < (z : ℝ)}) (-θ) := by
  intro c hc
  have h := ((stepSquaredTail_regularlyVarying hb hint hinf hθ) (c ^ 2)
    (sq_pos_of_pos hc)).comp (tendsto_pow_atTop (n := 2) (by norm_num))
  have he : (c ^ 2) ^ (-θ / 2) = c ^ (-θ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hc.le]
    congr 1
    ring
  rw [he] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (max 1 (1 / c))] with x hx
  have hx1 : 1 ≤ x := (le_max_left _ _).trans hx
  have hcx : 1 ≤ c * x := by
    have hh := (le_max_right _ _).trans hx
    rw [div_le_iff₀ hc] at hh
    linarith
  dsimp only [Function.comp_def]
  rw [← mul_pow, stepSquaredTail_sq_eq_rightTail ν hneg hx1,
    stepSquaredTail_sq_eq_rightTail ν hneg hcx]

/-- Capped and truncated moments differ by the endpoint tail term. -/
theorem truncSecondMoment_sqrt_eq_capped_sub_tail (ν : Measure ℤ) [IsProbabilityMeasure ν]
    {y : ℝ} (hy : 0 ≤ y) :
    truncSecondMoment ν (Real.sqrt y) = cappedSecondMoment ν y - y * stepSquaredTail ν y := by
  have hpt (z : ℤ) : {z : ℤ | |(z : ℝ)| ≤ Real.sqrt y}.indicator
      (fun z => (z : ℝ) ^ 2) z = min ((z : ℝ) ^ 2) y -
        {z : ℤ | y < (z : ℝ) ^ 2}.indicator (fun _ => y) z := by
    have he : |(z : ℝ)| ≤ Real.sqrt y ↔ (z : ℝ) ^ 2 ≤ y := by
      simpa only [sq_abs, Real.sq_sqrt hy] using
        (sq_le_sq₀ (abs_nonneg (z : ℝ)) (Real.sqrt_nonneg y)).symm
    by_cases hz : (z : ℝ) ^ 2 ≤ y
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, he, hz, not_lt.mpr hz,
        min_eq_left hz, ite_true, ite_false, sub_zero]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, he, hz, lt_of_not_ge hz,
        min_eq_right (le_of_not_ge hz), ite_true, ite_false, sub_self]
  rw [truncSecondMoment, ← integral_indicator MeasurableSet.of_discrete]
  simp_rw [hpt]
  rw [integral_sub (integrable_min_sq ν (fun z : ℤ => (z : ℝ)) (by fun_prop) hy)
    ((integrable_const y).indicator MeasurableSet.of_discrete),
    integral_indicator_const _ MeasurableSet.of_discrete, smul_eq_mul, mul_comm]
  rfl

/-- **D4, Gaussian branch:** infinite second moment and Gaussian attraction imply
slow variation and divergence of the truncated second moment. The proof needs no
support bound, because the capped-moment comparison already handles both tails. -/
theorem truncSecondMoment_slowlyVarying_unbounded {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {b : ℕ → ℝ} (hb : IsStableAttracted ν 2 (mean ν) b)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν)
    (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν) :
    BGW.StableTrees.SlowlyVarying (truncSecondMoment ν) ∧
      Tendsto (truncSecondMoment ν) atTop atTop := by
  have hC : KaramataTransforms.RegularlyVarying (cappedSecondMoment ν) 0 := by
    simpa using cappedSecondMoment_regularlyVarying hb hint hinf
  have hD : Tendsto (fun y => y * stepSquaredTail ν y / cappedSecondMoment ν y) atTop (𝓝 0) := by
    simpa using stepSquaredTail_density_limit hb hint hinf
  have hratio : Tendsto (fun y => truncSecondMoment ν (Real.sqrt y) / cappedSecondMoment ν y)
      atTop (𝓝 1) := by
    have h := hD.const_sub 1
    simp only [sub_zero] at h
    refine h.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ), hC.1] with y hy hpos
    rw [truncSecondMoment_sqrt_eq_capped_sub_tail ν hy]
    field_simp
  have hK := hC.of_ratio (V := fun y => truncSecondMoment ν (Real.sqrt y)) one_pos hratio
  refine ⟨?_, GaussianBranch.truncSecondMoment_tendsto_atTop hinf⟩
  intro c hc
  have h := (hK.2 (c ^ 2) (sq_pos_of_pos hc)).comp
    (tendsto_pow_atTop (n := 2) (by norm_num))
  simp only [Real.rpow_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  dsimp only [Function.comp_def]
  rw [← mul_pow, Real.sqrt_sq hx, Real.sqrt_sq (mul_nonneg hc.le hx)]

/-- Stable attraction below index two automatically has infinite second moment. -/
theorem not_integrable_sq_of_index_lt_two {ν : Measure ℤ} [IsProbabilityMeasure ν]
    {θ m : ℝ} {b : ℕ → ℝ} (hb : IsStableAttracted ν θ m b)
    (hint : Integrable (fun z : ℤ => (z : ℝ)) ν) (hθ : θ < 2) :
    ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) ν := by
  intro hsq
  have := index_eq_two_of_integrable_sq hb hint hsq
  linarith

end BGW.StableTrees.Attraction.DomainCriterion
