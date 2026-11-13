/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionDensity
import BGW.StableTrees.ExcursionMarkov

/-!
# The path-only Gamma identity

The remaining lifetime gives the size-tail identity. Gamma weighting cancels
its survival kernel and the unit prefix density supplies the normalization.

## Main results

* `levyExcLaw_prefix_eq_withDensity_tail`: the unit prefix law is the Gamma-weighted
  tail prefix measure.
* `lintegral_gamma_identity_path`: the Gamma identity for nonnegative measurable path tests.
* `gamma_identity_path`: the Gamma identity for bounded signed path tests.
* `integral_gammaA_tail_eq_one`: the Gamma weight integrates to one against the tail prefix.
* `excursionTail_size_tail`: the size-tail identity for the excursion tail measure.

## References

* T. Duquesne, *A limit theorem for the contour process of conditioned Galton--Watson trees*,
  Ann. Probab. 31 (2003), 996--1027; path-prefix absolute continuity.
* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
* T. Duquesne, *Path decompositions for real Lévy processes*,
  Ann. Inst. H. Poincaré Probab. Statist. 39 (2003), 339–370.
* T. Duquesne and J.-F. Le Gall, *Random Trees, Lévy Processes and Spatial Branching
  Processes*, Astérisque 281 (2002).
* I. Kortchemski, *A simple proof of Duquesne's theorem on contour processes of
  conditioned Galton--Watson trees*, arXiv:1109.4138, Proposition 2.3 (path part).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- Law of the excursion prefix under the normalized lifetime tail. -/
noncomputable def tailPrefix (θ : ℝ) (a : ℝ≥0) : Measure (D (a : ℝ) ℝ) :=
  (tailExcursionLaw θ : Measure Excursion).map (excursionRestrict a)

/-- Endpoint coordinate of a compact path. -/
noncomputable def evalEnd (a : ℝ≥0) (x : D (a : ℝ) ℝ) : ℝ :=
  (x : Set.Icc (0 : ℝ) a → ℝ) ⟨a, a.2, le_rfl⟩

/-- Restriction preserves the endpoint value. -/
theorem evalEnd_excursionRestrict (a : ℝ≥0) (e : Excursion) :
    evalEnd a (excursionRestrict a e) = e.path.1 a := rfl

/-- The endpoint coordinate is measurable. -/
theorem measurable_evalEnd (a : ℝ≥0) : Measurable (evalEnd a) := measurable_eval _

/-- Almost sure positivity of the endpoint under the tail prefix law. -/
theorem ae_evalEnd_pos_tailPrefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ∀ᵐ x ∂(tailPrefix θ a), 0 < evalEnd a x := by
  rw [tailPrefix, ae_map_iff (measurable_excursionRestrict a).aemeasurable
    (measurableSet_lt measurable_const (measurable_evalEnd a))]
  filter_upwards [ae_tailExcursionLaw_support hθ] with e he
  exact he.2.1 a ha.1 (ha.2.trans he.1)

/-- Size-tail identity from the remaining lifetime and Kendall's tail kernel. -/
theorem excursionTail_size_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) (F : D (a : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ e, F (excursionRestrict a e) ∂(excursionTail θ 1) =
      ∫⁻ e, F (excursionRestrict a e) *
        sizeTailKernelENN θ (1 - a) (e.path.1 a) ∂(excursionTail θ a) := by
  classical
  let r : ℝ := 1 - a
  have hr : 0 ≤ r := sub_nonneg.mpr (show (a : ℝ) ≤ 1 from ha.2.le)
  have hs1 : MeasurableSet {e : Excursion | 1 < (e.lifetime : ℝ)} :=
    measurableSet_lt measurable_const measurable_excursion_lifetime.coe_nnreal_real
  have hrem := excursion_remainingLifetime_lintegral hθ a ha.1 F hF
    ((Ioi r).indicator 1) (measurable_const.indicator measurableSet_Ioi)
  simp only [lintegral_indicator_one measurableSet_Ioi] at hrem
  have hleft : (∫⁻ e in {e : Excursion | a < e.lifetime},
      F (excursionRestrict a e) * (Ioi r).indicator 1 ((e.lifetime : ℝ) - a)
      ∂excursionMeasure θ) = ∫⁻ e, F (excursionRestrict a e) ∂excursionTail θ 1 := by
    calc
      _ = ∫⁻ e in {e : Excursion | a < e.lifetime},
          {e : Excursion | 1 < (e.lifetime : ℝ)}.indicator
            (fun e => F (excursionRestrict a e)) e ∂excursionMeasure θ := by
        apply lintegral_congr
        intro e
        change F (excursionRestrict a e) *
          (if r < (e.lifetime : ℝ) - a then 1 else 0) =
          if 1 < (e.lifetime : ℝ) then F (excursionRestrict a e) else 0
        by_cases he : 1 < (e.lifetime : ℝ)
        · have h : r < (e.lifetime : ℝ) - a := by dsimp [r]; linarith
          simp [he, h]
        · have h : ¬r < (e.lifetime : ℝ) - a := by dsimp [r]; linarith
          simp [he, h]
      _ = _ := by
        rw [lintegral_indicator hs1, Measure.restrict_restrict hs1]
        have hset : {e : Excursion | 1 < (e.lifetime : ℝ)} ∩
            {e : Excursion | a < e.lifetime} = {e : Excursion | 1 < (e.lifetime : ℝ)} := by
          apply inter_eq_left.mpr
          intro e he
          have : (a : ℝ) < (e.lifetime : ℝ) := (show (a : ℝ) < 1 from ha.2).trans he
          exact this
        rw [hset]
        rfl
  rw [hleft] at hrem
  rw [hrem]
  apply lintegral_congr_ae
  have hj := ae_valueNN_pos hθ a ha.1
  filter_upwards [hj] with e he
  rw [← sizeTailKernelENN_eq_passageLaw hθ hr (e.valueNN a) he, Excursion.coe_valueNN]

/- `gammaA` is the literal real quotient. Its values for `x ≤ 0`
are unused and need not be zero. A zero denominator gives zero;
a nonintegrable Bochner denominator is also totalized to zero.
On `a < 1`, `x > 0`, `sizeTailKernelENN_eq_passageLaw` and `sizeTailKernel_pos` identify
the denominator with the finite, strictly positive passage-time tail. -/

/-- Measurability of the Gamma density on the prefix space. -/
theorem measurable_gammaA_evalEnd (θ : ℝ) (a : ℝ≥0) :
    Measurable (fun x => ENNReal.ofReal (gammaA θ a (evalEnd a x))) :=
  (((measurable_gammaA θ).comp (measurable_const.prodMk (measurable_evalEnd a))).ennreal_ofReal)

/-- Gamma-weighted tail prefix integrals equal unit-prefix integrals. -/
theorem lintegral_gamma_identity_path {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) (F : D (a : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(unitPrefix θ a) =
      ∫⁻ x, F x * ENNReal.ofReal (gammaA θ a (evalEnd a x)) ∂(tailPrefix θ a) := by
  have hG : 0 < Real.Gamma (1 - 1 / θ) := Real.Gamma_pos_of_pos
    (sub_pos.mpr ((div_lt_one (show 0 < θ by linarith [hθ.1])).mpr hθ.1))
  have hcoef : ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) * ENNReal.ofReal θ =
      (ENNReal.ofReal (Scalar.stableDensity θ 0))⁻¹ := by
    rw [← ENNReal.ofReal_mul hG.le,
      ← ENNReal.ofReal_inv_of_pos (Scalar.stableDensity_zero_pos hθ)]
    congr 1
    simp only [stableDensity_zero_eq_inv_theta_gamma hθ, one_div, inv_inv, mul_comm]
  have htest : Measurable (fun x => F x * ENNReal.ofReal (gammaA θ a (evalEnd a x))) :=
    hF.mul (measurable_gammaA_evalEnd θ a)
  have hmap := lintegral_map htest (measurable_excursionRestrict a)
    (μ := (tailExcursionLaw θ : Measure Excursion))
  have hright : (∫⁻ x, F x * ENNReal.ofReal (gammaA θ a (evalEnd a x)) ∂tailPrefix θ a) =
      ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) *
        ∫⁻ e, F (excursionRestrict a e) * ENNReal.ofReal (gammaA θ a (e.path.1 a))
          ∂excursionTail θ 1 := by
    change (∫⁻ x, F x * ENNReal.ofReal (gammaA θ a (evalEnd a x))
      ∂(tailExcursionLaw θ : Measure Excursion).map (excursionRestrict a)) = _
    rw [hmap, coe_tailExcursionLaw hθ, tailExcursionMeasure, lintegral_smul_measure,
      smul_eq_mul]
    rfl
  rw [hright]
  have htail := excursionTail_size_tail hθ a ha _ htest
  simp only [evalEnd_excursionRestrict] at htail
  rw [htail]
  have heq : (∫⁻ e, F (excursionRestrict a e) * ENNReal.ofReal (gammaA θ a (e.path.1 a)) *
      sizeTailKernelENN θ (1 - a) (e.path.1 a) ∂excursionTail θ a) =
      ENNReal.ofReal θ * ∫⁻ e, F (excursionRestrict a e) *
        ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a)) ∂excursionTail θ a := by
    calc
      _ = ∫⁻ e, ENNReal.ofReal θ * (F (excursionRestrict a e) *
          ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a))) ∂excursionTail θ a := by
        apply lintegral_congr_ae
        have hj := ae_valueNN_pos hθ a ha.1
        filter_upwards [hj] with e he
        have hx : 0 < e.path.1 a := by simpa only [Excursion.coe_valueNN] using
          (show (0 : ℝ) < e.valueNN a from he)
        have hs : 0 < sizeTailKernel θ (1 - a) (e.path.1 a) :=
          sizeTailKernel_pos hθ (sub_pos.mpr ha.2) hx
        have hg : 0 ≤ gammaA θ a (e.path.1 a) := gammaA_nonneg hθ ha.2 hx
        rw [← ofReal_sizeTailKernel hθ
          (sub_nonneg.mpr (show (a : ℝ) ≤ 1 from ha.2.le)) hx, mul_assoc,
          ← ENNReal.ofReal_mul hg, gammaA_mul_sizeTail hs,
          ENNReal.ofReal_mul (show 0 ≤ θ by linarith [hθ.1])]
        ac_rfl
      _ = _ := lintegral_const_mul _ (by
        exact (hF.comp (measurable_excursionRestrict a)).mul (measurable_prefixDensity θ a))
  rw [heq, ← mul_assoc, hcoef]
  exact lintegral_unitPrefix_eq hθ a ha F hF

/- Path-only Gamma identity, including theta = 2.
Joint height tests require H04's common measurable prefix graph.
Identification with the classical Brownian excursion law requires CT8. -/

/-- The unit prefix is obtained by weighting the tail prefix by Gamma. -/
theorem levyExcLaw_prefix_eq_withDensity_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    unitPrefix θ a =
      (tailPrefix θ a).withDensity (fun x => ENNReal.ofReal (gammaA θ a (evalEnd a x))) := by
  apply Measure.ext_of_lintegral
  intro F hF
  rw [lintegral_withDensity_eq_lintegral_mul _ (measurable_gammaA_evalEnd θ a) hF]
  exact (lintegral_gamma_identity_path hθ a ha F hF).trans
    (lintegral_congr fun x => mul_comm _ _)

/-- Gamma is integrable under the tail prefix law and has expectation one. -/
theorem integral_gammaA_tail_eq_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Integrable (fun x => gammaA θ a (evalEnd a x)) (tailPrefix θ a) ∧
      ∫ x, gammaA θ a (evalEnd a x) ∂(tailPrefix θ a) = 1 := by
  have hm : Measurable (fun x => gammaA θ a (evalEnd a x)) :=
    (measurable_gammaA θ).comp (measurable_const.prodMk (measurable_evalEnd a))
  have hn : 0 ≤ᵐ[tailPrefix θ a] fun x => gammaA θ a (evalEnd a x) := by
    filter_upwards [ae_evalEnd_pos_tailPrefix hθ a ha] with x hx
    exact gammaA_nonneg hθ ha.2 hx
  have hmass := lintegral_gamma_identity_path hθ a ha (fun _ => 1) measurable_const
  have hP : IsProbabilityMeasure (unitPrefix θ a) := by unfold unitPrefix; infer_instance
  simp only [one_mul, lintegral_one, measure_univ] at hmass
  have hi : Integrable (fun x => gammaA θ a (evalEnd a x)) (tailPrefix θ a) :=
    (lintegral_ofReal_ne_top_iff_integrable hm.aestronglyMeasurable hn).mp
      (by rw [← hmass]; exact ENNReal.one_ne_top)
  refine ⟨hi, ?_⟩
  have heq := congrArg ENNReal.toReal hmass
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn,
    ENNReal.toReal_ofReal (integral_nonneg_of_ae hn)] at heq
  exact heq.symm

/-- Bounded signed path tests satisfy the Gamma identity. -/
theorem gamma_identity_path {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) (F : D (a : ℝ) ℝ → ℝ) (hF : Measurable F)
    (hb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    (∫ x, F x ∂(unitPrefix θ a)) =
      ∫ x, F x * gammaA θ a (evalEnd a x) ∂(tailPrefix θ a) := by
  -- The measure formula holds for all real tests, via totalized integrals.
  -- `hb` and `hF` are part of the stated interface (bounded measurable tests); the proof
  -- uses the nonnegative identity.
  have _hb := hb
  have _hF := hF
  rw [levyExcLaw_prefix_eq_withDensity_tail hθ a ha,
    integral_withDensity_eq_integral_toReal_smul (measurable_gammaA_evalEnd θ a)
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [ae_evalEnd_pos_tailPrefix hθ a ha] with x hx
  have hn : 0 ≤ gammaA θ (a : ℝ) (evalEnd a x) := gammaA_nonneg hθ ha.2 hx
  rw [ENNReal.toReal_ofReal hn, smul_eq_mul, mul_comm]

end BGW.StableTrees
