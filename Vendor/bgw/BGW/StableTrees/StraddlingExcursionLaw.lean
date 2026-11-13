/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StraddlingExcursionCompensation
import Mathlib.MeasureTheory.Measure.Typeclasses.NullSingletonClass
import Mathlib.Probability.Independence.Basic

/-!
# Law of the excursion straddling a fixed time

Predictable compensation and the passage potential identify the joint law of the start,
lifetime and normalized shape. The normalized shape is independent of the first two
coordinates, and the start has the generalized arcsine density.

## References

J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees
private theorem lintegral_lebNN_passage_potential {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {F : ℝ → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ x, ∫⁻ f, F (passageTime x f)
      ∂(stableLocalLaw θ : Measure DLoc) ∂lebNN =
      ∫⁻ s, straddleAgeDensity θ s * F s := by
  have hc : (∫⁻ x, ∫⁻ f, F (passageTime x f)
      ∂(stableLocalLaw θ : Measure DLoc) ∂lebNN) =
      ∫⁻ x in Ioi (0 : ℝ), ∫⁻ f, F (passageTime x.toNNReal f)
        ∂(stableLocalLaw θ : Measure DLoc) := by
    rw [restrict_Ioi_eq_restrict_Ici]
    have he := lintegral_subtype_comap (μ := (volume : Measure ℝ))
      (s := Ici (0 : ℝ)) measurableSet_Ici
      (fun x : ℝ => ∫⁻ f, F (passageTime x.toNNReal f)
        ∂(stableLocalLaw θ : Measure DLoc))
    change (∫⁻ x : ℝ≥0, ∫⁻ f, F (passageTime (x : ℝ).toNNReal f)
      ∂(stableLocalLaw θ : Measure DLoc) ∂lebNN) = _ at he
    simpa only [Real.toNNReal_coe] using he
  rw [hc]
  exact lintegral_passage_potential hθ hF

private noncomputable def straddleKernel (θ : ℝ) (t : ℝ≥0)
    (F : (ℝ × ℝ) × Excursion → ℝ≥0∞) (g : ℝ) (e : Excursion) : ℝ≥0∞ :=
  if g < t ∧ (t : ℝ) < g + e.lifetime then
    F ((g, (e.lifetime : ℝ)), normalizeExc θ e) else 0

private theorem measurable_straddleKernel (θ : ℝ) (t : ℝ≥0)
    {F : (ℝ × ℝ) × Excursion → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : ℝ × Excursion => straddleKernel θ t F p.1 p.2) := by
  have hl : Measurable (fun p : ℝ × Excursion => (p.2.lifetime : ℝ)) :=
    (measurable_excursion_lifetime.comp measurable_snd).coe_nnreal_real
  exact (hF.comp ((measurable_fst.prodMk hl).prodMk
    ((measurable_normalizeExc θ).comp measurable_snd))).ite
      ((measurableSet_lt measurable_fst measurable_const).inter
        (measurableSet_lt measurable_const (measurable_fst.add hl))) measurable_const

private theorem straddle_integral_potential {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) {F : (ℝ × ℝ) × Excursion → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ f, F (straddleData θ t f) ∂(stableLocalLaw θ : Measure DLoc) =
      ∫⁻ g, straddleAgeDensity θ g * ∫⁻ e, straddleKernel θ t F g e
        ∂excursionMeasure θ := by
  let := sigmaFinite_excursionMeasure hθ
  let := sigmaFinite_lebNN
  let K : ℝ → ℝ≥0∞ := fun g => ∫⁻ e, straddleKernel θ t F g e ∂excursionMeasure θ
  have hK : Measurable K := (measurable_straddleKernel θ t hF).lintegral_prod_right'
  have hminus : Measurable (fun p : DLoc × ℝ≥0 => K (passageTimeMinus p.2 p.1)) :=
    hK.comp ((measurable_passageTimeMinus_uncurry.comp measurable_swap).coe_nnreal_real)
  rw [lintegral_straddleData_compensation θ hθ ht hF]
  change (∫⁻ f, ∫⁻ x, K (passageTimeMinus x f) ∂lebNN
    ∂(stableLocalLaw θ : Measure DLoc)) = _
  rw [lintegral_lintegral_swap hminus.aemeasurable]
  calc
    _ = ∫⁻ x, ∫⁻ f, K (passageTime x f)
        ∂(stableLocalLaw θ : Measure DLoc) ∂lebNN := by
      apply lintegral_congr_ae
      filter_upwards [] with x
      apply lintegral_congr_ae
      filter_upwards [ae_passageTimeMinus_eq_passageTime hθ x] with f hf
      rw [hf]
    _ = _ := lintegral_lebNN_passage_potential hθ hK

private noncomputable def shapeKernel (t : ℝ≥0)
    (F : (ℝ × ℝ) × Excursion → ℝ≥0∞) (g u : ℝ) (e : Excursion) : ℝ≥0∞ :=
  if g < t ∧ (t : ℝ) < g + u then F ((g, u), e) else 0

private theorem measurable_shapeKernel (t : ℝ≥0)
    {F : (ℝ × ℝ) × Excursion → ℝ≥0∞} (hF : Measurable F) :
    Measurable (fun p : (ℝ × ℝ) × Excursion => shapeKernel t F p.1.1 p.1.2 p.2) := by
  exact hF.ite
    ((measurableSet_lt (measurable_fst.comp measurable_fst) measurable_const).inter
      (measurableSet_lt measurable_const ((measurable_fst.comp measurable_fst).add
        (measurable_snd.comp measurable_fst)))) measurable_const

private theorem kernel_lifetime_shape {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    {F : (ℝ × ℝ) × Excursion → ℝ≥0∞} (hF : Measurable F) (g : ℝ) :
    ∫⁻ e, straddleKernel θ t F g e ∂excursionMeasure θ =
      ∫⁻ u, ∫⁻ e, shapeKernel t F g u e
        ∂(unitExcursionLaw θ : Measure Excursion) ∂lifetimeLaw θ := by
  let := sigmaFinite_lifetimeLaw θ
  have hp : Measurable (fun p : Ioi (0 : ℝ) × Excursion => ((g, (p.1 : ℝ)), p.2)) :=
    (measurable_const.prodMk (measurable_subtype_coe.comp measurable_fst)).prodMk measurable_snd
  have hm : Measurable (fun p : Ioi (0 : ℝ) × Excursion => shapeKernel t F g p.1 p.2) :=
    (measurable_shapeKernel t hF).comp hp
  rw [← lintegral_prod _ hm.aemeasurable, ← shapeLifetime_map_excursionMeasure hθ,
    lintegral_map hm (measurable_shapeLifetime θ)]
  rfl

private theorem age_shape_density {θ : ℝ} (t : ℝ≥0)
    {F : (ℝ × ℝ) × Excursion → ℝ≥0∞} (hF : Measurable F) (g : ℝ) :
    straddleAgeDensity θ g * (∫⁻ u, ∫⁻ e, shapeKernel t F g u e
      ∂(unitExcursionLaw θ : Measure Excursion) ∂lifetimeLaw θ) =
    ∫⁻ u, straddleDensity θ t (g, u) * ∫⁻ e, F ((g, u), e)
      ∂(unitExcursionLaw θ : Measure Excursion) := by
  have hm : Measurable (fun p : ℝ × Excursion => shapeKernel t F g p.1 p.2) :=
    (measurable_shapeKernel t hF).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  have hl := measurable_lifetimeDensity θ
  have hh : Measurable (fun u : Ioi (0 : ℝ) =>
      ∫⁻ e, shapeKernel t F g u e ∂(unitExcursionLaw θ : Measure Excursion)) :=
    hm.lintegral_prod_right'.comp measurable_subtype_coe
  rw [lifetimeLaw, lintegral_withDensity_eq_lintegral_mul _ hl hh]
  change straddleAgeDensity θ g * (∫⁻ u : Ioi (0 : ℝ), lifetimeDensity θ u *
    ∫⁻ e, shapeKernel t F g u e ∂(unitExcursionLaw θ : Measure Excursion) ∂volIoi) = _
  rw [volIoi]
  have hsub := lintegral_subtype_comap (μ := (volume : Measure ℝ))
    (s := Ioi (0 : ℝ)) measurableSet_Ioi
    (fun u : ℝ => lifetimeDensity θ u * ∫⁻ e, shapeKernel t F g u e
      ∂(unitExcursionLaw θ : Measure Excursion))
  rw [hsub]
  have hn : straddleAgeDensity θ g ≠ ⊤ := by
    by_cases hg : g ∈ Ioi (0 : ℝ)
    · simp only [straddleAgeDensity, indicator_of_mem hg]
      exact ENNReal.ofReal_ne_top
    · simp only [straddleAgeDensity, indicator_of_notMem hg]
      exact ENNReal.zero_ne_top
  rw [← lintegral_const_mul' _ _ hn, ← lintegral_indicator measurableSet_Ioi]
  apply lintegral_congr_ae
  filter_upwards [] with u
  by_cases hg : 0 < g
  · by_cases hgt : g < (t : ℝ)
    · by_cases htu : (t : ℝ) < g + u
      · have hu : 0 < u := by linarith
        simp [straddleDensity, shapeKernel, hg, hgt, htu, hu, mul_assoc]
      · simp [straddleDensity, shapeKernel, hg, hgt, htu]
    · simp [straddleDensity, shapeKernel, hg, hgt]
  · simp [straddleDensity, straddleAgeDensity, hg]

private theorem straddle_integral_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) {F : (ℝ × ℝ) × Excursion → ℝ≥0∞}
    (hF : Measurable F) :
    ∫⁻ f, F (straddleData θ t f) ∂(stableLocalLaw θ : Measure DLoc) =
      ∫⁻ g, ∫⁻ u, straddleDensity θ t (g, u) * ∫⁻ e, F ((g, u), e)
        ∂(unitExcursionLaw θ : Measure Excursion) := by
  rw [straddle_integral_potential hθ ht hF]
  apply lintegral_congr_ae
  filter_upwards [] with g
  rw [kernel_lifetime_shape hθ t hF g]
  exact age_shape_density t hF g

private theorem measurable_straddleDensity (θ : ℝ) (t : ℝ≥0) :
    Measurable (straddleDensity θ t) := by
  have ha : Measurable (straddleAgeDensity θ) := by
    unfold straddleAgeDensity
    apply Measurable.indicator _ measurableSet_Ioi
    fun_prop
  have hl : Measurable (lifetimeDensity θ) := by unfold lifetimeDensity; fun_prop
  apply ((ha.comp measurable_fst).mul (hl.comp measurable_snd)).indicator
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst measurable_const).inter
      (measurableSet_lt measurable_const (measurable_fst.add measurable_snd)))

/-- **Joint law** (path part): `((g_t, d_t - g_t), normalized straddling excursion)` has
the product law `straddleLaw ⊗ unitExcursionLaw`: the normalized excursion is independent of
`(g_t, d_t)` with the unit excursion law, and `(g_t, ζ_t)` has the explicit density from
compensation and the lifetime density. -/
theorem map_straddleData_eq_prod {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (straddleData θ t) (stableLocalLaw θ : Measure DLoc) =
      (straddleLaw θ t).prod (unitExcursionLaw θ : Measure Excursion) := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_map' hF.aemeasurable (aemeasurable_straddleData hθ t),
    straddle_integral_density hθ ht hF]
  rw [lintegral_prod _ hF.aemeasurable, straddleLaw,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_straddleDensity θ t)
      hF.lintegral_prod_right']
  change (∫⁻ g, ∫⁻ u, straddleDensity θ t (g, u) * ∫⁻ e, F ((g, u), e)
      ∂(unitExcursionLaw θ : Measure Excursion)) =
    ∫⁻ p, straddleDensity θ t p * ∫⁻ e, F (p, e)
      ∂(unitExcursionLaw θ : Measure Excursion) ∂(volume.prod volume)
  exact (lintegral_prod _ ((measurable_straddleDensity θ t).mul
    hF.lintegral_prod_right').aemeasurable).symm

/-- **Law of `(g_t, ζ_t)`** is `straddleLaw`. -/
theorem map_straddleAgeLife_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (fun f => ((straddleStart t f : ℝ), straddleLife t f))
        (stableLocalLaw θ : Measure DLoc) = straddleLaw θ t := by
  calc
    _ = Measure.map Prod.fst (Measure.map (straddleData θ t)
        (stableLocalLaw θ : Measure DLoc)) :=
      (measurable_fst.aemeasurable.map_map_of_aemeasurable
        (aemeasurable_straddleData hθ t)).symm
    _ = _ := by rw [map_straddleData_eq_prod hθ ht]; simp

/-- The claimed law of `(g_t, ζ_t)` is a probability measure (Beta integral). -/
theorem isProbabilityMeasure_straddleLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    IsProbabilityMeasure (straddleLaw θ t) := by
  rw [← map_straddleAgeLife_eq hθ ht]
  infer_instance

/-- **Blueprint statement**: `normalizeExc` of the straddling excursion has the unit law. -/
theorem map_normalize_straddling_eq_unitExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (fun f => normalizeExc θ (straddlingExcursion t f))
        (stableLocalLaw θ : Measure DLoc) =
      (unitExcursionLaw θ : Measure Excursion) := by
  let := isProbabilityMeasure_straddleLaw hθ ht
  calc
    _ = Measure.map Prod.snd (Measure.map (straddleData θ t)
        (stableLocalLaw θ : Measure DLoc)) :=
      (measurable_snd.aemeasurable.map_map_of_aemeasurable
        (aemeasurable_straddleData hθ t)).symm
    _ = _ := by rw [map_straddleData_eq_prod hθ ht]; simp

/-- **Independence** of `(g_t, ζ_t)` and the normalized straddling excursion. -/
theorem indepFun_straddle_age_shape {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    IndepFun (fun f => ((straddleStart t f : ℝ), straddleLife t f))
      (fun f => normalizeExc θ (straddlingExcursion t f))
      (stableLocalLaw θ : Measure DLoc) := by
  apply (indepFun_iff_map_prod_eq_prod_map_map (aemeasurable_straddleData hθ t).fst
    (aemeasurable_straddleData hθ t).snd).mpr
  change Measure.map (straddleData θ t) (stableLocalLaw θ : Measure DLoc) =
    (Measure.map (fun f => ((straddleStart t f : ℝ), straddleLife t f))
      (stableLocalLaw θ : Measure DLoc)).prod
      (Measure.map (fun f => normalizeExc θ (straddlingExcursion t f))
        (stableLocalLaw θ : Measure DLoc))
  rw [map_straddleAgeLife_eq hθ ht, map_normalize_straddling_eq_unitExcursionLaw hθ ht]
  exact map_straddleData_eq_prod hθ ht

/-- **Path version**: the normalized straddling excursion restricted to `[0,1]` has law
`levyExcLaw θ`. -/
theorem map_straddling_restrict_eq_levyExcLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    Measure.map (fun f => excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f)))
        (stableLocalLaw θ : Measure DLoc) = (levyExcLaw θ : Measure (D 1 ℝ)) := by
  calc
    _ = Measure.map (excursionRestrict 1) (Measure.map
        (fun f => normalizeExc θ (straddlingExcursion t f))
        (stableLocalLaw θ : Measure DLoc)) :=
      ((measurable_excursionRestrict 1).aemeasurable.map_map_of_aemeasurable
        (aemeasurable_straddleData hθ t).snd).symm
    _ = _ := by rw [map_normalize_straddling_eq_unitExcursionLaw hθ ht]; rfl

private theorem start_test_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    (F : ℝ → ℝ≥0∞) (g : ℝ) :
    straddleAgeDensity θ g * (∫⁻ e, straddleKernel θ t (fun p => F p.1.1) g e
      ∂excursionMeasure θ) = straddleStartDensity θ t g * F g := by
  by_cases hg : 0 < g
  · by_cases hgt : g < (t : ℝ)
    · have hset : MeasurableSet {e : Excursion | (t : ℝ) - g < (e.lifetime : ℝ)} :=
        measurableSet_lt measurable_const measurable_excursion_lifetime.coe_nnreal_real
      have hfun : (fun e => straddleKernel θ t (fun p => F p.1.1) g e) =
          {e : Excursion | (t : ℝ) - g < (e.lifetime : ℝ)}.indicator (fun _ => F g) := by
        funext e
        by_cases hc : (t : ℝ) < g + (e.lifetime : ℝ)
        · have hd : (t : ℝ) - g < (e.lifetime : ℝ) := by linarith
          simp [straddleKernel, hgt, hc, hd]
        · have hd : ¬ (t : ℝ) - g < (e.lifetime : ℝ) := by linarith
          simp [straddleKernel, hgt, hc, hd]
      rw [hfun, lintegral_indicator hset, setLIntegral_const,
        excursionMeasure_lifetime_tail hθ ((t : ℝ) - g) (sub_pos.mpr hgt)]
      have ha : 0 < 1 / θ := one_div_pos.mpr (lt_trans zero_lt_one hθ.1)
      have hGamma : 0 < Real.Gamma (1 / θ) := Real.Gamma_pos_of_pos ha
      have hdensity : straddleAgeDensity θ g *
          ENNReal.ofReal (((t : ℝ) - g) ^ (-(1 / θ)) / Real.Gamma (1 - 1 / θ)) =
          straddleStartDensity θ t g := by
        rw [straddleAgeDensity, indicator_of_mem (show g ∈ Ioi (0 : ℝ) from hg),
          straddleStartDensity,
          indicator_of_mem (show g ∈ Ioo (0 : ℝ) (t : ℝ) from ⟨hg, hgt⟩),
          ← ENNReal.ofReal_mul (div_nonneg (Real.rpow_nonneg hg.le _) hGamma.le)]
        congr 1
        ring
      calc
        _ = (straddleAgeDensity θ g * ENNReal.ofReal
          (((t : ℝ) - g) ^ (-(1 / θ)) / Real.Gamma (1 - 1 / θ))) * F g := by ac_rfl
        _ = _ := by rw [hdensity]
    · simp [straddleKernel, hgt, straddleStartDensity]
  · simp [straddleAgeDensity, hg, straddleStartDensity]

/-- **Generalized arcsine law of `g_t`**: `g_t/t ~ Beta(1/θ, 1-1/θ)`. -/
theorem map_straddleStart_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    Measure.map (fun f => (straddleStart t f : ℝ)) (stableLocalLaw θ : Measure DLoc) =
      volume.withDensity (straddleStartDensity θ t) := by
  have hm : Measurable (straddleStartDensity θ t) := by
    apply Measurable.indicator _ measurableSet_Ioo
    fun_prop
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  have hstart : AEMeasurable (fun f : DLoc => (straddleStart t f : ℝ))
      (stableLocalLaw θ : Measure DLoc) := (aemeasurable_straddleData hθ t).fst.fst
  rw [lintegral_map' hF.aemeasurable hstart]
  calc
    _ = ∫⁻ g, straddleAgeDensity θ g * ∫⁻ e,
        straddleKernel θ t (fun p => F p.1.1) g e ∂excursionMeasure θ :=
      straddle_integral_potential hθ ht (hF.comp (measurable_fst.comp measurable_fst))
    _ = ∫⁻ g, straddleStartDensity θ t g * F g := by
      apply lintegral_congr_ae
      exact Eventually.of_forall (start_test_integral hθ t F)
    _ = _ := (lintegral_withDensity_eq_lintegral_mul _ hm hF).symm

end BGW.StableTrees
