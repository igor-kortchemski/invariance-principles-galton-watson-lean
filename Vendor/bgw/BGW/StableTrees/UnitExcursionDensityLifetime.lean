/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionLaw
public import BGW.StableTrees.KendallAdapter
import BGW.StableTrees.ExcursionMarkov
import Mathlib.MeasureTheory.Function.AEEqOfLIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Prefix densities at almost every lifetime

The remaining-lifetime identity and Kendall's density give the prefix/lifetime
joint integral. Comparing it with the lifetime mixture proves the density identity
for each fixed nonnegative measurable prefix test.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

private theorem passage_lintegral_shift {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (x : ℝ≥0) (hx : 0 < x) (a : ℝ) (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ s, g (s + a) ∂passageLaw θ x) =
      ∫⁻ u in Ioi a, g u * ENNReal.ofReal (qKernel θ (u - a) x) := by
  have hd : Measurable (fun s : ℝ =>
      ENNReal.ofReal (if 0 < s then qKernel θ s x else 0)) :=
    (Measurable.ite measurableSet_Ioi
      ((measurable_qKernel θ).comp (measurable_id.prodMk measurable_const))
      measurable_const).ennreal_ofReal
  rw [passageLaw_eq_qKernel hθ x hx,
    lintegral_withDensity_eq_lintegral_mul _ hd]
  · have heq : (fun s : ℝ => ENNReal.ofReal (if 0 < s then qKernel θ s x else 0) *
        g (s + a)) = fun s => (Ioi a).indicator
          (fun u => g u * ENNReal.ofReal (qKernel θ (u - a) x)) (s + a) := by
      funext s
      by_cases hs : 0 < s
      · simp [hs, show a < s + a by linarith, mul_comm]
      · simp [hs, show ¬a < s + a by linarith]
    simp only [Pi.mul_apply]
    change (∫⁻ s, ENNReal.ofReal (if 0 < s then qKernel θ s x else 0) * g (s + a)) = _
    rw [heq, lintegral_add_right_eq_self, lintegral_indicator measurableSet_Ioi]
  · exact hg.comp (measurable_id.add_const a)

/-- The remaining-lifetime law expressed as a density in the full lifetime. -/
theorem prefix_lifetime_lintegral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : 0 < a) (F : D (a : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    (∫⁻ e in {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)},
      F (excursionRestrict a e) * g e.lifetime ∂excursionMeasure θ) =
    ∫⁻ u in Ioi (a : ℝ), g u *
      ∫⁻ e in {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)},
        F (excursionRestrict a e) *
          ENNReal.ofReal (qKernel θ (u - a) (e.path.1 a)) ∂excursionMeasure θ := by
  have hmark := excursion_remainingLifetime_lintegral hθ a ha F hF
    (fun s => g (s + a)) (hg.comp (measurable_id.add_const _))
  simp only [sub_add_cancel] at hmark
  simp only [NNReal.coe_lt_coe] at ⊢
  rw [hmark]
  let μ : Measure Excursion :=
    (excursionMeasure θ).restrict {e : Excursion | a < e.lifetime}
  let _ : IsFiniteMeasure μ := isFiniteMeasure_excursionMeasure_survival hθ a ha
  have hm : Measurable (fun p : Excursion × ℝ =>
      g p.2 * (F (excursionRestrict a p.1) *
        ENNReal.ofReal (qKernel θ (p.2 - a) (p.1.path.1 a)))) :=
    (hg.comp measurable_snd).mul
      ((hF.comp ((measurable_excursionRestrict a).comp measurable_fst)).mul
        (((measurable_qKernel θ).comp
          ((measurable_snd.sub measurable_const).prodMk
            ((measurable_excursion_eval a).comp measurable_fst))).ennreal_ofReal))
  calc
    _ = ∫⁻ e, F (excursionRestrict a e) *
        (∫⁻ u in Ioi (a : ℝ), g u *
          ENNReal.ofReal (qKernel θ (u - a) (e.path.1 a))) ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [ae_valueNN_pos hθ a ha] with e he
      rw [passage_lintegral_shift hθ _ he _ _ hg]
      simp only [Excursion.coe_valueNN]
    _ = ∫⁻ e, (∫⁻ u in Ioi (a : ℝ), g u *
        (F (excursionRestrict a e) *
          ENNReal.ofReal (qKernel θ (u - a) (e.path.1 a)))) ∂μ := by
      apply lintegral_congr
      intro e
      have hk : Measurable (fun u : ℝ => g u *
          ENNReal.ofReal (qKernel θ (u - a) (e.path.1 a))) :=
        hg.mul (((measurable_qKernel θ).comp
          ((measurable_id.sub_const (a : ℝ)).prodMk
            (measurable_const : Measurable (fun _ : ℝ => e.path.1 a)))).ennreal_ofReal)
      exact (lintegral_const_mul (F (excursionRestrict a e)) hk).symm.trans
        (lintegral_congr fun u => by ac_rfl)
    _ = _ := by
      rw [lintegral_lintegral_swap hm.aemeasurable]
      apply lintegral_congr
      intro u
      have hk : Measurable (fun e : Excursion => F (excursionRestrict a e) *
          ENNReal.ofReal (qKernel θ (u - a) (e.path.1 a))) :=
        (hF.comp (measurable_excursionRestrict a)).mul
          (((measurable_qKernel θ).comp
            ((measurable_const : Measurable (fun _ : Excursion => u - (a : ℝ))).prodMk
              (measurable_excursion_eval a))).ennreal_ofReal)
      exact lintegral_const_mul (g u) hk

private theorem setLIntegral_volIoi_above (a : ℝ) (ha : 0 ≤ a) (f : ℝ → ℝ≥0∞) :
    (∫⁻ u in {u : Ioi (0 : ℝ) | a < (u : ℝ)}, f u ∂volIoi) =
      ∫⁻ u in Ioi a, f u := by
  change (∫⁻ u in {u : Ioi (0 : ℝ) | a < (u : ℝ)}, f u
    ∂Measure.comap Subtype.val volume) = _
  rw [setLIntegral_subtype measurableSet_Ioi]
  have heq : Subtype.val '' {u : Ioi (0 : ℝ) | a < (u : ℝ)} = Ioi a := by
    ext u
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hu
      exact ⟨⟨u, ha.trans_lt hu⟩, hu, rfl⟩
  rw [heq]

/-- The density identity for each fixed nonnegative measurable prefix test. -/
theorem prefix_density_ae_lifetime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) (ha : 0 < a)
    (F : D (a : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∀ᵐ u : Set.Ioi (0 : ℝ) ∂(volIoi.restrict {u : Set.Ioi (0 : ℝ) | (a : ℝ) < (u : ℝ)}),
      lifetimeDensity θ (u : ℝ) * ∫⁻ e, F (excursionRestrict a e) ∂(excursionAt θ u) =
        ∫⁻ e in {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)},
          F (excursionRestrict a e) *
            ENNReal.ofReal (qKernel θ ((u : ℝ) - a) (e.path.1 a)) ∂(excursionMeasure θ) := by
  let _ : SigmaFinite (excursionMeasure θ) := sigmaFinite_excursionMeasure hθ
  let _ : SigmaFinite volIoi := sigmaFinite_volIoi
  let L : Ioi (0 : ℝ) → ℝ≥0∞ := fun u =>
    lifetimeDensity θ u * ∫⁻ e, F (excursionRestrict a e) ∂excursionAt θ u
  let R : ℝ → ℝ≥0∞ := fun u =>
    ∫⁻ e in {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)},
      F (excursionRestrict a e) * ENNReal.ofReal (qKernel θ (u - a) (e.path.1 a))
        ∂excursionMeasure θ
  have hscale : Measurable (fun p : Ioi (0 : ℝ) × Excursion =>
      F (excursionRestrict a (excursionScale θ p.1 p.2))) :=
    hF.comp ((measurable_excursionRestrict a).comp (measurable_excursionScale_joint θ))
  have hL : Measurable L := by
    have hm : Measurable (fun u : Ioi (0 : ℝ) =>
        ∫⁻ e, F (excursionRestrict a e) ∂excursionAt θ u) := by
      have hi (u : Ioi (0 : ℝ)) :
          (∫⁻ e, F (excursionRestrict a e) ∂excursionAt θ u) =
          ∫⁻ e, F (excursionRestrict a (excursionScale θ u e))
            ∂(unitExcursionLaw θ : Measure Excursion) :=
        lintegral_map (hF.comp (measurable_excursionRestrict a)) (measurable_excursionScale θ u)
      simp_rw [hi]
      exact hscale.lintegral_prod_right'
    have hd := measurable_lifetimeDensity θ
    exact hd.mul hm
  have hR : Measurable R := by
    have hm : Measurable (fun p : ℝ × Excursion =>
        F (excursionRestrict a p.2) *
          ENNReal.ofReal (qKernel θ (p.1 - a) (p.2.path.1 a))) :=
      (hF.comp ((measurable_excursionRestrict a).comp measurable_snd)).mul
        (((measurable_qKernel θ).comp
          ((measurable_fst.sub_const (a : ℝ)).prodMk
            ((measurable_excursion_eval a).comp measurable_snd))).ennreal_ofReal)
    exact hm.lintegral_prod_right' (ν := (excursionMeasure θ).restrict
      {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)})
  have htest (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
      (∫⁻ u in {u : Ioi (0 : ℝ) | (a : ℝ) < (u : ℝ)}, g u * L u ∂volIoi) =
      ∫⁻ u in {u : Ioi (0 : ℝ) | (a : ℝ) < (u : ℝ)}, g u * R u ∂volIoi := by
    have hmix := setLIntegral_excursionMeasure_eq_mixture hθ
      ((hF.comp (measurable_excursionRestrict a)).mul
        (hg.comp measurable_excursion_lifetime.coe_nnreal_real)) (a : ℝ) a.2
    simp only [Pi.mul_apply, Function.comp_apply] at hmix
    have hm : (∫⁻ u in {u : Ioi (0 : ℝ) | (a : ℝ) < (u : ℝ)}, g u * L u ∂volIoi) =
        ∫⁻ e in {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)},
          F (excursionRestrict a e) * g e.lifetime ∂excursionMeasure θ := by
      rw [hmix]
      apply lintegral_congr
      intro u
      have heq : (∫⁻ e, F (excursionRestrict a e) * g e.lifetime ∂excursionAt θ u) =
          (∫⁻ e, F (excursionRestrict a e) ∂excursionAt θ u) * g u := by
        calc
          _ = ∫⁻ e, F (excursionRestrict a e) * g u ∂excursionAt θ u := by
            apply lintegral_congr_ae
            filter_upwards [ae_lifetime_excursionAt hθ u] with e he
            rw [he]
          _ = _ := lintegral_mul_const _ (hF.comp (measurable_excursionRestrict a))
      rw [heq]
      dsimp [L]
      ac_rfl
    rw [hm, prefix_lifetime_lintegral hθ a ha F hF g hg,
      setLIntegral_volIoi_above (a : ℝ) a.2 (fun u => g u * R u)]
  apply ae_eq_of_forall_setLIntegral_eq_of_sigmaFinite hL
    (hR.comp measurable_subtype_coe)
  intro B hB _
  let C : Set ℝ := Subtype.val '' B
  have hC : MeasurableSet C :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ioi).measurableSet_image.mpr hB
  have h := htest (C.indicator 1) (measurable_const.indicator hC)
  have hind (u : Ioi (0 : ℝ)) : C.indicator (1 : ℝ → ℝ≥0∞) u = B.indicator 1 u := by
    by_cases hu : u ∈ B
    · rw [Set.indicator_of_mem (Set.mem_image_of_mem _ hu), Set.indicator_of_mem hu]
      rfl
    · have hn : (u : ℝ) ∉ C := by
        rintro ⟨v, hv, heq⟩
        exact hu (Subtype.ext heq ▸ hv)
      rw [Set.indicator_of_notMem hn, Set.indicator_of_notMem hu]
  simp_rw [hind] at h
  have hindmul (f : Ioi (0 : ℝ) → ℝ≥0∞) :
      (fun u => B.indicator 1 u * f u) = B.indicator f := by
    funext u
    by_cases hu : u ∈ B <;> simp [hu]
  simp_rw [hindmul] at h
  simpa only [Function.comp_apply, lintegral_indicator hB] using h

end BGW.StableTrees
