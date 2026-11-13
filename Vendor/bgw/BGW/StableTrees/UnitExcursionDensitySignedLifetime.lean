/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionDensityLifetime
import BGW.StableTrees.ExcursionMarkov

/-!
# Signed lifetime density comparison

Two nonnegative prefix tests give the signed integral identity whenever the
weighted test is integrable. The exceptional set depends on the fixed test.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- Signed integral comparison at almost every lifetime,
whenever the weighted test is integrable. -/
theorem prefix_density_ae_lifetime_integral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (a : ℝ≥0) (ha : 0 < a) (F : D (a : ℝ) ℝ → ℝ) (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∀ᵐ u : Ioi (0 : ℝ) ∂volIoi.restrict {u : Ioi (0 : ℝ) | (a : ℝ) < (u : ℝ)},
      Integrable (fun e => F (excursionRestrict a e) *
        qKernel θ ((u : ℝ) - a) (e.path.1 a)) (excursionTail θ a) →
      (lifetimeDensity θ u).toReal * (∫ e, F (excursionRestrict a e) ∂excursionAt θ u) =
        ∫ e, F (excursionRestrict a e) * qKernel θ ((u : ℝ) - a) (e.path.1 a)
          ∂excursionTail θ a := by
  have hp := prefix_density_ae_lifetime hθ a ha (fun x => ENNReal.ofReal (F x))
    hF.ennreal_ofReal
  have hn := prefix_density_ae_lifetime hθ a ha (fun x => ENNReal.ofReal (-F x))
    hF.neg.ennreal_ofReal
  have hU : MeasurableSet {u : Ioi (0 : ℝ) | (a : ℝ) < (u : ℝ)} :=
    measurableSet_lt measurable_const measurable_subtype_coe
  filter_upwards [hp, hn, ae_restrict_mem hU] with u huplus huminus hu
  intro hInt
  let _ := isProbabilityMeasure_excursionAt θ u
  obtain ⟨C, hC⟩ := hFb
  have hi : Integrable (fun e => F (excursionRestrict a e)) (excursionAt θ u) :=
    Integrable.of_bound (hF.comp (measurable_excursionRestrict a)).aestronglyMeasurable C
      (Eventually.of_forall fun e => hC _)
  have hq (e : Excursion) : 0 ≤ qKernel θ ((u : ℝ) - a) (e.path.1 a) :=
    qKernel_nonneg hθ (sub_pos.mpr hu) (e.2.2.1 a)
  have hpos : (∫⁻ e, ENNReal.ofReal (F (excursionRestrict a e)) *
      ENNReal.ofReal (qKernel θ ((u : ℝ) - a) (e.path.1 a)) ∂excursionTail θ a) =
      ∫⁻ e, ENNReal.ofReal (F (excursionRestrict a e) *
        qKernel θ ((u : ℝ) - a) (e.path.1 a)) ∂excursionTail θ a :=
    lintegral_congr fun e => (ENNReal.ofReal_mul' (hq e)).symm
  have hneg : (∫⁻ e, ENNReal.ofReal (-F (excursionRestrict a e)) *
      ENNReal.ofReal (qKernel θ ((u : ℝ) - a) (e.path.1 a)) ∂excursionTail θ a) =
      ∫⁻ e, ENNReal.ofReal (-(F (excursionRestrict a e) *
        qKernel θ ((u : ℝ) - a) (e.path.1 a))) ∂excursionTail θ a := by
    apply lintegral_congr
    intro e
    rw [← ENNReal.ofReal_mul' (hq e), neg_mul]
  change lifetimeDensity θ u * _ =
    ∫⁻ e, ENNReal.ofReal (F (excursionRestrict a e)) *
      ENNReal.ofReal (qKernel θ ((u : ℝ) - a) (e.path.1 a)) ∂excursionTail θ a at huplus
  change lifetimeDensity θ u * _ =
    ∫⁻ e, ENNReal.ofReal (-F (excursionRestrict a e)) *
      ENNReal.ofReal (qKernel θ ((u : ℝ) - a) (e.path.1 a)) ∂excursionTail θ a at huminus
  rw [hpos] at huplus
  rw [hneg] at huminus
  have hpt := congrArg ENNReal.toReal huplus
  have hnt := congrArg ENNReal.toReal huminus
  simp only [ENNReal.toReal_mul] at hpt hnt
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hi,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt, mul_sub, hpt, hnt]

end BGW.StableTrees
