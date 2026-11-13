/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionDensityGoodLaw
public import BGW.StableTrees.UnitExcursionDensityTransfer

/-!
# Unit excursion prefix density and absence of fixed jumps

The prefix law at every interior horizon is the normalized Kendall-weighted
excursion survival measure. In particular the unit law has no fixed jumps.

## Main results

* `unitPrefix`: the law of the prefix of the unit excursion up to an interior time.
* `levyExcLaw_prefix_density`: `unitPrefix θ a` is the normalized Kendall-weighted
  excursion survival measure, pushed forward by the restriction to `[0, a]`.
* `lintegral_unitPrefix_eq`: integral form of the prefix density for nonnegative
  measurable tests.
* `levyExcLaw_noFixedJump`: the unit law has no fixed jump at an interior time.
* `exists_goodTimes_unit`: a countable dense set of times without fixed jumps.
* `prefix_density_ae_lifetime`: the prefix density identity at almost every lifetime
  for a fixed nonnegative measurable test.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.

* T. Duquesne, *Path decompositions for real Lévy processes*,
  Ann. Inst. H. Poincaré Probab. Statist. 39 (2003), 339–370.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/- The proof first establishes mass and prefix density at good horizons `b`, transfers the
absence of a fixed jump at a time `t` from a good horizon `b > t`, and then obtains mass and
prefix density at every `0 < a < 1`. -/

/-- The unit law has no jump at each deterministic interior time. -/
theorem levyExcLaw_noFixedJump {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    (ht : t ∈ Ioo (0 : ℝ≥0) 1) : NoFixedJumpUnit θ t := by
  obtain ⟨G, _, hGsub, hGdense, hGgood⟩ := exists_goodTimes_unit hθ
  obtain ⟨b, hbG, htb, _⟩ := hGdense t 1 ht.2 le_rfl
  exact noFixedJumpUnit_of_prefix_density hθ b t ht.1 htb.le
    (levyExcLaw_prefix_density_of_good hθ b (hGsub hbG) (hGgood b hbG))

/-- The density side has mass equal to the stable density at zero. -/
theorem lintegral_prefix_density_mass {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ∫⁻ e in {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)},
      ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a)) ∂(excursionMeasure θ) =
        ENNReal.ofReal (Scalar.stableDensity θ 0) :=
  lintegral_prefix_density_mass_of_good hθ a ha (levyExcLaw_noFixedJump hθ a ha)

/-- The law of a unit-excursion prefix is the normalized Kendall-weighted survival measure. -/
theorem levyExcLaw_prefix_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    unitPrefix θ a =
      (ENNReal.ofReal (Scalar.stableDensity θ 0))⁻¹ •
        ((excursionTail θ a).withDensity
          (fun e => ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a)))).map
            (excursionRestrict a) :=
  levyExcLaw_prefix_density_of_good hθ a ha (levyExcLaw_noFixedJump hθ a ha)

/-- Integral form of the prefix density for nonnegative measurable tests. -/
theorem lintegral_unitPrefix_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    (ha : a ∈ Ioo (0 : ℝ≥0) 1) (F : D (a : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ x, F x ∂(unitPrefix θ a) =
      (ENNReal.ofReal (Scalar.stableDensity θ 0))⁻¹ *
        ∫⁻ e in {e : Excursion | (a : ℝ) < (e.lifetime : ℝ)},
          F (excursionRestrict a e) *
            ENNReal.ofReal (qKernel θ (1 - a) (e.path.1 a)) ∂(excursionMeasure θ) := by
  have hm : Measurable (fun e : Excursion => F (excursionRestrict a e)) :=
    hF.comp (measurable_excursionRestrict a)
  rw [levyExcLaw_prefix_density hθ a ha, lintegral_smul_measure, smul_eq_mul,
    lintegral_map hF (measurable_excursionRestrict a),
    lintegral_withDensity_eq_lintegral_mul _ (measurable_prefixDensity θ a)
      hm]
  congr 1
  exact lintegral_congr fun e => mul_comm _ _

end BGW.StableTrees
