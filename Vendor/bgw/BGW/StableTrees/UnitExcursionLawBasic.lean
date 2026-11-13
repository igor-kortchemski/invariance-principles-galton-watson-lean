/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionLifetime
public import BGW.StableTrees.ExcursionMeasure
public import BGW.ContinuumTrees.ExcursionCarrier

/-! # Normalized excursion laws and their lifetime-indexed scaling family

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Definitions -/

/-- The tail `N ↾ {ζ > a}` of the excursion measure. -/
noncomputable def excursionTail (θ : ℝ) (a : ℝ) : Measure Excursion :=
  (excursionMeasure θ).restrict {e : Excursion | a < (e.lifetime : ℝ)}

/-- Explicit normalized unit measure: `Γ(1-1/θ) • (normalizeExc θ)_* (N ↾ {ζ > 1})`.  The
coefficient is `N(ζ > 1)⁻¹`; this is a normalized restriction, not a conditioning on `{ζ = 1}`. -/
noncomputable def unitExcursionMeasure (θ : ℝ) : Measure Excursion :=
  ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) • (excursionTail θ 1).map (normalizeExc θ)

/-- The tail law `N(· | ζ > 1) = Γ(1-1/θ) • N ↾ {ζ > 1}` as a plain measure. -/
noncomputable def tailExcursionMeasure (θ : ℝ) : Measure Excursion :=
  ENNReal.ofReal (Real.Gamma (1 - 1 / θ)) • excursionTail θ 1

open scoped Classical in
/-- Probability-measure packaging with a junk `dirac junkExcursion` branch. -/
noncomputable def toProbOrJunk (μ : Measure Excursion) : ProbabilityMeasure Excursion :=
  if h : IsProbabilityMeasure μ then ⟨μ, h⟩
  else ⟨Measure.dirac junkExcursion, inferInstance⟩

/-- **Unit excursion law**; agrees with `unitExcursionMeasure` for `1 < θ ≤ 2`.  Outside that
range it is only a totalized probability measure. -/
noncomputable def unitExcursionLaw (θ : ℝ) : ProbabilityMeasure Excursion :=
  toProbOrJunk (unitExcursionMeasure θ)

/-- Law of the excursion under `N(· | ζ > 1)`; agrees with `tailExcursionMeasure` for
`1 < θ ≤ 2`.  Outside that range it is only a totalized probability measure. -/
noncomputable def tailExcursionLaw (θ : ℝ) : ProbabilityMeasure Excursion :=
  toProbOrJunk (tailExcursionMeasure θ)

/-- **Unit-lifetime excursion as a path on `[0,1]`**. -/
noncomputable def levyExcLaw (θ : ℝ) : ProbabilityMeasure (D 1 ℝ) :=
  (unitExcursionLaw θ).map (excursionRestrict 1)

/-- **Whole excursion under `N(· | ζ > 1)`, restricted to `[0,T]`**. -/
noncomputable def tailLevyExcLaw (θ : ℝ) (T : ℝ≥0) : ProbabilityMeasure (D (T : ℝ) ℝ) :=
  (tailExcursionLaw θ).map (excursionRestrict T)

/-- The scaled unit excursion `(S_u)_* unitExcursionLaw`, `u > 0`: the measure `N_{(u)}`
of excursions of lifetime `u`. -/
noncomputable def excursionAt (θ : ℝ) (u : Set.Ioi (0 : ℝ)) : Measure Excursion :=
  ((unitExcursionLaw θ : Measure Excursion)).map (excursionScale θ u)

/-- The lifetime density `(1/θ)/Γ(1-1/θ) · u^{-1-1/θ}`. -/
noncomputable def lifetimeDensity (θ : ℝ) (u : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 / θ) / Real.Gamma (1 - 1 / θ) * u ^ (-1 - 1 / θ))

/-- The excursion lifetime density is measurable on the positive half-line. -/
theorem measurable_lifetimeDensity (θ : ℝ) :
    Measurable (fun u : Ioi (0 : ℝ) => lifetimeDensity θ u) := by
  unfold lifetimeDensity
  fun_prop

/-- Lebesgue measure on `Set.Ioi 0` (comap of `volume`). -/
noncomputable def volIoi : Measure (Set.Ioi (0 : ℝ)) := Measure.comap Subtype.val volume

/-- Lebesgue measure restricted to the positive half-line is sigma-finite. -/
theorem sigmaFinite_volIoi : SigmaFinite volIoi := by
  have hm : SigmaFinite (volIoi.map (Subtype.val : Ioi (0 : ℝ) → ℝ)) := by
    rw [volIoi, map_comap_subtype_coe measurableSet_Ioi]
    infer_instance
  exact SigmaFinite.of_map volIoi measurable_subtype_coe.aemeasurable hm

/-- The Lévy measure `ζ_* N` on `Set.Ioi 0`. -/
noncomputable def lifetimeLaw (θ : ℝ) : Measure (Set.Ioi (0 : ℝ)) :=
  volIoi.withDensity (fun u => lifetimeDensity θ u)

private theorem gamma_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    0 < Real.Gamma (1 - 1 / θ) :=
  Real.Gamma_pos_of_pos (sub_pos.mpr ((div_lt_one (by linarith)).mpr hθ.1))

private theorem measurableSet_tail (a : ℝ) :
    MeasurableSet {e : Excursion | a < (e.lifetime : ℝ)} :=
  measurableSet_lt measurable_const measurable_excursion_lifetime.coe_nnreal_real

/-- **Mass of the unit tail**: `N(ζ > 1) = 1/Γ(1-1/θ) = θ d_θ(0)`. -/
theorem excursionMeasure_lifetime_gt_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    excursionMeasure θ {e : Excursion | 1 < (e.lifetime : ℝ)} =
      ENNReal.ofReal (1 / Real.Gamma (1 - 1 / θ)) := by
  simpa using excursionMeasure_lifetime_tail hθ 1 one_pos

/-- The same mass through the stable density at `0`. -/
theorem excursionMeasure_lifetime_gt_one_eq_density {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    excursionMeasure θ {e : Excursion | 1 < (e.lifetime : ℝ)} =
      ENNReal.ofReal (θ * Scalar.stableDensity θ 0) := by
  rw [excursionMeasure_lifetime_gt_one hθ, stableDensity_zero_eq_inv_theta_gamma hθ]
  congr 1
  field_simp [ne_of_gt (lt_trans zero_lt_one hθ.1)]

/-- The tail measure is a probability measure. -/
theorem isProbabilityMeasure_tailExcursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsProbabilityMeasure (tailExcursionMeasure θ) := by
  constructor
  rw [tailExcursionMeasure, Measure.smul_apply, smul_eq_mul, excursionTail,
    Measure.restrict_apply MeasurableSet.univ, univ_inter,
    excursionMeasure_lifetime_gt_one hθ, ENNReal.ofReal_div_of_pos (gamma_pos hθ)]
  rw [ENNReal.ofReal_one, one_div]
  simpa only [one_div] using
    ENNReal.mul_inv_cancel (ENNReal.ofReal_ne_zero_iff.mpr (gamma_pos hθ))
      ENNReal.ofReal_ne_top

/-- The unnormalized unit measure is a probability measure. -/
theorem isProbabilityMeasure_unitExcursionMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsProbabilityMeasure (unitExcursionMeasure θ) := by
  have := isProbabilityMeasure_tailExcursionMeasure hθ
  have heq : unitExcursionMeasure θ =
      (tailExcursionMeasure θ).map (normalizeExc θ) := by
    rw [unitExcursionMeasure, tailExcursionMeasure,
      Measure.map_smul _ (measurable_normalizeExc θ).aemeasurable]
  rw [heq]
  infer_instance

/-- Unfolding: the law is the explicit normalized restriction. -/
theorem coe_unitExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (unitExcursionLaw θ : Measure Excursion) = unitExcursionMeasure θ := by
  unfold unitExcursionLaw toProbOrJunk ProbabilityMeasure.toMeasure ProbabilityMeasure
  rw [dite_eq_left (isProbabilityMeasure_unitExcursionMeasure hθ)]

/-- Unfolding for the tail law. -/
theorem coe_tailExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (tailExcursionLaw θ : Measure Excursion) = tailExcursionMeasure θ := by
  unfold tailExcursionLaw toProbOrJunk ProbabilityMeasure.toMeasure ProbabilityMeasure
  rw [dite_eq_left (isProbabilityMeasure_tailExcursionMeasure hθ)]

/-- Unit excursions have lifetime one almost surely (indeed surely on the support). -/
theorem ae_lifetime_unitExcursionLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), e.lifetime = 1 := by
  rw [coe_unitExcursionLaw hθ, unitExcursionMeasure]
  apply Measure.ae_smul_measure
  rw [ae_map_iff (measurable_normalizeExc θ).aemeasurable
    (measurableSet_eq_fun measurable_excursion_lifetime measurable_const)]
  exact Eventually.of_forall (normalizeExc_lifetime θ)

/-- Each `excursionAt θ u` is a probability measure (for every `θ`). -/
theorem isProbabilityMeasure_excursionAt (θ : ℝ) (u : Set.Ioi (0 : ℝ)) :
    IsProbabilityMeasure (excursionAt θ u) := by
  unfold excursionAt
  infer_instance

/-- Measurability of `u ↦ N_{(u)}(A)`. -/
theorem measurable_excursionAt_apply (θ : ℝ) {A : Set Excursion} (hA : MeasurableSet A) :
    Measurable (fun u : Set.Ioi (0 : ℝ) => excursionAt θ u A) := by
  have hm := measurable_measure_prodMk_left (ν := (unitExcursionLaw θ : Measure Excursion))
    (hA.preimage (measurable_excursionScale_joint θ))
  change Measurable (fun u : Ioi (0 : ℝ) =>
    (unitExcursionLaw θ : Measure Excursion) (excursionScale θ u ⁻¹' A)) at hm
  simpa only [excursionAt, Measure.map_apply (measurable_excursionScale θ _) hA] using hm

/-- `N_{(u)}`-almost every excursion has lifetime `u`. -/
theorem ae_lifetime_excursionAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (u : Set.Ioi (0 : ℝ)) :
    ∀ᵐ e ∂(excursionAt θ u), (e.lifetime : ℝ) = (u : ℝ) := by
  unfold excursionAt
  rw [ae_map_iff (measurable_excursionScale θ u).aemeasurable
    (measurableSet_eq_fun measurable_excursion_lifetime.coe_nnreal_real measurable_const)]
  filter_upwards [ae_lifetime_unitExcursionLaw hθ] with e he
  rw [excursionScale_lifetime, he, NNReal.coe_one, mul_one]

/-- Exact scaling of the family at every lifetime: `(S_c)_* N_{(u)} = N_{(cu)}`. -/
theorem map_excursionScale_excursionAt (θ : ℝ) (c u : Set.Ioi (0 : ℝ)) :
    (excursionAt θ u).map (excursionScale θ c) =
      excursionAt θ ⟨(c : ℝ) * (u : ℝ), Set.mem_Ioi.2 (mul_pos c.2 u.2)⟩ := by
  unfold excursionAt
  rw [Measure.map_map (measurable_excursionScale θ c) (measurable_excursionScale θ u)]
  congr 1
  funext e
  exact excursionScale_mul θ c u e

/-- The family at lifetime one is the unit law. -/
theorem excursionAt_one (θ : ℝ) :
    excursionAt θ ⟨1, Set.mem_Ioi.2 one_pos⟩ = (unitExcursionLaw θ : Measure Excursion) := by
  simp only [excursionAt, show excursionScale θ ⟨1, Set.mem_Ioi.2 one_pos⟩ = id from
    funext (excursionScale_one θ), Measure.map_id]

end BGW.StableTrees
