/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionDensityCandidate
import BGW.Skorokhod.MeasurableLaws
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-!
# Identification of the unit prefix law at good horizons

The candidate is normalized before finite-dimensional uniqueness is used.
The dense evaluation set contains the terminal coordinate.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Reindexing the good-time cylinder identity by an arbitrary finite type. -/
theorem integral_goodTimes_eq_prefixDensityMeasure_fintype {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (b : ℝ≥0) (hb : b ∈ Ioo (0 : ℝ≥0) 1) (hbgood : NoFixedJumpUnit θ b)
    {I : Type*} [Fintype I] (t : I → ℝ≥0) (ht : ∀ i, t i ≤ b)
    (hgood : ∀ i, NoFixedJumpUnit θ (t i)) (φ : (I → ℝ) → ℝ)
    (hφ : Continuous φ) (hφb : ∃ C : ℝ, ∀ x, |φ x| ≤ C) :
    (∫ e, φ (fun i => e.path.1 (t i)) ∂(unitExcursionLaw θ : Measure Excursion)) =
      (Scalar.stableDensity θ 0)⁻¹ *
        ∫ e, φ (fun i => e.path.1 (t i)) ∂prefixDensityMeasure θ b := by
  let v : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let ψ : (Fin (Fintype.card I) → ℝ) → ℝ := fun x => φ (fun i => x (v.symm i))
  have hψ : Continuous ψ := hφ.comp (continuous_pi fun i => continuous_apply (v.symm i))
  obtain ⟨C, hC⟩ := hφb
  have h := integral_goodTimes_eq_prefixDensityMeasure hθ b hb hbgood
    (fun i => t (v i)) (fun i => ht (v i)) (fun i => hgood (v i)) ψ hψ
    ⟨C, fun x => hC _⟩
  simpa only [ψ, Equiv.apply_symm_apply] using h

/-- At a good horizon, normalized Kendall weighting gives the unit prefix law. -/
theorem levyExcLaw_prefix_density_of_good {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (b : ℝ≥0)
    (hb : b ∈ Ioo (0 : ℝ≥0) 1) (hbgood : NoFixedJumpUnit θ b) :
    unitPrefix θ b = (ENNReal.ofReal (Scalar.stableDensity θ 0))⁻¹ •
      (prefixDensityMeasure θ b).map (excursionRestrict b) := by
  classical
  let c := ENNReal.ofReal (Scalar.stableDensity θ 0)
  have hc0 : c ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr (Scalar.stableDensity_zero_pos hθ)
  have hctop : c ≠ ∞ := ENNReal.ofReal_ne_top
  let M : Measure (D (b : ℝ) ℝ) := c⁻¹ • (prefixDensityMeasure θ b).map (excursionRestrict b)
  have hM : IsProbabilityMeasure M := by
    constructor
    change (c⁻¹ • (prefixDensityMeasure θ b).map (excursionRestrict b)) univ = 1
    rw [Measure.smul_apply, smul_eq_mul,
      Measure.map_apply (measurable_excursionRestrict b) MeasurableSet.univ,
      preimage_univ, prefixDensityMeasure_univ_of_good hθ b hb hbgood]
    exact ENNReal.inv_mul_cancel hc0 hctop
  let P : ProbabilityMeasure (D (b : ℝ) ℝ) := (unitExcursionLaw θ).map (excursionRestrict b)
  let Q : ProbabilityMeasure (D (b : ℝ) ℝ) := ⟨M, hM⟩
  let S : Set (Icc (0 : ℝ) b) := {t | NoFixedJumpUnit θ ⟨t, t.2.1⟩}
  let _ : Nontrivial (Icc (0 : ℝ) b) := by
    refine ⟨⟨⟨0, le_rfl, b.2⟩, ⟨b, b.2, le_rfl⟩, ?_⟩⟩
    intro heq
    have : (0 : ℝ) = b := congrArg Subtype.val heq
    have hb0 : (0 : ℝ) < b := hb.1
    linarith
  have hS : Dense S := by
    obtain ⟨G, _, _, hGdense, hGgood⟩ := exists_goodTimes_unit hθ
    apply dense_of_exists_between
    intro x y hxy
    obtain ⟨t, htG, hxt, hty⟩ := hGdense ⟨x, x.2.1⟩ ⟨y, y.2.1⟩ hxy
      (show (⟨(y : ℝ), y.2.1⟩ : ℝ≥0) ≤ 1 from
        y.2.2.trans (show (b : ℝ) ≤ 1 from hb.2.le))
    refine ⟨⟨t, t.2, ?_⟩, hGgood t htG, hxt, hty⟩
    exact hty.le.trans y.2.2
  have hSb : (⟨b, b.2, le_rfl⟩ : Icc (0 : ℝ) b) ∈ S := hbgood
  have hPQ : P = Q := by
    apply ext_of_finiteDimensional hS b.2 hSb
    intro s hs
    apply Subtype.ext
    let ev : D (b : ℝ) ℝ → s → ℝ := fun x j => x j.val
    have hev : Measurable ev := Measurable.of_eval fun j => measurable_eval j.val
    change (P : Measure (D (b : ℝ) ℝ)).map ev = (Q : Measure (D (b : ℝ) ℝ)).map ev
    apply ext_of_forall_integral_eq_of_IsFiniteMeasure
    intro f
    rw [integral_map hev.aemeasurable f.continuous.aestronglyMeasurable,
      integral_map hev.aemeasurable f.continuous.aestronglyMeasurable]
    let t : s → ℝ≥0 := fun j => ⟨j.val, j.val.2.1⟩
    have ht (j : s) : t j ≤ b := j.val.2.2
    have hg (j : s) : NoFixedJumpUnit θ (t j) := hs j.property
    have hcy := integral_goodTimes_eq_prefixDensityMeasure_fintype hθ b hb hbgood
      t ht hg f f.continuous ⟨‖f‖, fun x => f.norm_coe_le_norm x⟩
    change (∫ x, f (ev x) ∂((unitExcursionLaw θ : Measure Excursion).map
      (excursionRestrict b))) = ∫ x, f (ev x) ∂M
    change (∫ x, f (ev x) ∂((unitExcursionLaw θ : Measure Excursion).map
      (excursionRestrict b))) =
      ∫ x, f (ev x) ∂(c⁻¹ • (prefixDensityMeasure θ b).map (excursionRestrict b))
    have hmf : Measurable (fun x : D (b : ℝ) ℝ => f (ev x)) :=
      f.continuous.measurable.comp hev
    have hmap (μ : Measure Excursion) :
        (∫ x, f (ev x) ∂μ.map (excursionRestrict b)) =
        ∫ e, f (ev (excursionRestrict b e)) ∂μ :=
      integral_map (measurable_excursionRestrict b).aemeasurable hmf.aestronglyMeasurable
    rw [integral_smul_measure, hmap, hmap]
    have heval (e : Excursion) : ev (excursionRestrict b e) =
        fun j => e.path.1 (t j) := rfl
    simp_rw [heval]
    simpa only [c, ENNReal.toReal_inv,
      ENNReal.toReal_ofReal (Scalar.stableDensity_zero_pos hθ).le, smul_eq_mul] using hcy
  exact congrArg (fun R : ProbabilityMeasure (D (b : ℝ) ℝ) => (R : Measure (D (b : ℝ) ℝ))) hPQ

end BGW.StableTrees
