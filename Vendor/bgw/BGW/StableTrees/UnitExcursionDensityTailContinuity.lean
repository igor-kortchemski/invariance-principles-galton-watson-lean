/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionDensityLifetime
import BGW.StableTrees.ExcursionMarkov
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Continuity of cutoff prefix densities

Compact endpoint support bounds the Kendall kernel on a compact time/endpoint
rectangle. Finite excursion survival measure then gives dominated convergence.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- Continuity of cutoff prefix densities at lifetime one. -/
theorem excursionTail_density_continuousAt_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (b : ℝ≥0)
    (hb : b ∈ Ioo (0 : ℝ≥0) 1) {n : ℕ} (t : Fin n → ℝ≥0) (ht : ∀ i, t i ≤ b)
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hφb : ∃ C : ℝ, ∀ x, |φ x| ≤ C)
    (χ : ℝ → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    ContinuousAt
      (fun u : ℝ => ∫ e in {e : Excursion | (b : ℝ) < (e.lifetime : ℝ)},
        φ (fun i => e.path.1 (t i)) * χ (e.path.1 b) *
          qKernel θ (u - b) (e.path.1 b) ∂(excursionMeasure θ)) 1 := by
  -- This domination also applies to tests at times beyond b.
  -- `ht` is part of the stated interface; the argument does not use it.
  have _ht := ht
  let μ : Measure Excursion :=
    (excursionMeasure θ).restrict {e : Excursion | (b : ℝ) < (e.lifetime : ℝ)}
  let _ : IsFiniteMeasure μ := by
    dsimp only [μ]
    simp only [NNReal.coe_lt_coe]
    exact isFiniteMeasure_excursionMeasure_survival hθ b hb.1
  let δ : ℝ := (1 - b) / 2
  have hb1 : (b : ℝ) < 1 := hb.2
  have hb0 : 0 ≤ (b : ℝ) := b.2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let K : Set (ℝ × ℝ) := Icc δ 2 ×ˢ tsupport χ
  have hK : IsCompact K := isCompact_Icc.prod hχc
  have hfK : ContinuousOn (fun z : ℝ × ℝ => χ z.2 * qKernel θ z.1 z.2) K :=
    (hχ.comp continuous_snd).continuousOn.mul
      ((continuousOn_qKernel hθ).mono fun z hz => hδ.trans_le hz.1.1)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hfK
  obtain ⟨A, hA⟩ := hφb
  have hmφ : Measurable (fun e : Excursion => φ (fun i => e.path.1 (t i))) :=
    hφ.measurable.comp (Measurable.of_eval fun i => measurable_excursion_eval (t i))
  have hnear : ∀ᶠ u : ℝ in 𝓝 1, δ < u - b ∧ u - b < 2 := by
    have hc : ContinuousAt (fun u : ℝ => u - (b : ℝ)) 1 := by fun_prop
    exact hc.eventually (Ioo_mem_nhds (by dsimp [δ]; linarith) (by linarith))
  apply continuousAt_of_dominated (μ := μ) (bound := fun _ => |A| * |C|)
  · exact Eventually.of_forall fun u =>
      ((hmφ.mul (hχ.measurable.comp (measurable_excursion_eval b))).mul
        ((measurable_qKernel θ).comp
          (measurable_const.prodMk (measurable_excursion_eval b)))).aestronglyMeasurable
  · filter_upwards [hnear] with u hu
    apply Eventually.of_forall
    intro e
    by_cases he : χ (e.path.1 b) = 0
    · simp only [he, mul_zero, zero_mul, norm_zero]
      exact mul_nonneg (abs_nonneg A) (abs_nonneg C)
    · have hx : e.path.1 b ∈ tsupport χ := subset_tsupport χ he
      have hbound := hC (u - b, e.path.1 b) ⟨⟨hu.1.le, hu.2.le⟩, hx⟩
      rw [mul_assoc, norm_mul]
      exact mul_le_mul ((hA _).trans (le_abs_self A))
        (hbound.trans (le_abs_self C)) (norm_nonneg _) (abs_nonneg A)
  · exact integrable_const _
  · apply Eventually.of_forall
    intro e
    have hc : ContinuousAt (fun z : ℝ × ℝ => qKernel θ z.1 z.2)
        (1 - b, e.path.1 b) :=
      (continuousOn_qKernel hθ).continuousAt
        ((isOpen_lt continuous_const continuous_fst).mem_nhds (sub_pos.mpr hb1))
    exact continuousAt_const.mul (hc.comp
      (f := fun u : ℝ => (u - (b : ℝ), e.path.1 b)) (by fun_prop))

end BGW.StableTrees
