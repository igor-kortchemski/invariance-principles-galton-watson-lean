/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionDensityContinuity
public import BGW.StableTrees.UnitExcursionDensityTailContinuity
import BGW.StableTrees.UnitExcursionDensitySignedLifetime
import BGW.StableTrees.ExcursionMarkov
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Evaluating cutoff prefix densities at lifetime one

Fix a cylinder test before invoking the lifetime identity. Continuity on both
sides upgrades almost-everywhere equality to equality at lifetime one.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- Compact endpoint cutoffs make the positive-time prefix density integrable. -/
theorem integrable_prefix_cutoff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (b : ℝ≥0) (hb : 0 < b) (H : Excursion → ℝ) (hH : Measurable H)
    (hHb : ∃ C : ℝ, ∀ e, |H e| ≤ C) (χ : ℝ → ℝ) (hχ : Continuous χ)
    (hχc : HasCompactSupport χ) {s : ℝ} (hs : 0 < s) :
    Integrable (fun e => H e * χ (e.path.1 b) * qKernel θ s (e.path.1 b))
      (excursionTail θ b) := by
  let _ : IsFiniteMeasure (excursionTail θ b) := by
    unfold excursionTail
    simp only [NNReal.coe_lt_coe]
    exact isFiniteMeasure_excursionMeasure_survival hθ b hb
  have hq : Continuous (fun x : ℝ => qKernel θ s x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact ((continuousOn_qKernel hθ).continuousAt
      ((isOpen_lt continuous_const continuous_fst).mem_nhds hs)).comp
      (f := fun x : ℝ => (s, x)) (by fun_prop)
  have hc : Continuous (fun x : ℝ => χ x * qKernel θ s x) := hχ.mul hq
  have hsupp : HasCompactSupport (fun x : ℝ => χ x * qKernel θ s x) :=
    hχc.mul_right
  obtain ⟨C, hC⟩ := hsupp.exists_bound_of_continuous hc
  obtain ⟨A, hA⟩ := hHb
  apply Integrable.of_bound
    (((hH.mul (hχ.measurable.comp (measurable_excursion_eval b))).mul
      (hq.measurable.comp (measurable_excursion_eval b))).aestronglyMeasurable) (|A| * |C|)
  apply Eventually.of_forall
  intro e
  simp only [Pi.mul_apply, Function.comp_apply]
  rw [mul_assoc, norm_mul]
  exact mul_le_mul ((hA e).trans (le_abs_self A)) ((hC _).trans (le_abs_self C))
    (norm_nonneg _) (abs_nonneg A)

private theorem eq_at_of_ae_on_open {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) [μ.IsOpenPosMeasure]
    {f g : X → ℝ} {U : Set X} (hU : IsOpen U) {x : X} (hx : x ∈ U)
    (h : f =ᵐ[μ.restrict U] g) (hf : ContinuousAt f x) (hg : ContinuousAt g x) :
    f x = g x := by
  have hd := Measure.dense_of_ae (ae_imp_of_ae_restrict h)
  have hcl : x ∈ closure {y | f y = g y} := by
    rw [mem_closure_iff]
    intro V hV hxV
    obtain ⟨y, hy, hyV⟩ := hd.exists_mem_open (hV.inter hU) ⟨x, hxV, hx⟩
    exact ⟨y, hyV.1, hy hyV.2⟩
  let _ : NeBot (𝓝[{y | f y = g y}] x) := mem_closure_iff_nhdsWithin_neBot.mp hcl
  have heq : f =ᶠ[𝓝[{y | f y = g y}] x] g := self_mem_nhdsWithin
  exact tendsto_nhds_unique (hf.tendsto.mono_left nhdsWithin_le_nhds)
    ((hg.tendsto.mono_left nhdsWithin_le_nhds).congr' heq.symm)

/-- Evaluation of the prefix density at lifetime one on good-time cutoff cylinders. -/
theorem integral_goodTimes_eq_density_at_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (b : ℝ≥0)
    (hb : b ∈ Ioo (0 : ℝ≥0) 1) (hbgood : NoFixedJumpUnit θ b) {n : ℕ} (t : Fin n → ℝ≥0)
    (ht : ∀ i, t i ≤ b) (hgood : ∀ i, NoFixedJumpUnit θ (t i))
    (φ : (Fin n → ℝ) → ℝ) (hφ : Continuous φ) (hφb : ∃ C : ℝ, ∀ x, |φ x| ≤ C)
    (χ : ℝ → ℝ) (hχ : Continuous χ) (hχc : HasCompactSupport χ) :
    (∫ e, φ (fun i => e.path.1 (t i)) * χ (e.path.1 b) ∂(unitExcursionLaw θ : Measure Excursion)) =
      (Scalar.stableDensity θ 0)⁻¹ *
        ∫ e in {e : Excursion | (b : ℝ) < (e.lifetime : ℝ)},
          φ (fun i => e.path.1 (t i)) * χ (e.path.1 b) *
            qKernel θ (1 - b) (e.path.1 b) ∂(excursionMeasure θ) := by
  let τ : Fin n → Icc (0 : ℝ) b := fun i => ⟨t i, (t i).2, ht i⟩
  let top : Icc (0 : ℝ) b := ⟨b, b.2, le_rfl⟩
  let F : D (b : ℝ) ℝ → ℝ := fun x => φ (fun i => x (τ i)) * χ (x top)
  have hF : Measurable F :=
    (hφ.measurable.comp (Measurable.of_eval fun i => measurable_eval (τ i))).mul
      (hχ.measurable.comp (measurable_eval top))
  obtain ⟨A, hA⟩ := hφb
  obtain ⟨C, hC⟩ := hχc.exists_bound_of_continuous hχ
  have hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C := by
    refine ⟨|A| * |C|, fun x => ?_⟩
    exact (abs_mul _ _).le.trans
      (mul_le_mul ((hA _).trans (le_abs_self A)) ((hC _).trans (le_abs_self C))
        (abs_nonneg _) (abs_nonneg A))
  have hFe (e : Excursion) : F (excursionRestrict b e) =
      φ (fun i => e.path.1 (t i)) * χ (e.path.1 b) := rfl
  let σ : Fin (n + 1) → ℝ≥0 := Fin.cases b t
  let ψ : (Fin (n + 1) → ℝ) → ℝ := fun x => φ (fun i => x i.succ) * χ (x 0)
  have hψ : Continuous ψ :=
    (hφ.comp (continuous_pi fun i => continuous_apply i.succ)).mul
      (hχ.comp (continuous_apply 0))
  have hψb : ∃ C : ℝ, ∀ x, |ψ x| ≤ C := by
    refine ⟨|A| * |C|, fun x => ?_⟩
    exact (abs_mul _ _).le.trans
      (mul_le_mul ((hA _).trans (le_abs_self A)) ((hC _).trans (le_abs_self C))
        (abs_nonneg _) (abs_nonneg A))
  have hσ : ∀ i, σ i ≤ 1 := Fin.forall_fin_succ.mpr
    ⟨hb.2.le, fun i => (ht i).trans hb.2.le⟩
  have hσgood : ∀ i, NoFixedJumpUnit θ (σ i) :=
    Fin.forall_fin_succ.mpr ⟨hbgood, hgood⟩
  let L : Ioi (0 : ℝ) → ℝ := fun u => (lifetimeDensity θ u).toReal *
    ∫ e, φ (fun i => e.path.1 (t i)) * χ (e.path.1 b) ∂excursionAt θ u
  let R : Ioi (0 : ℝ) → ℝ := fun u =>
    ∫ e, φ (fun i => e.path.1 (t i)) * χ (e.path.1 b) *
      qKernel θ ((u : ℝ) - b) (e.path.1 b) ∂excursionTail θ b
  have hL : ContinuousAt L ⟨1, Set.mem_Ioi.mpr one_pos⟩ := by
    have hi := excursionAt_finiteDim_continuousAt_one hθ σ hσ hσgood ψ hψ hψb
    have hd : ContinuousAt (fun u : Ioi (0 : ℝ) => (lifetimeDensity θ u).toReal)
        ⟨1, Set.mem_Ioi.mpr one_pos⟩ := by
      simp only [lifetimeDensity, ENNReal.toReal_ofReal']
      have hr : ContinuousAt (fun u : Ioi (0 : ℝ) => (u : ℝ) ^ (-1 - 1 / θ))
          ⟨1, Set.mem_Ioi.mpr one_pos⟩ :=
        continuous_subtype_val.continuousAt.rpow_const (by simp)
      exact (continuousAt_const.mul hr).max continuousAt_const
    convert hd.mul hi using 1
    rfl
  have hR : ContinuousAt R ⟨1, Set.mem_Ioi.mpr one_pos⟩ := by
    convert ContinuousAt.comp (x := (⟨1, Set.mem_Ioi.mpr one_pos⟩ : Ioi (0 : ℝ)))
      (f := fun u : Ioi (0 : ℝ) => (u : ℝ))
      (excursionTail_density_continuousAt_one hθ b hb t ht φ hφ ⟨A, hA⟩ χ hχ hχc)
      continuous_subtype_val.continuousAt using 1
    rfl
  have hae : L =ᵐ[volIoi.restrict {u : Ioi (0 : ℝ) | (b : ℝ) < (u : ℝ)}] R := by
    filter_upwards [prefix_density_ae_lifetime_integral hθ b hb.1 F hF hFb,
      ae_restrict_mem (measurableSet_lt measurable_const measurable_subtype_coe)] with u hu hut
    have hint := integrable_prefix_cutoff hθ b hb.1
      (fun e => φ (fun i => e.path.1 (t i)))
      (hφ.measurable.comp (Measurable.of_eval fun i => measurable_excursion_eval (t i)))
      ⟨A, fun e => hA _⟩ χ hχ hχc (sub_pos.mpr hut)
    simpa only [hFe] using hu (by simpa only [hFe] using hint)
  let _ : volIoi.IsOpenPosMeasure :=
    Measure.IsOpenPosMeasure.comap volume (isOpen_Ioi.isOpenEmbedding_subtypeVal)
  have heq := eq_at_of_ae_on_open volIoi
    (isOpen_lt continuous_const continuous_subtype_val)
    (show (b : ℝ) < 1 from hb.2) hae hL hR
  have hd1 : (lifetimeDensity θ 1).toReal = Scalar.stableDensity θ 0 := by
    rw [lifetimeDensity, Real.one_rpow, mul_one,
      div_div, ← stableDensity_zero_eq_inv_theta_gamma hθ,
      ENNReal.toReal_ofReal (stableDensity_nonneg hθ 0)]
  change (lifetimeDensity θ 1).toReal * _ = _ at heq
  rw [hd1, excursionAt_one] at heq
  have hp0 : Scalar.stableDensity θ 0 ≠ 0 := by
    rw [stableDensity_zero_eq_inv_theta_gamma hθ]
    apply one_div_ne_zero
    apply mul_ne_zero (by linarith [hθ.1])
    exact (Real.Gamma_pos_of_pos (by
      have hθ0 : 0 < θ := by linarith [hθ.1]
      exact sub_pos.mpr ((div_lt_one hθ0).mpr hθ.1))).ne'
  dsimp only [R] at heq
  have hh := congrArg (fun z : ℝ => (Scalar.stableDensity θ 0)⁻¹ * z) heq
  rw [inv_mul_cancel_left₀ hp0] at hh
  exact hh

end BGW.StableTrees
