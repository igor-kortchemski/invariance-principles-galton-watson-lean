/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Convergence of nonnegative weights with mass one

Scheffé's argument uses dominated convergence for the minimum of the two weights.
Convergence in measure is reduced to almost everywhere convergence on subsequences.

Reference: J.-F. Le Gall, *Random trees and applications*, Probab. Surveys 2 (2005),
Section 1.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace BGW.StableTrees

/-- **Scheffé for nonnegative mass-one weights** (generic helper).  If `w_k ≥ 0`,
`w ≥ 0`, all with integral one and `w_k → w` in measure, then `w_k → w` in `L¹`. -/
theorem tendsto_integral_abs_sub_of_massOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {w : ℕ → Ω → ℝ} {w₀ : Ω → ℝ}
    (hw : ∀ k, Measurable (w k)) (hw₀ : Measurable w₀)
    (hnn : ∀ k ω, 0 ≤ w k ω) (hnn₀ : ∀ ω, 0 ≤ w₀ ω)
    (h1 : ∀ k, ∫ ω, w k ω ∂P = 1) (h10 : ∫ ω, w₀ ω ∂P = 1)
    (hconv : TendstoInMeasure P w atTop w₀) :
    Tendsto (fun k => ∫ ω, |w k ω - w₀ ω| ∂P) atTop (𝓝 0) := by
  have hi (k : ℕ) := integrable_of_integral_eq_one (h1 k)
  have hi₀ := integrable_of_integral_eq_one h10
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, _, hms⟩ := (hconv.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hm (k : ℕ) : Integrable (fun ω => min (w (ns (ms k)) ω) (w₀ ω)) P := by
    apply hi₀.mono' ((hw _).min hw₀).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hnn _ _) (hnn₀ _))]
      exact min_le_right _ _
  have hlim : Tendsto (fun k => ∫ ω, min (w (ns (ms k)) ω) (w₀ ω) ∂P) atTop (𝓝 1) := by
    rw [← h10]
    apply tendsto_integral_of_dominated_convergence w₀
    · intro k
      exact ((hw _).min hw₀).aestronglyMeasurable
    · exact hi₀
    · intro k
      exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hnn _ _) (hnn₀ _))]
        exact min_le_right _ _
    · filter_upwards [hms] with ω hω
      simpa only [min_self, Function.comp_apply] using hω.min (tendsto_const_nhds (x := w₀ ω))
  have heq (k : ℕ) : (∫ ω, |w (ns (ms k)) ω - w₀ ω| ∂P) =
      2 - 2 * ∫ ω, min (w (ns (ms k)) ω) (w₀ ω) ∂P := by
    have hab (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
      rcases le_total x y with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring
    simp_rw [hab]
    rw [integral_sub
      (show Integrable (fun ω => w (ns (ms k)) ω + w₀ ω) P from (hi _).add hi₀)
      ((hm k).const_mul 2), integral_add (hi _) hi₀,
      integral_const_mul, h1, h10]
    ring
  simpa only [heq, Function.comp_def, show (2 : ℝ) - 2 * 1 = 0 by norm_num] using
    (tendsto_const_nhds (x := (2 : ℝ))).sub (hlim.const_mul 2)

/-- **Weighted convergence** (consequence): uniformly bounded measurable `F_k → F` in measure
and weights as above give `∫ F_k w_k → ∫ F w₀`. -/
theorem tendsto_integral_mul_of_massOne {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {w : ℕ → Ω → ℝ} {w₀ : Ω → ℝ}
    (hw : ∀ k, Measurable (w k)) (hw₀ : Measurable w₀)
    (hnn : ∀ k ω, 0 ≤ w k ω) (hnn₀ : ∀ ω, 0 ≤ w₀ ω)
    (h1 : ∀ k, ∫ ω, w k ω ∂P = 1) (h10 : ∫ ω, w₀ ω ∂P = 1)
    (hconv : TendstoInMeasure P w atTop w₀)
    {F : ℕ → Ω → ℝ} {F₀ : Ω → ℝ} {C : ℝ} (hF : ∀ k, Measurable (F k)) (hF₀ : Measurable F₀)
    (hC : ∀ k ω, |F k ω| ≤ C) (hC₀ : ∀ ω, |F₀ ω| ≤ C)
    (hFc : TendstoInMeasure P F atTop F₀) :
    Tendsto (fun k => ∫ ω, (F k ω * w k ω) ∂P) atTop (𝓝 (∫ ω, (F₀ ω * w₀ ω) ∂P)) := by
  have hi (k : ℕ) := integrable_of_integral_eq_one (h1 k)
  have hi₀ := integrable_of_integral_eq_one h10
  have hL := tendsto_integral_abs_sub_of_massOne hw hw₀ hnn hnn₀ h1 h10 hconv
  have hip (k : ℕ) := (hi k).bdd_mul (hF k).aestronglyMeasurable
    (ae_of_all _ fun ω => (Real.norm_eq_abs _).symm ▸ hC k ω)
  have hip₀ := hi₀.bdd_mul hF₀.aestronglyMeasurable
    (ae_of_all _ fun ω => (Real.norm_eq_abs _).symm ▸ hC₀ ω)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hmsmono, hms⟩ := (hFc.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hD : Tendsto (fun k => ∫ ω, (F (ns (ms k)) ω - F₀ ω) * w₀ ω ∂P)
      atTop (𝓝 0) := by
    have hbound : Integrable (fun ω => (2 * C) * w₀ ω) P := hi₀.const_mul _
    have hlim := tendsto_integral_of_dominated_convergence (fun ω => (2 * C) * w₀ ω)
      (fun k => (((hF _).sub hF₀).mul hw₀).aestronglyMeasurable) hbound
      (fun k => ae_of_all _ fun ω => ?_)
      (show ∀ᵐ ω ∂P, Tendsto (fun k => (F (ns (ms k)) ω - F₀ ω) * w₀ ω)
        atTop (𝓝 ((0 : Ω → ℝ) ω)) from ?_)
    · simpa using hlim
    · change ‖(F (ns (ms k)) ω - F₀ ω) * w₀ ω‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn₀ _)]
      exact mul_le_mul_of_nonneg_right
        ((abs_sub _ _).trans (by linarith [hC (ns (ms k)) ω, hC₀ ω])) (hnn₀ _)
    · filter_upwards [hms] with ω hω
      simpa using (hω.sub_const (F₀ ω)).mul_const (w₀ ω)
  have hE : Tendsto (fun k => ∫ ω, F (ns (ms k)) ω *
      (w (ns (ms k)) ω - w₀ ω) ∂P) atTop (𝓝 0) := by
    have hLC := (hL.comp (hns.comp hmsmono.tendsto_atTop)).const_mul C
    rw [mul_zero] at hLC
    apply squeeze_zero_norm' _ hLC
    · exact Eventually.of_forall fun k => by
        calc ‖∫ ω, F (ns (ms k)) ω * (w (ns (ms k)) ω - w₀ ω) ∂P‖
            ≤ ∫ ω, ‖F (ns (ms k)) ω * (w (ns (ms k)) ω - w₀ ω)‖ ∂P :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ ω, C * |w (ns (ms k)) ω - w₀ ω| ∂P := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              (((hi _).sub hi₀).abs.const_mul C)
            exact ae_of_all _ fun ω => by
              change ‖F (ns (ms k)) ω * (w (ns (ms k)) ω - w₀ ω)‖ ≤
                C * |w (ns (ms k)) ω - w₀ ω|
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right (hC _ _) (abs_nonneg _)
          _ = C * ∫ ω, |w (ns (ms k)) ω - w₀ ω| ∂P := integral_const_mul _ _
  have hsum := hE.add hD
  have heq (k : ℕ) :
      (∫ ω, F (ns (ms k)) ω * w (ns (ms k)) ω ∂P) - (∫ ω, F₀ ω * w₀ ω ∂P) =
      (∫ ω, F (ns (ms k)) ω * (w (ns (ms k)) ω - w₀ ω) ∂P) +
        ∫ ω, (F (ns (ms k)) ω - F₀ ω) * w₀ ω ∂P := by
    have hiF := hi₀.bdd_mul (hF (ns (ms k))).aestronglyMeasurable
      (ae_of_all _ fun ω => (Real.norm_eq_abs _).symm ▸ hC _ ω)
    rw [← integral_sub (hip _) hip₀,
      ← integral_add ((hip (ns (ms k))).sub hiF |>.congr
        (ae_of_all _ fun ω => (mul_sub _ _ _).symm))
        (hiF.sub hip₀ |>.congr (ae_of_all _ fun ω => (sub_mul _ _ _).symm))]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by ring
  have hh : Tendsto (fun k => (∫ ω, F (ns (ms k)) ω * w (ns (ms k)) ω ∂P) -
      (∫ ω, F₀ ω * w₀ ω ∂P)) atTop (𝓝 0) := by
    simpa only [heq, add_zero] using hsum
  have hh' := hh.add_const (∫ ω, F₀ ω * w₀ ω ∂P)
  simpa only [sub_add_cancel, zero_add, Function.comp_def] using hh'

end BGW.StableTrees
