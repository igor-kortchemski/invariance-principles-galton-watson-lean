/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformClockIntegrals
public import BGW.StableTrees.SupremumLadderTransformIntegrals
public import BGW.StableTrees.SupremumLadderTransformResolvent

/-!
# Weighted occupations and the boundary potential

The cumulative representation and half-rate tails provide integrability before passing
compact occupation errors to expectations.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Ordinary weighted occupation of the reflected process.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
noncomputable def supWeightedOccupation (q lam ε : ℝ) (f : DLoc) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-q * t - lam * supRunning f t.toNNReal) *
    supOccKernel ε (supReflected f t.toNNReal)

/-- The weighted occupation is measurable, including on exceptional paths.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem measurable_supWeightedOccupation (q lam ε : ℝ) :
    Measurable (supWeightedOccupation q lam ε) := by
  have hS := measurable_supRunning_uncurry.comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hR := measurable_supReflected_uncurry.comp
    ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd)
  have hm : Measurable (fun p : ℝ × DLoc =>
      Real.exp (-q * p.1 - lam * supRunning p.2 p.1.toNNReal) *
        supOccKernel ε (supReflected p.2 p.1.toNNReal)) :=
    (((measurable_const.mul measurable_fst).sub
      (measurable_const.mul hS)).exp.mul ((measurable_supOccKernel ε).comp hR))
  exact hm.stronglyMeasurable.integral_prod_left'.measurable

/-- At a zero-start path, the weighted kernel is integrable and bounded by the
ordinary discounted occupation.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem integrableOn_supWeightedKernel {q lam ε : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam)
    (hε : 0 < ε) (f : DLoc) (hf : f.1 0 = 0) :
    IntegrableOn (fun t : ℝ => Real.exp (-q * t - lam * supRunning f t.toNNReal) *
      supOccKernel ε (supReflected f t.toNNReal)) (Ioi 0) ∧
      supWeightedOccupation q lam ε f ≤ supAuxOccupationTail q ε 0 f := by
  have hb := integrableOn_supAuxKernel_exp hq hε 0 f
  simp_rw [supReflectedFrom_zero_apply hf] at hb
  have hSm := (monotone_supRunning f).measurable.comp measurable_real_toNNReal
  have hRm := (measurable_supReflected_uncurry.comp
    (measurable_real_toNNReal.prodMk (measurable_const : Measurable (fun _ : ℝ => f))))
  have hmeas : Measurable (fun t : ℝ =>
      Real.exp (-q * t - lam * supRunning f t.toNNReal) *
        supOccKernel ε (supReflected f t.toNNReal)) :=
    (((measurable_const.mul measurable_id).sub (measurable_const.mul hSm)).exp).mul
      ((measurable_supOccKernel ε).comp hRm)
  have hle (t : ℝ) :
      Real.exp (-q * t - lam * supRunning f t.toNNReal) *
        supOccKernel ε (supReflected f t.toNNReal) ≤
      Real.exp (-q * t) * supOccKernel ε (supReflected f t.toNNReal) := by
    apply mul_le_mul_of_nonneg_right _ (supOccKernel_mem_Icc hε _).1
    apply Real.exp_le_exp.mpr
    have hs : 0 ≤ supRunning f t.toNNReal := by
      simpa only [hf] using eval_le_supRunning f (u := 0) (zero_le : 0 ≤ t.toNNReal)
    nlinarith [mul_nonneg hlam hs]
  have hi : IntegrableOn (fun t : ℝ =>
      Real.exp (-q * t - lam * supRunning f t.toNNReal) *
        supOccKernel ε (supReflected f t.toNNReal)) (Ioi 0) := by
    apply hb.mono' hmeas.aestronglyMeasurable
    filter_upwards with t
    rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (supOccKernel_mem_Icc hε _).1)]
    exact hle t
  refine ⟨hi, ?_⟩
  change _ ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-q * t) *
    supOccKernel ε (supReflectedFrom 0 f t.toNNReal)
  simp_rw [supReflectedFrom_zero_apply hf]
  exact integral_mono hi hb hle

/-- The weighted occupation is integrable under the stable path law.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem integrable_supWeightedOccupation {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam ε : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam) (hε : 0 < ε) :
    Integrable (supWeightedOccupation q lam ε) (stableLocalLaw θ : Measure DLoc) := by
  apply (integrable_supAuxOccupationTail θ hq hε 0).mono'
    (measurable_supWeightedOccupation q lam ε).aestronglyMeasurable
  filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
  have hn : 0 ≤ supWeightedOccupation q lam ε f := integral_nonneg fun t =>
    mul_nonneg (Real.exp_pos _).le (supOccKernel_mem_Icc hε _).1
  rw [Real.norm_of_nonneg hn]
  exact (integrableOn_supWeightedKernel hq hlam hε f hf).2

/-- Almost every auxiliary clock has a finite real Stieltjes potential at every fixed rate.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem ae_integrable_aux_clock_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      IntegrableOn (fun t : ℝ => Real.exp (-q * t)) (Ioi 0)
        (pathStieltjes (supAuxLocalTime θ f)).measure := by
  filter_upwards [ae_supAuxLocalTime_continuous hθ,
    (integrable_exp_supAuxIncrement_prod hθ hq 0).prod_left_ae] with f hm hi
  exact (pathStieltjes_integral_exp ⟨hm.2.1, hm.2.2⟩ hq 0 hi).1

/-- Occupation and clock integrals use the same finite cumulative weight.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem supWeightedOccupation_eq_cumulative {q lam ε : ℝ}
    (hq : 0 < q) (hlam : 0 ≤ lam) (hε : 0 < ε) (f : DLoc) (hf : f.1 0 = 0) :
    supWeightedOccupation q lam ε f =
      ∫ s in Ioi (0 : ℝ), supOccupation ε f s.toNNReal
        ∂(supWeightStieltjes q lam hq.le hlam f).measure := by
  have hwi := (integrableOn_supWeightedKernel hq hlam hε f hf).1
  have hOi := (integral_exp_supOccupation_clock (half_pos hq) hε f hf).1
  have hc := integral_supWeight_eq_cumulative hq hlam hf
    ⟨monotone_supOccupation hε.le f, continuous_supOccupation hε f⟩
      (supOccupation_zero ε f) hOi
  have he := lintegral_supOccupation_supWeight hq hlam hε f hf
  rw [← ofReal_integral_eq_lintegral_ofReal hc.1 (ae_of_all _ fun t => (Real.exp_pos _).le),
    ← ofReal_integral_eq_lintegral_ofReal hwi (ae_of_all _ fun t =>
      mul_nonneg (Real.exp_pos _).le (supOccKernel_mem_Icc hε _).1)] at he
  have h := congrArg ENNReal.toReal he
  have heq : (∫ t in Ioi (0 : ℝ), Real.exp (-q * t - lam * supRunning f t.toNNReal)
      ∂(pathStieltjes (supOccupation ε f)).measure) = supWeightedOccupation q lam ε f := by
    simpa only [supWeightedOccupation,
      ENNReal.toReal_ofReal (integral_nonneg fun t => (Real.exp_pos _).le),
      ENNReal.toReal_ofReal (integral_nonneg fun t =>
        mul_nonneg (Real.exp_pos _).le (supOccKernel_mem_Icc hε _).1)] using h
  exact heq.symm.trans hc.2

end BGW.StableTrees
