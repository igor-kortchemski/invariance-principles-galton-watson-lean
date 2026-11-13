/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureLaplaceSimple
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! The full excursion Laplace functional, obtained by finite-box simple approximation.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- **Laplace functional** of the point measure, for every measurable `ℝ≥0∞`-valued test `g`
(Campbell formula; `exp (-∞) = 0` on both sides):
`E exp (-∫ g dξ) = exp (-∫ (1 - exp (-g)) d(Leb ⊗ N))`. -/
theorem excursion_laplaceFunctional {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    {g : ℝ≥0 × Excursion → ℝ≥0∞} (hg : Measurable g) :
    ∫⁻ f, expNeg (∫⁻ p, g p ∂ξ f) ∂(stableLocalLaw θ : Measure DLoc) =
      expNeg (∫⁻ p, 1 - expNeg (g p) ∂(lebNN.prod (excursionMeasure θ))) :=
  by
  classical
  let P : Measure DLoc := stableLocalLaw θ
  let μ := lebNN.prod (excursionMeasure θ)
  let := sigmaFinite_excursionMeasure hθ
  let E : ℕ → Set (ℝ≥0 × Excursion) := fun n =>
    Ioc 0 (n + 1 : ℝ≥0) ×ˢ excursionLifetimeSlab n
  have hE (n : ℕ) : MeasurableSet (E n) := measurable_box (measurableSet_excursionLifetimeSlab n)
  have hEmono : Monotone E := by
    intro n m hnm
    exact Set.prod_mono (Ioc_subset_Ioc_right (by exact_mod_cast Nat.add_le_add_right hnm 1))
      (monotone_excursionLifetimeSlab hnm)
  have hcover {p : ℝ≥0 × Excursion} (hp : 0 < p.1) : ∃ n, p ∈ E n := by
    obtain ⟨i, hi⟩ := exists_nat_gt p.1
    obtain ⟨j, hj⟩ := mem_iUnion.mp (iUnion_excursionLifetimeSlab ▸ mem_univ p.2)
    refine ⟨max i j, ⟨hp, hi.le.trans ?_⟩,
      monotone_excursionLifetimeSlab (le_max_right i j) hj⟩
    exact_mod_cast (le_max_left i j).trans (Nat.le_succ (max i j))
  let s : ℕ → SimpleFunc (ℝ≥0 × Excursion) ℝ≥0∞ := fun n =>
    (SimpleFunc.eapprox g n).restrict (E n)
  have hsm (n : ℕ) : Measurable (s n) := (s n).measurable
  have hsmono : Monotone (fun n => (s n : (ℝ≥0 × Excursion) → ℝ≥0∞)) := by
    intro n m hnm p
    simp only [s, SimpleFunc.restrict_apply _ (hE _)]
    by_cases hp : p ∈ E n
    · rw [indicator_of_mem hp, indicator_of_mem (hEmono hnm hp)]
      exact SimpleFunc.monotone_eapprox g hnm p
    · rw [indicator_of_notMem hp]
      exact bot_le
  have hslim {p : ℝ≥0 × Excursion} (hp : 0 < p.1) :
      Tendsto (fun n => s n p) atTop (𝓝 (g p)) := by
    obtain ⟨i, hi⟩ := hcover hp
    have heq : (fun n => s n p) =ᶠ[atTop] (fun n => SimpleFunc.eapprox g n p) := by
      filter_upwards [eventually_ge_atTop i] with n hn
      exact SimpleFunc.restrict_apply (SimpleFunc.eapprox g n) (hE n) p |>.trans
        (indicator_of_mem (hEmono hn hi) _)
    exact (tendsto_congr' heq).mpr (SimpleFunc.tendsto_eapprox hg p)
  have hsupport (n : ℕ) : Function.support (s n) ⊆ E n := by
    intro p hp
    by_contra hn
    have hz : s n p = 0 := by simp only [s, SimpleFunc.restrict_apply _ (hE n),
      indicator_of_notMem hn]
    exact hp hz
  have hsimple (n : ℕ) :
      (∫⁻ f, expNeg (∫⁻ p, s n p ∂ξ f) ∂P) =
        expNeg (∫⁻ p, 1 - expNeg (s n p) ∂μ) :=
    excursion_laplace_simple hθ hξ hae (n + 1) (1 / (n + 1)) (by positivity) (s n) (hsupport n)
  have hξzero := (isTimeSimpleLevy_of_ae_eq_excursionPointMeasure hθ hξ hae).1.atZero
  have hsamplelim : ∀ᵐ f ∂P, Tendsto (fun n => ∫⁻ p, s n p ∂ξ f) atTop
      (𝓝 (∫⁻ p, g p ∂ξ f)) := by
    filter_upwards [hξzero] with f hf
    apply lintegral_tendsto_of_tendsto_of_monotone (fun n => (hsm n).aemeasurable)
      (Eventually.of_forall fun p n m h => hsmono h p)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hf] with p hp
    have hp0 : p.1 ≠ 0 := by simpa using hp
    exact hslim (show (0 : ℝ≥0) < p.1 from lt_of_le_of_ne bot_le hp0.symm)
  have hexpmeas (n : ℕ) : Measurable (fun f => expNeg (∫⁻ p, s n p ∂ξ f)) :=
    continuous_expNeg.measurable.comp ((Measure.measurable_lintegral (hsm n)).comp hξ)
  have hleftlim : Tendsto (fun n => ∫⁻ f, expNeg (∫⁻ p, s n p ∂ξ f) ∂P) atTop
      (𝓝 (∫⁻ f, expNeg (∫⁻ p, g p ∂ξ f) ∂P)) := by
    apply tendsto_lintegral_of_dominated_convergence (fun _ => 1) hexpmeas
      (fun _ => Eventually.of_forall fun _ => expNeg_le_one _) (by simp [P])
    exact hsamplelim.mono fun f hf => (continuous_expNeg.tendsto _).comp hf
  have hμzero : μ (({0} : Set ℝ≥0) ×ˢ univ) = 0 := by
    rw [Measure.prod_prod, lebNN_singleton_zero, zero_mul]
  have htranslim : Tendsto (fun n => ∫⁻ p, 1 - expNeg (s n p) ∂μ) atTop
      (𝓝 (∫⁻ p, 1 - expNeg (g p) ∂μ)) := by
    apply lintegral_tendsto_of_tendsto_of_monotone
      (fun n => (measurable_const.sub (continuous_expNeg.measurable.comp (hsm n))).aemeasurable)
      (Eventually.of_forall fun p n m h => tsub_le_tsub_left (antitone_expNeg (hsmono h p)) 1)
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hμzero] with p hp
    have hp0 : p.1 ≠ 0 := by simpa using hp
    exact ((ENNReal.continuous_sub_left ENNReal.one_ne_top).tendsto _).comp
      ((continuous_expNeg.tendsto _).comp
        (hslim (show (0 : ℝ≥0) < p.1 from lt_of_le_of_ne bot_le hp0.symm)))
  exact tendsto_nhds_unique hleftlim
    (by simpa only [hsimple, Function.comp_def] using (continuous_expNeg.tendsto _).comp htranslim)

end BGW.StableTrees
