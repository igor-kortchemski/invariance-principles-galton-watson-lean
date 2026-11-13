/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumDrawdown
public import BGW.StableTrees.SupremumReflectedFamily
public import BGW.Probability.DoobL2Resolvent
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Supremum potentials and reflected occupation resolvents

Analytic functions for the scale series, exponential-clock supremum tail, and
occupation resolvents of the reflected stable family.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- `W(x) = x^{θ-1}/Γ(θ)` for `x ≥ 0`, `0` for `x < 0`. -/
noncomputable def stableScale (θ x : ℝ) : ℝ :=
  if 0 ≤ x then x ^ (θ - 1) / Real.Gamma θ else 0

/-- Term `q^n x^{θ(n+1)-1}/Γ(θ(n+1))` of `W_q`. -/
noncomputable def stableSeriesTerm (θ q : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  q ^ n * x ^ (θ * (n + 1) - 1) / Real.Gamma (θ * (n + 1))

/-- Term `q^n x^{θ(n+1)-2}/Γ(θ(n+1)-1)` of `W_q'`. -/
noncomputable def stableSeriesDerivTerm (θ q : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  q ^ n * x ^ (θ * (n + 1) - 2) / Real.Gamma (θ * (n + 1) - 1)

/-- `W_q(x)` for `x ≥ 0`, `0` for `x < 0`. -/
noncomputable def stableSeries (θ q x : ℝ) : ℝ :=
  if 0 ≤ x then ∑' n : ℕ, stableSeriesTerm θ q n x else 0

/-- Termwise derivative of `W_q` on `(0,∞)`, `0` elsewhere. -/
noncomputable def stableSeriesDeriv (θ q x : ℝ) : ℝ :=
  if 0 < x then ∑' n : ℕ, stableSeriesDerivTerm θ q n x else 0

/-- `H_q(x) = P(S_{e_q} ≥ x)` for `x ≥ 0`, extended by `1` for `x < 0`. -/
noncomputable def supExpTail (θ q x : ℝ) : ℝ :=
  if x < 0 then 1 else (expClockLaw θ q {p | x ≤ supRunning p.1 p.2.toNNReal}).toReal

/-- `h_q = (Φ/q) H_q`, `Φ = q^{1/θ}`. -/
noncomputable def supPotential (θ q x : ℝ) : ℝ := q ^ (1 / θ) / q * supExpTail θ q x

/-- The occupation kernel `g_ε(r) = ε⁻¹ 1{r < ε}`. -/
noncomputable def supOccKernel (ε r : ℝ) : ℝ := Set.indicator (Set.Iio ε) (fun _ => ε⁻¹) r

/-- `q`-resolvent of the reflected family on a bounded Borel `k`:
`y ↦ E ∫_0^∞ e^{-qt} k(R^y_t) dt` (start `y.toNNReal`). -/
noncomputable def reflectedResolvent (θ q : ℝ) (k : ℝ → ℝ) (y : ℝ) : ℝ :=
  ∫ f, (∫ t in Set.Ioi (0 : ℝ),
    Real.exp (-q * t) * k (supReflectedFrom y.toNNReal f t.toNNReal))
    ∂(stableLocalLaw θ : Measure DLoc)

/-- `u^q_ε = reflectedResolvent θ q g_ε`. -/
noncomputable def supOccupationResolvent (θ q ε : ℝ) (y : ℝ) : ℝ :=
  reflectedResolvent θ q (supOccKernel ε) y

/-- The zero-resolvent correction `v_ε`. -/
noncomputable def supCorrection (θ ε x : ℝ) : ℝ :=
  stableScale θ x - ε⁻¹ * (∫ r in Set.Ioc 0 ε, stableScale θ (x - r)) -
    (if θ = 2 then ε / 2 else 0)

/-- The scale vanishes on the nonpositive half-line for a stable index. -/
theorem stableScale_eq_zero {θ x : ℝ} (hθ : 1 < θ) (hx : x ≤ 0) :
    stableScale θ x = 0 := by
  rcases hx.eq_or_lt with rfl | hx
  · simp [stableScale, Real.zero_rpow (by linarith : θ - 1 ≠ 0)]
  · simp [stableScale, not_le.mpr hx]

/-- The scale series vanishes at its left endpoint. -/
theorem stableSeries_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) : stableSeries θ q 0 = 0 := by
  unfold stableSeries
  simp only [le_refl, ite_true]
  have heq : (fun n : ℕ => stableSeriesTerm θ q n 0) = fun _ => 0 := by
    funext n
    have hn : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have he : θ * (n + 1) - 1 ≠ 0 := by nlinarith [hθ.1]
    simp [stableSeriesTerm, Real.zero_rpow he]
  simp only [heq, tsum_zero]

/-- The exponential-clock supremum tail equals one at zero. -/
theorem supExpTail_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    supExpTail θ q 0 = 1 := by
  let := isProbabilityMeasure_expClockLaw θ hq
  have he : expClockLaw θ q {p | 0 ≤ supRunning p.1 p.2.toNNReal} = 1 := by
    have hae := (ae_nonneg_supRunning_supReflected_expTime hθ hq).mono (fun _ hp => hp.1)
    have heq : {p : DLoc × ℝ | 0 ≤ supRunning p.1 p.2.toNNReal} =ᵐ[expClockLaw θ q]
        (Set.univ : Set (DLoc × ℝ)) := by
      filter_upwards [hae] with p hp
      change (0 ≤ supRunning p.1 p.2.toNNReal) = True
      exact eq_true hp
    rw [measure_congr heq, measure_univ]
  simp [supExpTail, he]

/-- The exponential-clock tail takes values in the unit interval. -/
theorem supExpTail_mem_Icc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) (x : ℝ) :
    supExpTail θ q x ∈ Icc (0 : ℝ) 1 := by
  let := isProbabilityMeasure_expClockLaw θ hq
  -- `hθ` is part of the stated interface; this holds for every θ.
  have _hθ := hθ
  unfold supExpTail
  split_ifs
  · exact ⟨zero_le_one, le_refl _⟩
  · exact ⟨ENNReal.toReal_nonneg, measureReal_le_one⟩

/-- The exponential-clock supremum tail is nonincreasing. -/
theorem antitone_supExpTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    Antitone (supExpTail θ q) := by
  let := isProbabilityMeasure_expClockLaw θ hq
  intro x y hxy
  by_cases hx : x < 0
  · simpa [supExpTail, hx] using (supExpTail_mem_Icc hθ hq y).2
  · have hy : ¬y < 0 := not_lt.mpr (le_trans (not_lt.mp hx) hxy)
    simp only [supExpTail, hx, hy, ite_false]
    exact ENNReal.toReal_mono (measure_ne_top _ _)
      (measure_mono (fun _ hp => le_trans hxy hp))

/-- The boundary potential has the required normalization. -/
theorem supPotential_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    supPotential θ q 0 = q ^ (1 / θ) / q := by
  simp [supPotential, supExpTail_zero hθ hq]

/-- The potential lies between zero and its boundary value. -/
theorem supPotential_mem_Icc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) (x : ℝ) :
    supPotential θ q x ∈ Icc (0 : ℝ) (q ^ (1 / θ) / q) := by
  have hc : 0 ≤ q ^ (1 / θ) / q := le_of_lt (div_pos (Real.rpow_pos_of_pos hq _) hq)
  obtain ⟨h0, h1⟩ := supExpTail_mem_Icc hθ hq x
  exact ⟨mul_nonneg hc h0, (mul_le_mul_of_nonneg_left h1 hc).trans_eq (mul_one _)⟩

/-- The occupation cutoff is a Borel function. -/
theorem measurable_supOccKernel (ε : ℝ) : Measurable (supOccKernel ε) := by
  exact measurable_const.indicator measurableSet_Iio

/-- The positive occupation kernel lies in its sharp constant interval. -/
theorem supOccKernel_mem_Icc {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    supOccKernel ε r ∈ Icc (0 : ℝ) ε⁻¹ := by
  by_cases hr : r ∈ Iio ε
  · simp [supOccKernel, hr, (inv_pos.mpr hε).le]
  · simp [supOccKernel, hr, (inv_pos.mpr hε).le]

/-- The correction at the reflecting boundary. -/
theorem supCorrection_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε) :
    supCorrection θ ε 0 = -(if θ = 2 then ε / 2 else 0) := by
  -- `hε` is part of the stated interface; this holds for every ε.
  have _hε := hε
  have hi : (∫ r in Ioc 0 ε, stableScale θ (0 - r)) = 0 := by
    apply setIntegral_eq_zero_of_forall_eq_zero
    intro r hr
    exact stableScale_eq_zero hθ.1 (by linarith [hr.1])
  unfold supCorrection
  rw [hi, stableScale_eq_zero hθ.1 le_rfl]
  ring

/-- The boundary potential gives the Brownian correction exponent. -/
theorem supPotential_zero_mul {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q) :
    q ^ (1 / θ) * supPotential θ q 0 = q ^ (2 / θ - 1) := by
  rw [supPotential_zero hθ hq, Real.rpow_sub hq, Real.rpow_one,
    show 2 / θ = 1 / θ + 1 / θ by ring, Real.rpow_add hq]
  ring

/-- The scalar correction exponent distinguishes the Brownian endpoint. -/
theorem tendsto_rpow_two_div_sub_one {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Tendsto (fun q : ℝ => q ^ (2 / θ - 1)) (𝓝[>] 0) (𝓝 (if θ = 2 then 1 else 0)) := by
  by_cases he : θ = 2
  · subst θ
    norm_num
  · have ht : 0 < θ := by linarith [hθ.1]
    have ha : 0 < 2 / θ - 1 := by
      have : θ < 2 := lt_of_le_of_ne hθ.2 he
      exact sub_pos.mpr ((lt_div_iff₀ ht).2 (by simpa using this))
    simp only [he, ite_false]
    simpa only [Real.zero_rpow ha.ne'] using
      ((Real.continuousAt_rpow_const 0 (2 / θ - 1) (Or.inr ha.le)).tendsto.mono_left
        nhdsWithin_le_nhds)

end BGW.StableTrees
