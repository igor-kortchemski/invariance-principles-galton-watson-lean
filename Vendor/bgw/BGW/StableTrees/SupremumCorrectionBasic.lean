/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotential
public import BGW.StableTrees.SupremumAuxLocalTime

/-!
# Zero-resolvent correction and discounted error processes

Definitions of the centered error and its positive-rate approximants, and elementary
bounds for the correction. The auxiliary clock retains its raw adapted representative.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- `V_ε = (1/Γ(θ) + 1/2) ε^{θ-1}`: explicit bound for `sup_{y ≥ 0} |v_ε(y)|`. -/
noncomputable def supCorrectionBound (θ ε : ℝ) : ℝ := (1 / Real.Gamma θ + 1 / 2) * ε ^ (θ - 1)

/-- The correction increment `w_t = v_ε(R_t) - v_ε(0)`, `R_t = R^0_t`. -/
noncomputable def occupationCorrection (θ ε : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  supCorrection θ ε (supReflectedFrom 0 f t) - supCorrection θ ε 0

/-- **The error process** `D_t = O_ε(t) - M^*_t + v_ε(R_t) - v_ε(0)`,
with `M^* = supAuxLocalTime`. -/
noncomputable def errorMartingale (θ ε : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  (supOccupation ε f t - supAuxLocalTime θ f t) + occupationCorrection θ ε t f

/-- Discounted head of the clock, `∫_{(0,t]} e^{-qs} dM^*_s`, by integration by parts
(`M^*_0 = 0`): `e^{-qt} M^*_t + q ∫_0^t e^{-qs} M^*_s ds`.  Adapted for every path. -/
noncomputable def supAuxDiscountedHead (θ q : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  Real.exp (-q * t) * supAuxLocalTime θ f t +
    q * ∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s) * supAuxLocalTime θ f s.toNNReal

/-- Discounted head of the occupation, `O^q_t = ∫_0^t e^{-qs} g_ε(R^0_s) ds`. -/
noncomputable def supOccupationDiscountedHead (q ε : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  ∫ s in Ioc (0 : ℝ) t, Real.exp (-q * s) * supOccKernel ε (supReflectedFrom 0 f s.toNNReal)

/-- **Positive-rate error martingale**
`N^q_t = O^q_t - M^q_t + e^{-qt} (u^q_ε - h_q)(R_t)`. -/
noncomputable def discountedErrorMartingale (θ q ε : ℝ) (t : ℝ≥0) (f : DLoc) : ℝ :=
  (supOccupationDiscountedHead q ε t f - supAuxDiscountedHead θ q t f) +
    Real.exp (-q * t) * (supOccupationResolvent θ q ε (supReflectedFrom 0 f t) -
      supPotential θ q (supReflectedFrom 0 f t))

/-- Strict exit time `τ_K = inf{t | R^0_t > K}` (`⊤` if never). -/
noncomputable def supReflectedExit (K : ℝ) (f : DLoc) : ℝ≥0∞ :=
  ⨅ t : ℝ≥0, if K < supReflectedFrom 0 f t then (t : ℝ≥0∞) else ⊤

/-- The localizing cutoff `min (τ_n) n` (independent of the inverse clock). -/
noncomputable def errCutoff (n : ℕ) (f : DLoc) : ℝ≥0∞ :=
  min (supReflectedExit (n : ℝ) f) (n : ℝ≥0∞)

/-- The stopping epoch `min (min t σ) (cutoff n)` as a finite time. -/
noncomputable def errStopTime (n : ℕ) (σ : DLoc → ℝ≥0∞) (t : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  (min (min (t : ℝ≥0∞) (σ f)) (errCutoff n f)).toNNReal

/-- The correction is Borel measurable, including outside the stable parameter range. -/
theorem measurable_supCorrection (θ ε : ℝ) : Measurable (supCorrection θ ε) := by
  have hs : Measurable (stableScale θ) := by
    unfold stableScale
    exact ((measurable_id.pow_const (θ - 1)).div_const _).ite
      (measurableSet_le measurable_const measurable_id) measurable_const
  have hi : Measurable (fun x => ∫ r in Ioc 0 ε, stableScale θ (x - r)) := by
    exact ((hs.comp (measurable_fst.sub measurable_snd)).stronglyMeasurable.integral_prod_right'
      (ν := volume.restrict (Ioc 0 ε))).measurable
  exact (hs.sub (hi.const_mul _)).sub measurable_const

/-- The correction increment is bounded uniformly in the path and time. -/
theorem abs_occupationCorrection_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε : ℝ} (hε : 0 < ε)
    (t : ℝ≥0) (f : DLoc) : |occupationCorrection θ ε t f| ≤ 2 * supCorrectionBound θ ε := by
  have hR := abs_supCorrection_le hθ hε (supReflectedFrom_nonneg 0 f t)
  have h0 := abs_supCorrection_le hθ hε (le_refl (0 : ℝ))
  exact (abs_sub _ _).trans (by dsimp [supCorrectionBound]; linarith)

/-- The correction increment vanishes on the contact set. -/
theorem occupationCorrection_eq_zero {θ ε : ℝ} {t : ℝ≥0} {f : DLoc}
    (h : supReflectedFrom 0 f t = 0) : occupationCorrection θ ε t f = 0 := by
  simp [occupationCorrection, h]

/-- The uniform correction bound vanishes as the occupation width tends to zero. -/
theorem tendsto_supCorrectionBound {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    Tendsto (supCorrectionBound θ) (𝓝[>] 0) (𝓝 0) := by
  have he : 0 < θ - 1 := by linarith [hθ.1]
  have ht : Tendsto (fun ε : ℝ => ε ^ (θ - 1)) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow he.ne'] using
      ((Real.continuousAt_rpow_const 0 (θ - 1) (Or.inr he.le)).tendsto.mono_left
        nhdsWithin_le_nhds : Tendsto _ (𝓝[>] (0 : ℝ)) _)
  unfold supCorrectionBound
  convert ht.const_mul (1 / Real.Gamma θ + 1 / 2) using 1
  simp only [mul_zero]

/-- The cutoff is bounded by its deterministic integer horizon. -/
theorem errCutoff_le (n : ℕ) (f : DLoc) : errCutoff n f ≤ n := min_le_right _ _

/-- Increasing the state threshold delays its strict exit. -/
private theorem monotone_supReflectedExit (f : DLoc) :
    Monotone (fun K : ℝ => supReflectedExit K f) := by
  intro K L hKL
  apply iInf_mono
  intro t
  by_cases hL : L < supReflectedFrom 0 f t
  · simp only [ite_eq_left hL, ite_eq_left (hKL.trans_lt hL), le_refl]
  · simp only [ite_eq_right hL, le_top]

/-- The cutoffs increase with their integer level. -/
theorem monotone_errCutoff (f : DLoc) : Monotone (fun n : ℕ => errCutoff n f) := by
  intro n m hnm
  exact min_le_min (monotone_supReflectedExit f (Nat.cast_le.mpr hnm))
    (Nat.cast_le.mpr hnm)

end BGW.StableTrees
