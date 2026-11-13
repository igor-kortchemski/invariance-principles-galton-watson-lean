/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumFactorizationKernel

/-! # Independence of the supremum and drawdown at an exponential time

For the spectrally positive `θ`-stable process (`1 < θ ≤ 2`) and an independent exponential
clock `e_q` (`expClockLaw θ q`), the supremum `S_{e_q}` and the drawdown `S_{e_q} - X_{e_q}` are
independent (`indepFun_supRunning_supReflected_expTime`), with product and resolvent forms
(`lintegral_mul_supRunning_supReflected_expTime`,
`lintegral_resolvent_mul_supRunning_supReflected`). The proof splits the clock at the excursion of
`X - I` that straddles it (compensation formula for the excursion point measure) and transfers the
resulting factorization of `(-I_{e_q}, X_{e_q} - I_{e_q})` by time reversal.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
* A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed., Springer, 2014,
  Chapter 6 (Wiener–Hopf factorization).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem product_of_excursion_factors {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ p, F (supRunning p.1 p.2.toNNReal) * G (supReflected p.1 p.2.toNNReal)
      ∂expClockLaw θ q) =
    (∫⁻ p, F (supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q) *
      ∫⁻ p, G (supReflected p.1 p.2.toNNReal) ∂expClockLaw θ q := by
  let := isProbabilityMeasure_expClockLaw θ hq
  let A : (ℝ → ℝ≥0∞) → ℝ≥0∞ := fun K =>
    ∫⁻ f, (∫⁻ x, expNeg (ENNReal.ofReal q * passagePast x f) * K x ∂lebNN)
      ∂(stableLocalLaw θ : Measure DLoc)
  let B : (ℝ → ℝ≥0∞) → ℝ≥0∞ := fun K =>
    ∫⁻ e, excursionDiscount q K e ∂excursionMeasure θ
  have hbase := lintegral_supRunning_supReflected_excursion_factors hθ hq hF hG
  have hleft := lintegral_supRunning_supReflected_excursion_factors hθ hq hF
    (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞)))
  have hright := lintegral_supRunning_supReflected_excursion_factors hθ hq
    (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞))) hG
  have hone := lintegral_supRunning_supReflected_excursion_factors hθ hq
    (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞)))
    (measurable_const : Measurable (fun _ : ℝ => (1 : ℝ≥0∞)))
  have hL : (∫⁻ p, F (supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q) =
      A (fun _ => 1) * B F := by
    calc
      _ = ∫⁻ p, F (supRunning p.1 p.2.toNNReal) * 1 ∂expClockLaw θ q := by
        simp only [mul_one]
      _ = _ := hleft
  have hR : (∫⁻ p, G (supReflected p.1 p.2.toNNReal) ∂expClockLaw θ q) =
      A G * B (fun _ => 1) := by
    calc
      _ = ∫⁻ p, 1 * G (supReflected p.1 p.2.toNNReal) ∂expClockLaw θ q := by
        simp only [one_mul]
      _ = _ := hright
  have hn : A (fun _ => 1) * B (fun _ => 1) = 1 := by
    calc
      _ = ∫⁻ _p : DLoc × ℝ, (1 : ℝ≥0∞) * 1 ∂expClockLaw θ q := hone.symm
      _ = _ := by simp
  rw [hbase, hL, hR]
  change A G * B F = (A (fun _ => 1) * B F) * (A G * B (fun _ => 1))
  calc
    _ = (A (fun _ => 1) * B (fun _ => 1)) * (A G * B F) := by rw [hn, one_mul]
    _ = _ := by ac_rfl

/-- **Independence of the supremum and the drawdown at an independent exponential time.**
`S_{e_q}` and `S_{e_q} - X_{e_q}` are independent under `P ⊗ Exp(q)`, for every `q > 0`. -/
theorem indepFun_supRunning_supReflected_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) :
    IndepFun (fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal)
      (fun p : DLoc × ℝ => supReflected p.1 p.2.toNNReal) (expClockLaw θ q) := by
  classical
  rw [indepFun_iff_measure_inter_preimage_eq_mul]
  intro s t hs ht
  have he := product_of_excursion_factors hθ hq
    (measurable_const.indicator hs : Measurable (s.indicator (fun _ => (1 : ℝ≥0∞))))
    (measurable_const.indicator ht : Measurable (t.indicator (fun _ => (1 : ℝ≥0∞))))
  have hmS := measurable_supRunning_expTime hs
  have hmR := measurable_supReflected_expTime ht
  have hiS : (fun p : DLoc × ℝ => s.indicator (fun _ => (1 : ℝ≥0∞))
      (supRunning p.1 p.2.toNNReal)) =
      ((fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) ⁻¹' s).indicator (fun _ => 1) := rfl
  have hiR : (fun p : DLoc × ℝ => t.indicator (fun _ => (1 : ℝ≥0∞))
      (supReflected p.1 p.2.toNNReal)) =
      ((fun p : DLoc × ℝ => supReflected p.1 p.2.toNNReal) ⁻¹' t).indicator (fun _ => 1) := rfl
  have hi : (fun p : DLoc × ℝ => s.indicator (fun _ => (1 : ℝ≥0∞))
      (supRunning p.1 p.2.toNNReal) *
        t.indicator (fun _ => (1 : ℝ≥0∞)) (supReflected p.1 p.2.toNNReal)) =
      (((fun p : DLoc × ℝ => supRunning p.1 p.2.toNNReal) ⁻¹' s) ∩
        ((fun p : DLoc × ℝ => supReflected p.1 p.2.toNNReal) ⁻¹' t)).indicator
          (fun _ => 1) := by
    funext p
    by_cases hps : supRunning p.1 p.2.toNNReal ∈ s <;>
      by_cases hpt : supReflected p.1 p.2.toNNReal ∈ t <;>
        simp [hps, hpt]
  rw [hi, hiS, hiR, lintegral_indicator_const (hmS.inter hmR),
    lintegral_indicator_const hmS, lintegral_indicator_const hmR] at he
  simpa only [mul_one, one_mul] using he

/-- **Product form** in `ℝ≥0∞` (no integrability needed): for Borel `F G : ℝ → ℝ≥0∞`,
`E[F(S_{e_q}) G(R_{e_q})] = E[F(S_{e_q})] · E[G(R_{e_q})]`. -/
theorem lintegral_mul_supRunning_supReflected_expTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ p, F (supRunning p.1 p.2.toNNReal) * G (supReflected p.1 p.2.toNNReal) ∂expClockLaw θ q =
      (∫⁻ p, F (supRunning p.1 p.2.toNNReal) ∂expClockLaw θ q) *
        ∫⁻ p, G (supReflected p.1 p.2.toNNReal) ∂expClockLaw θ q := 
  product_of_excursion_factors hθ hq hF hG

/-- **Resolvent form** (same statement without the clock space): with `q e^{-qt} dt` weights on
`[0, ∞)`, `∫ q e^{-qt} E[F(S_t) G(R_t)] dt` factors.  Derived from the product form by Tonelli. -/
theorem lintegral_resolvent_mul_supRunning_supReflected {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 < q) {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
        ∫⁻ f, F (supRunning f t.toNNReal) * G (supReflected f t.toNNReal)
          ∂(stableLocalLaw θ : Measure DLoc) =
      (∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
          ∫⁻ f, F (supRunning f t.toNNReal) ∂(stableLocalLaw θ : Measure DLoc)) *
        ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (q * Real.exp (-q * t)) *
          ∫⁻ f, G (supReflected f t.toNNReal) ∂(stableLocalLaw θ : Measure DLoc) := by
  have hPair : Measurable (fun p : DLoc × ℝ =>
      F (supRunning p.1 p.2.toNNReal) * G (supReflected p.1 p.2.toNNReal)) :=
    (hF.comp measurable_supRunning_expTime).mul (hG.comp measurable_supReflected_expTime)
  have hFC : Measurable (fun p : DLoc × ℝ => F (supRunning p.1 p.2.toNNReal)) :=
    hF.comp measurable_supRunning_expTime
  have hGC : Measurable (fun p : DLoc × ℝ => G (supReflected p.1 p.2.toNNReal)) :=
    hG.comp measurable_supReflected_expTime
  have he := lintegral_mul_supRunning_supReflected_expTime hθ hq hF hG
  rw [lintegral_expClockLaw θ hq hPair, lintegral_expClockLaw θ hq hFC,
    lintegral_expClockLaw θ hq hGC] at he
  exact he

end BGW.StableTrees
