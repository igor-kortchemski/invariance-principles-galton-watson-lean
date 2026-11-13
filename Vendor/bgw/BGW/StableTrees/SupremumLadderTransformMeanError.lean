/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLadderTransformMean

/-!
# Compact and tail bounds for weighted occupation error

The estimate uses compact square error and the half-rate occupation and clock means.
No expectation is interchanged with a path-dependent weight measure.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A pathwise compact-error and half-rate-tail estimate for weighted occupations.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem ae_abs_supWeightedOccupation_sub_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam ε δ : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam) (hε : 0 < ε) (hδ : 0 < δ)
    (T : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      |supWeightedOccupation q lam ε f - (supBoundaryPotential θ q lam f).toReal| ≤
        δ + supAuxApproxError θ ε T f ^ 2 / δ + Real.exp (-(q / 2) * T) *
          (supAuxOccupationTail (q / 2) ε 0 f + supAuxDiscountedTail θ (q / 2) 0 f) := by
  filter_upwards [ae_eval_zero_stableLocalLaw hθ, ae_supAuxLocalTime_continuous hθ,
    ae_integrable_aux_clock_exp hθ (half_pos hq),
    ae_supBoundaryPotential_cumulative hθ hq hlam] with f hf hm hni hrep
  have hcompact : IsCompact (Iic T) := by
    simpa only [Icc, Iic, zero_le, true_and] using
      (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T))
  let : CompactSpace (Iic T) := isCompact_iff_compactSpace.mp hcompact
  have hc : Continuous (fun t : Iic T =>
      |supOccupation ε f t - supAuxLocalTime θ f t|) :=
    (((continuous_supOccupation hε f).sub hm.2.2).abs).comp continuous_subtype_val
  have he (t : ℝ≥0) (ht : t ≤ T) :
      |supOccupation ε f t - supAuxLocalTime θ f t| ≤
        δ + supAuxApproxError θ ε T f ^ 2 / δ := by
    have hle : |supOccupation ε f t - supAuxLocalTime θ f t| ≤
        supAuxApproxError θ ε T f := le_ciSup (isCompact_range hc).bddAbove ⟨t, ht⟩
    have hs : (supAuxApproxError θ ε T f - δ) * δ ≤ supAuxApproxError θ ε T f ^ 2 := by
      nlinarith [sq_nonneg (supAuxApproxError θ ε T f - δ)]
    have hd := (le_div_iff₀ hδ).mpr hs
    linarith
  have hmi := integral_exp_supOccupation_clock (half_pos hq) hε f hf
  have hbound := abs_integral_clock_sub_le
    ⟨monotone_supOccupation hε.le f, continuous_supOccupation hε f⟩ (supOccupation_zero ε f)
    ⟨hm.2.1, hm.2.2⟩ hm.1 (supWeightStieltjes q lam hq.le hlam f).measure hq
    (fun t ht => supWeightStieltjes_measure_Ioi_le hq hlam hf ht) hmi.1 hni T
    (show 0 ≤ δ + supAuxApproxError θ ε T f ^ 2 / δ from by positivity) he
  rw [← supWeightedOccupation_eq_cumulative hq hlam hε f hf, ← hrep.2.1, hmi.2] at hbound
  exact hbound

/-- The weighted approximation error has a mean bound with a vanishing compact term and
an exponentially small tail, uniform in the occupation cutoff.

Reference: Bertoin, *Lévy Processes*, Chapter VI. -/
theorem integral_abs_supWeightedOccupation_sub_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {q lam ε δ : ℝ} (hq : 0 < q) (hlam : 0 ≤ lam) (hε : 0 < ε) (hδ : 0 < δ)
    (T : ℝ≥0) :
    (∫ f, |supWeightedOccupation q lam ε f - (supBoundaryPotential θ q lam f).toReal|
      ∂(stableLocalLaw θ : Measure DLoc)) ≤
        δ + (∫ f, supAuxApproxError θ ε T f ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) / δ +
          Real.exp (-(q / 2) * T) * (2 * ((q / 2) ^ (1 / θ) / (q / 2))) := by
  have hE : Integrable (fun f => supAuxApproxError θ ε T f ^ 2) (stableLocalLaw θ : Measure DLoc) :=
    (supOccupation_compact_L2_tendsto_supAuxLimit hθ T).1 ε hε
  have hO := integrable_supAuxOccupationTail θ (half_pos hq) hε 0
  have hM := integrable_supAuxDiscountedTail hθ (half_pos hq) 0
  have hL := ((integrable_supWeightedOccupation hθ hq hlam hε).sub
    (integrable_supBoundaryPotential_toReal hθ hq hlam)).abs
  have hR := ((integrable_const δ).add (hE.div_const δ)).add
    ((hO.add hM).const_mul (Real.exp (-(q / 2) * T)))
  have hbound := integral_mono_ae hL hR
    (ae_abs_supWeightedOccupation_sub_le hθ hq hlam hε hδ T)
  have hOmean : (∫ f, supAuxOccupationTail (q / 2) ε 0 f ∂(stableLocalLaw θ : Measure DLoc)) ≤
      (q / 2) ^ (1 / θ) / (q / 2) := by
    rw [integral_supAuxOccupationTail_zero]
    exact (supOccupationResolvent_mem_Icc hθ (half_pos hq) hε 0).2
  have hMmean : (∫ f, supAuxDiscountedTail θ (q / 2) 0 f ∂(stableLocalLaw θ : Measure DLoc)) =
      (q / 2) ^ (1 / θ) / (q / 2) := by
    rw [integral_supAuxDiscountedTail_zero hθ (half_pos hq), supPotential_zero hθ (half_pos hq)]
  have hsplit : (∫ f, δ + supAuxApproxError θ ε T f ^ 2 / δ +
      Real.exp (-(q / 2) * T) *
        (supAuxOccupationTail (q / 2) ε 0 f + supAuxDiscountedTail θ (q / 2) 0 f)
          ∂(stableLocalLaw θ : Measure DLoc)) =
      (∫ f, δ + supAuxApproxError θ ε T f ^ 2 / δ ∂(stableLocalLaw θ : Measure DLoc)) +
        ∫ f, Real.exp (-(q / 2) * T) *
          (supAuxOccupationTail (q / 2) ε 0 f + supAuxDiscountedTail θ (q / 2) 0 f)
            ∂(stableLocalLaw θ : Measure DLoc) :=
    integral_add ((integrable_const δ).add (hE.div_const δ))
      ((hO.add hM).const_mul (Real.exp (-(q / 2) * T)))
  have hfirst : (∫ f, δ + supAuxApproxError θ ε T f ^ 2 / δ ∂(stableLocalLaw θ : Measure DLoc)) =
      δ + (∫ f, supAuxApproxError θ ε T f ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) / δ := by
    rw [integral_add (integrable_const δ) (hE.div_const δ), integral_const, integral_div]
    simp
  have hsecond : (∫ f, Real.exp (-(q / 2) * T) *
      (supAuxOccupationTail (q / 2) ε 0 f + supAuxDiscountedTail θ (q / 2) 0 f)
        ∂(stableLocalLaw θ : Measure DLoc)) =
      Real.exp (-(q / 2) * T) * ((∫ f, supAuxOccupationTail (q / 2) ε 0 f
        ∂(stableLocalLaw θ : Measure DLoc)) +
        ∫ f, supAuxDiscountedTail θ (q / 2) 0 f ∂(stableLocalLaw θ : Measure DLoc)) := by
    rw [integral_const_mul, integral_add hO hM]
  change (∫ f, |supWeightedOccupation q lam ε f - (supBoundaryPotential θ q lam f).toReal|
    ∂(stableLocalLaw θ : Measure DLoc)) ≤ _
  calc
    _ ≤ _ := hbound
    _ = _ := hsplit
    _ = δ + (∫ f, supAuxApproxError θ ε T f ^ 2 ∂(stableLocalLaw θ : Measure DLoc)) / δ +
        Real.exp (-(q / 2) * T) * ((∫ f, supAuxOccupationTail (q / 2) ε 0 f
          ∂(stableLocalLaw θ : Measure DLoc)) +
          ∫ f, supAuxDiscountedTail θ (q / 2) 0 f
            ∂(stableLocalLaw θ : Measure DLoc)) := by rw [hfirst, hsecond]
    _ ≤ _ := by rw [hMmean]; nlinarith [hOmean, Real.exp_pos (-(q / 2) * T)]

end BGW.StableTrees
