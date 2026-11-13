/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integral limits on large events

Bounded convergence localized to a good measurable event gives an eventual integral bound,
with an explicit multiple of the measure of the complementary event.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace BGW.Probability

/-- Full-sequence bounded convergence on a good event gives an eventual integral bound, paying
only the uniform bound times the probability of its complement. -/
theorem eventually_integral_le_of_tendsto_on {Ω : Type*} [MeasurableSpace Ω]
    (P : ProbabilityMeasure Ω) {e : ℕ → Ω → ℝ} {G : Set Ω} (hG : MeasurableSet G)
    {C : ℝ} (hC : 0 ≤ C) (he : ∀ n, AEStronglyMeasurable (e n) (P : Measure Ω))
    (hbound : ∀ n, ∀ᵐ p ∂(P : Measure Ω), 0 ≤ e n p ∧ e n p ≤ C)
    (hconv : ∀ᵐ p ∂(P : Measure Ω), p ∈ G → Tendsto (fun n => e n p) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, (∫ p, e n p ∂(P : Measure Ω)) <
      C * (P : Measure Ω).real Gᶜ + ε := by
  let b : Ω → ℝ := Gᶜ.indicator (fun _ => C)
  have hb : Integrable b (P : Measure Ω) := (integrable_const C).indicator hG.compl
  let d (n : ℕ) (p : Ω) := max (e n p - b p) 0
  have hdmeas (n : ℕ) : AEStronglyMeasurable (d n) (P : Measure Ω) :=
    (continuous_max.comp_aestronglyMeasurable
      (((he n).sub hb.aestronglyMeasurable).prodMk aestronglyMeasurable_const))
  have hdlim : ∀ᵐ p ∂(P : Measure Ω), Tendsto (fun n => d n p) atTop (𝓝 0) := by
    filter_upwards [hconv, ae_all_iff.mpr hbound] with p hp hbp
    by_cases hg : p ∈ G
    · have hbzero : b p = 0 := by simp [b, hg]
      simpa only [d, hbzero, sub_zero, max_self] using
        (hp hg).max (tendsto_const_nhds (x := (0 : ℝ)))
    · have heq : (fun n => d n p) = fun _ => 0 := by
        funext n
        have hle : e n p ≤ C := (hbp n).2
        simp [d, b, hg, max_eq_right (sub_nonpos.mpr hle)]
      rw [heq]
      exact tendsto_const_nhds
  have hdint (n : ℕ) : Integrable (d n) (P : Measure Ω) := by
    apply Integrable.mono' (integrable_const C) (hdmeas n)
    filter_upwards [hbound n] with p hp
    have hbnonneg : 0 ≤ b p := (indicator_nonneg (fun _ _ => hC) p)
    dsimp [d]
    simp only [abs_of_nonneg (show (0 : ℝ) ≤ max (e n p - b p) 0 from le_max_right _ _)]
    exact max_le (by linarith only [hp.2, hbnonneg]) hC
  have hdconv : Tendsto (fun n => ∫ p, d n p ∂(P : Measure Ω)) atTop (𝓝 0) := by
    have ht := tendsto_integral_filter_of_norm_le_const
      (Eventually.of_forall hdmeas)
      (f := fun _ : Ω => (0 : ℝ)) ?_ hdlim
    · simpa only [integral_zero] using ht
    refine ⟨C, Eventually.of_forall fun n => ?_⟩
    filter_upwards [hbound n] with p hp
    have hbnonneg : 0 ≤ b p := (indicator_nonneg (fun _ _ => hC) p)
    dsimp [d]
    simp only [abs_of_nonneg (show (0 : ℝ) ≤ max (e n p - b p) 0 from le_max_right _ _)]
    exact max_le (by linarith only [hp.2, hbnonneg]) hC
  have hbeq : (∫ p, b p ∂(P : Measure Ω)) = C * (P : Measure Ω).real Gᶜ := by
    rw [integral_indicator hG.compl]
    simp [mul_comm, measureReal_def]
  filter_upwards [hdconv.eventually_lt_const hε] with n hn
  have hei : Integrable (e n) (P : Measure Ω) := by
    apply Integrable.mono' (integrable_const C) (he n)
    filter_upwards [hbound n] with p hp
    simpa only [Real.norm_eq_abs, abs_of_nonneg hp.1] using hp.2
  have hle : (∫ p, e n p ∂(P : Measure Ω)) ≤
      (∫ p, d n p ∂(P : Measure Ω)) + ∫ p, b p ∂(P : Measure Ω) := by
    rw [← integral_add (hdint n) hb]
    apply integral_mono_ae hei ((hdint n).add hb)
    filter_upwards [] with p
    have hm := le_max_left (e n p - b p) 0
    dsimp [d]
    linarith only [hm]
  rw [hbeq] at hle
  linarith

end BGW.Probability
