/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.PathTailTestFunctions
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Comparing test integrals through localized reconstruction

The comparison uses equality on a finite-prefix event and full-sequence convergence on a
large good event. All error terms are bounded by measurable indicators.
-/

@[expose] public section

open MeasureTheory Set Filter
open scoped Topology
open BGW.Probability

namespace BGW.StableTrees.PathTail

/-- Scalar integral comparison when reconstruction is almost everywhere exact on observable
events and converges on a large good event. The estimate pays four times the test bound on the
bad limiting event. -/
theorem eventually_abs_integral_sub_le_of_reconstruction_ae {Ω Γ S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace S]
    (P₀ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Γ)
    (a : ℕ → Ω → ℝ) (b : ℕ → S → ℝ) (o : ℕ → Ω → S) (Y : ℕ → Γ → S)
    (z : Γ → ℝ) (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n))
    (ho : ∀ n, Measurable (o n)) (hY : ∀ n, Measurable (Y n))
    (hz : AEStronglyMeasurable z (P : Measure Γ))
    (hlaw : ∀ n, (P : Measure Γ).map (Y n) = (P₀ : Measure Ω).map (o n))
    (E : ℕ → Set S) (hE : ∀ n, MeasurableSet (E n))
    (hexact : ∀ n, ∀ᵐ ω ∂(P₀ : Measure Ω), o n ω ∈ E n → a n ω = b n (o n ω))
    (G : Set Γ) (hG : MeasurableSet G) {C : ℝ} (hC : 0 ≤ C)
    (haC : ∀ n ω, |a n ω| ≤ C) (hbC : ∀ n y, |b n y| ≤ C) (hzC : ∀ p, |z p| ≤ C)
    (hconv : ∀ᵐ p ∂(P : Measure Γ), p ∈ G →
      Tendsto (fun n => b n (Y n p)) atTop (𝓝 (z p)) ∧
        ∀ᶠ n in atTop, Y n p ∈ E n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      |(∫ ω, a n ω ∂(P₀ : Measure Ω)) - ∫ p, z p ∂(P : Measure Γ)| <
        4 * C * (P : Measure Γ).real Gᶜ + ε := by
  let q (n : ℕ) : S → ℝ := (E n)ᶜ.indicator (fun _ => 2 * C)
  have hq (n : ℕ) : Measurable (q n) := measurable_const.indicator (hE n).compl
  let e (n : ℕ) (p : Γ) := |b n (Y n p) - z p| + q n (Y n p)
  have hbi (n : ℕ) : Integrable (fun p => b n (Y n p)) (P : Measure Γ) :=
    ⟨((hb n).comp (hY n)).aestronglyMeasurable,
      HasFiniteIntegral.of_bounded (Eventually.of_forall fun p => by
        simpa only [Real.norm_eq_abs] using hbC n (Y n p))⟩
  have hzi : Integrable z (P : Measure Γ) :=
    ⟨hz, HasFiniteIntegral.of_bounded (Eventually.of_forall fun p => by
      simpa only [Real.norm_eq_abs] using hzC p)⟩
  have hqi (n : ℕ) : Integrable (fun p => q n (Y n p)) (P : Measure Γ) := by
    refine ⟨((hq n).comp (hY n)).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 2 * C) ?_⟩
    filter_upwards [] with p
    by_cases hp : Y n p ∈ (E n)ᶜ <;> simp [q, hp, abs_of_nonneg hC, hC]
  have hei (n : ℕ) : Integrable (e n) (P : Measure Γ) :=
    (hbi n |>.sub hzi |>.abs).add (hqi n)
  have hebound (n : ℕ) : ∀ᵐ p ∂(P : Measure Γ), 0 ≤ e n p ∧ e n p ≤ 4 * C := by
    filter_upwards [] with p
    have hab : |b n (Y n p) - z p| ≤ 2 * C :=
      (abs_sub _ _).trans (by linarith only [hbC n (Y n p), hzC p])
    have hqbounds : 0 ≤ q n (Y n p) ∧ q n (Y n p) ≤ 2 * C := by
      by_cases hp : Y n p ∈ (E n)ᶜ <;> simp [q, hp, hC]
    exact ⟨add_nonneg (abs_nonneg _) hqbounds.1, by dsimp [e]; linarith⟩
  have helim : ∀ᵐ p ∂(P : Measure Γ), p ∈ G →
      Tendsto (fun n => e n p) atTop (𝓝 0) := by
    filter_upwards [hconv] with p hp hg
    obtain ⟨hc, hev⟩ := hp hg
    have hzero : ∀ᶠ n in atTop, q n (Y n p) = 0 := by
      filter_upwards [hev] with n hn
      simp [q, hn]
    have hqzero : Tendsto (fun n => q n (Y n p)) atTop (𝓝 0) :=
      tendsto_const_nhds.congr' (hzero.mono fun _ hn => hn.symm)
    simpa only [sub_self, abs_zero, add_zero] using (hc.sub_const (z p)).abs.add hqzero
  have hsmall := eventually_integral_le_of_tendsto_on P hG (by positivity : 0 ≤ 4 * C)
    (fun n => (hei n).aestronglyMeasurable) hebound helim hε
  filter_upwards [hsmall] with n hn
  have hai : Integrable (a n) (P₀ : Measure Ω) :=
    ⟨(ha n).aestronglyMeasurable, HasFiniteIntegral.of_bounded
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using haC n ω)⟩
  have hboi : Integrable (fun ω => b n (o n ω)) (P₀ : Measure Ω) :=
    ⟨((hb n).comp (ho n)).aestronglyMeasurable, HasFiniteIntegral.of_bounded
      (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbC n (o n ω))⟩
  have hqoi : Integrable (fun ω => q n (o n ω)) (P₀ : Measure Ω) := by
    refine ⟨((hq n).comp (ho n)).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := 2 * C) ?_⟩
    filter_upwards [] with ω
    by_cases hp : o n ω ∈ (E n)ᶜ <;> simp [q, hp, abs_of_nonneg hC, hC]
  have htransfer (v : S → ℝ) (hv : Measurable v) :
      (∫ ω, v (o n ω) ∂(P₀ : Measure Ω)) = ∫ p, v (Y n p) ∂(P : Measure Γ) := by
    rw [← integral_map (ho n).aemeasurable hv.aestronglyMeasurable,
      ← hlaw n, integral_map (hY n).aemeasurable hv.aestronglyMeasurable]
  have hfirst : |(∫ ω, a n ω ∂(P₀ : Measure Ω)) -
      ∫ p, b n (Y n p) ∂(P : Measure Γ)| ≤ ∫ p, q n (Y n p) ∂(P : Measure Γ) := by
    rw [← htransfer (b n) (hb n), ← htransfer (q n) (hq n), ← integral_sub hai hboi]
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    apply integral_mono_ae (hai.sub hboi).norm hqoi
    filter_upwards [hexact n] with ω hω
    by_cases hp : o n ω ∈ E n
    · simp [hω hp, q, hp]
    · have hab := (abs_sub (a n ω) (b n (o n ω))).trans
        (add_le_add (haC n ω) (hbC n (o n ω)))
      simpa [q, hp, Real.norm_eq_abs, two_mul] using hab
  have hsecond : |(∫ p, b n (Y n p) ∂(P : Measure Γ)) -
      ∫ p, z p ∂(P : Measure Γ)| ≤ ∫ p, |b n (Y n p) - z p| ∂(P : Measure Γ) := by
    rw [← integral_sub (hbi n) hzi]
    simpa only [Real.norm_eq_abs] using
      (norm_integral_le_integral_norm (fun p => b n (Y n p) - z p)
        (μ := (P : Measure Γ)))
  have hab := abs_sub_le ((∫ ω, a n ω ∂(P₀ : Measure Ω)))
    ((∫ p, b n (Y n p) ∂(P : Measure Γ))) ((∫ p, z p ∂(P : Measure Γ)))
  have heq : (∫ p, e n p ∂(P : Measure Γ)) =
      (∫ p, |b n (Y n p) - z p| ∂(P : Measure Γ)) +
        ∫ p, q n (Y n p) ∂(P : Measure Γ) := integral_add ((hbi n).sub hzi).abs (hqi n)
  linarith

/-- Scalar integral comparison when reconstruction is exact on observable events and converges
on a large good event. The estimate pays four times the test bound on the bad limiting event. -/
theorem eventually_abs_integral_sub_le_of_reconstruction {Ω Γ S : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [MeasurableSpace S]
    (P₀ : ProbabilityMeasure Ω) (P : ProbabilityMeasure Γ)
    (a : ℕ → Ω → ℝ) (b : ℕ → S → ℝ) (o : ℕ → Ω → S) (Y : ℕ → Γ → S)
    (z : Γ → ℝ) (ha : ∀ n, Measurable (a n)) (hb : ∀ n, Measurable (b n))
    (ho : ∀ n, Measurable (o n)) (hY : ∀ n, Measurable (Y n))
    (hz : AEStronglyMeasurable z (P : Measure Γ))
    (hlaw : ∀ n, (P : Measure Γ).map (Y n) = (P₀ : Measure Ω).map (o n))
    (E : ℕ → Set S) (hE : ∀ n, MeasurableSet (E n))
    (hexact : ∀ n ω, o n ω ∈ E n → a n ω = b n (o n ω))
    (G : Set Γ) (hG : MeasurableSet G) {C : ℝ} (hC : 0 ≤ C)
    (haC : ∀ n ω, |a n ω| ≤ C) (hbC : ∀ n y, |b n y| ≤ C) (hzC : ∀ p, |z p| ≤ C)
    (hconv : ∀ᵐ p ∂(P : Measure Γ), p ∈ G →
      Tendsto (fun n => b n (Y n p)) atTop (𝓝 (z p)) ∧
        ∀ᶠ n in atTop, Y n p ∈ E n)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop,
      |(∫ ω, a n ω ∂(P₀ : Measure Ω)) - ∫ p, z p ∂(P : Measure Γ)| <
        4 * C * (P : Measure Γ).real Gᶜ + ε :=
  eventually_abs_integral_sub_le_of_reconstruction_ae P₀ P a b o Y z ha hb ho hY hz hlaw E hE
    (fun n => Filter.Eventually.of_forall (hexact n)) G hG hC haC hbC hzC hconv hε

end BGW.StableTrees.PathTail
