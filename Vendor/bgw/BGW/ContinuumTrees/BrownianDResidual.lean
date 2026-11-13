/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
public import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Residual and Gaussian-tilt lemmas for Brownian bridge prefixes

Measure-theoretic and Gaussian-process lemmas used to compare the bridge prefix law with Brownian
motion: independence of an endpoint-adjusted residual from the endpoint, densities of a pair with an
endpoint weight, and the Gaussian tilt identity for the prefix density (Gaussian conditioning as in
D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, 3rd ed., Springer, 1999, Chapter
I).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace BGW.ContinuumTrees.BrownianD

/-- Reweighting by a function of the second coordinate commutes with pushforward along `F`. -/
theorem map_withDensity_comp_snd
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure Ω) (F : Ω → α × β) (hF : Measurable F)
    (g : β → ℝ≥0∞) (hg : Measurable g) :
    (μ.withDensity (fun ω => g (F ω).2)).map F =
      (μ.map F).withDensity (fun z => g z.2) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply hF hs, withDensity_apply _ (hs.preimage hF),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage hF), ← lintegral_indicator hs]
  exact (lintegral_map ((hg.comp measurable_snd).indicator hs) hF).symm

/-- Reweighting by a function of an independent coordinate keeps the pair law a product. -/
theorem map_withDensity_pair_indep
    {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    {μ : Measure Ω} [IsFiniteMeasure μ] (X : Ω → α) (Y : Ω → β)
    (hX : Measurable X) (hY : Measurable Y) (hXY : IndepFun X Y μ)
    (w : β → ℝ≥0∞) (hw : Measurable w) :
    (μ.withDensity (fun ω => w (Y ω))).map (fun ω => (X ω, Y ω)) =
      (μ.map X).prod ((μ.map Y).withDensity w) := by
  have hpair : Measurable (fun ω => (X ω, Y ω)) := hX.prodMk hY
  rw [map_withDensity_comp_snd μ (fun ω => (X ω, Y ω)) hpair w hw,
    hXY.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable,
    prod_withDensity_right hw]

/-- In a Gaussian process, the residual `X (u j) - l j * X e` is independent of `X e`
whenever `X e` has covariance `l j * Var (X e)` with each `X (u j)`. -/
theorem indepFun_residual_endpoint {Ω ι J : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ι → Ω → ℝ} (hX : IsGaussianProcess X μ) (hmeas : ∀ i, Measurable (X i))
    (u : J → ι) (e : ι) (l : J → ℝ)
    (hcov : ∀ j, cov[X (u j), X e; μ] = l j * cov[X e, X e; μ]) :
    IndepFun (fun ω j => X (u j) ω - l j * X e ω) (X e) μ := by
  classical
  let R : J → Ω → ℝ := fun j ω => X (u j) ω - l j * X e ω
  let Y : Unit → Ω → ℝ := fun _ => X e
  have hjoint : IsGaussianProcess (Sum.elim R Y) μ := by
    apply hX.of_isGaussianProcess
    intro q
    cases q with
    | inl j =>
      refine ⟨{u j, e},
        { toFun := fun z => z ⟨u j, by simp⟩ - l j * z ⟨e, by simp⟩
          map_add' := ?_
          map_smul' := ?_ }, ?_⟩
      · intro z₁ z₂
        simp only [Pi.add_apply]
        ring
      · intro r z
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring
      · intro f
        rfl
    | inr v =>
      refine ⟨{e},
        { toFun := fun z => z ⟨e, by simp⟩
          map_add' := by intro z₁ z₂; rfl
          map_smul' := by intro r z; rfl }, ?_⟩
      simp [Y]
  have hmem (i : ι) := (hX.hasGaussianLaw_eval i).memLp_two
  have hcovR (j : J) (v : Unit) : cov[R j, Y v; μ] = 0 := by
    have h := covariance_fun_sub_left (hmem (u j)) ((hmem e).const_mul (l j)) (hmem e)
    simp only [R, Y]
    rw [h, covariance_const_mul_left, hcov j]
    ring
  have hind := hjoint.indepFun_of_covariance_eq_zero
    (fun j => ((hmeas (u j)).sub ((hmeas e).const_mul (l j))).aemeasurable)
    (fun _ => (hmeas e).aemeasurable) hcovR
  have hright : Measurable (fun z : Unit → ℝ => z ()) := measurable_pi_apply ()
  simpa [Function.comp_def, R, Y] using hind.comp measurable_id hright

/-- The Gaussian tilt identity: the centered Gaussian density of variance `c² a`, multiplied by
the explicit prefix density, is the centered Gaussian density of variance `c² a (1 - a)`. -/
theorem gaussianPDFReal_mul_explicit {c : ℝ≥0} (hc : c ≠ 0) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (x : ℝ) :
    gaussianPDFReal 0 (c ^ 2 * Real.toNNReal a) x *
        ((1 - a) ^ (-(1 / 2 : ℝ)) * Real.exp (-x ^ 2 / (2 * (c : ℝ) ^ 2 * (1 - a)))) =
      gaussianPDFReal 0 (c ^ 2 * Real.toNNReal (a * (1 - a))) x := by
  let q : ℝ := 1 - a
  have hq : 0 < q := by dsimp [q]; linarith
  have haq : 0 < a * q := mul_pos ha hq
  have hcposR : 0 < (c : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hc)
  have hva : (c : ℝ) ^ 2 * max a 0 = (c : ℝ) ^ 2 * a := by
    rw [max_eq_left ha.le]
  have hvp : (c : ℝ) ^ 2 * max (a * (1 - a)) 0 = (c : ℝ) ^ 2 * a * (1 - a) := by
    rw [max_eq_left (by simpa [q] using haq.le)]
    ring
  have hroot : √(2 * Real.pi * ((c : ℝ) ^ 2 * a)) * √(1 - a) =
      √(2 * Real.pi * ((c : ℝ) ^ 2 * a * (1 - a))) := by
    calc
      √(2 * Real.pi * ((c : ℝ) ^ 2 * a)) * √(1 - a) =
          √((2 * Real.pi * ((c : ℝ) ^ 2 * a)) * (1 - a)) := by
        rw [← Real.sqrt_mul (by positivity)]
      _ = √(2 * Real.pi * ((c : ℝ) ^ 2 * a * (1 - a))) := by
        congr 1
        ring
  have hrootA : √(a * (Real.pi * (2 * (c : ℝ) ^ 2))) =
      √(2 * Real.pi * ((c : ℝ) ^ 2 * a)) := by
    congr 1
    ring
  have hpow : (1 - a) ^ (-(1 / 2 : ℝ)) = (√(1 - a))⁻¹ := by
    rw [Real.rpow_neg hq.le, ← Real.sqrt_eq_rpow]
  have hexp : -x ^ 2 / (2 * (c : ℝ) ^ 2 * a) +
      -x ^ 2 / (2 * (c : ℝ) ^ 2 * (1 - a)) =
      -x ^ 2 / (2 * (c : ℝ) ^ 2 * a * (1 - a)) := by
    field_simp [ne_of_gt hcposR, ne_of_gt ha, ne_of_gt hq]
    ring
  rw [gaussianPDFReal_def 0 (c ^ 2 * Real.toNNReal a),
    gaussianPDFReal_def 0 (c ^ 2 * Real.toNNReal (a * (1 - a)))]
  dsimp
  rw [hva, hvp, sub_zero, hpow]
  calc
    _ = ((√(2 * Real.pi * ((c : ℝ) ^ 2 * a)))⁻¹ * (√(1 - a))⁻¹) *
        (Real.exp (-x ^ 2 / (2 * (c : ℝ) ^ 2 * a)) *
          Real.exp (-x ^ 2 / (2 * (c : ℝ) ^ 2 * (1 - a)))) := by
      ac_rfl
    _ = (√(2 * Real.pi * ((c : ℝ) ^ 2 * a * (1 - a))))⁻¹ *
        Real.exp (-x ^ 2 / (2 * ((c : ℝ) ^ 2 * a * (1 - a)))) := by
      rw [← Real.exp_add, hexp]
      have hcoef : (√(2 * Real.pi * ((c : ℝ) ^ 2 * a)))⁻¹ *
          (√(1 - a))⁻¹ =
          (√(2 * Real.pi * ((c : ℝ) ^ 2 * a * (1 - a))))⁻¹ := by
        calc
          _ = (√(2 * Real.pi * ((c : ℝ) ^ 2 * a)) * √(1 - a))⁻¹ := by
            calc
              _ = (√(1 - a) * √(2 * Real.pi * ((c : ℝ) ^ 2 * a)))⁻¹ := by
                rw [← mul_inv_rev]
              _ = (√(2 * Real.pi * ((c : ℝ) ^ 2 * a)) * √(1 - a))⁻¹ := by
                rw [mul_comm]
          _ = _ := congrArg (fun y : ℝ => y⁻¹) hroot
      have harg : -x ^ 2 / (2 * (c : ℝ) ^ 2 * a * (1 - a)) =
          -x ^ 2 / (2 * ((c : ℝ) ^ 2 * a * (1 - a))) := by
        congr 1
        ring
      rw [hcoef, harg]

end BGW.ContinuumTrees.BrownianD
