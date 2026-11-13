/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.BrownianD
public import BGW.StableTrees.StableProcess
public import BGW.StableTrees.Scalar.FiniteVariance

import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Independence
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Tactic.Ring

/-!
# Index-two stable processes and Donsker's theorem

At stability index two, the stable process law is the law of `√2` times Brownian motion.
The finite-dimensional increment characterization identifies the two laws. The stable-domain
functional limit theorem then gives Donsker's theorem for critical offspring laws with finite
variance and the normalization used throughout the project (P. Billingsley, *Convergence of
Probability Measures*, 2nd ed., Wiley, 1999, Theorem 8.2; J. Bertoin, *Lévy Processes*, Cambridge
University Press, 1996, Chapter VIII).
-/

@[expose] public section

open MeasureTheory Filter ProbabilityTheory
open scoped Topology NNReal ENNReal

namespace BGW.StableTrees

open BGW.Skorokhod BGW.ContinuumTrees.BrownianD

private theorem stableLawAt_two {t : ℝ} (ht : 0 < t) :
    (stableLawAt 2 t : Measure ℝ) = gaussianReal 0 (2 * Real.toNNReal t) := by
  change Measure.map (fun x : ℝ => t ^ (1 / (2 : ℝ)) * x) (stableLaw 2 : Measure ℝ) = _
  rw [stableLaw_two]
  change Measure.map (t ^ (1 / (2 : ℝ)) * ·) (gaussianReal 0 2) = _
  rw [gaussianReal_map_const_mul]
  simp only [mul_zero]
  congr 1
  have hpow : t ^ (1 / (2 : ℝ)) = Real.sqrt t := by
    rw [Real.sqrt_eq_rpow]
  rw [hpow]
  ext
  simp only [NNReal.coe_mul, NNReal.coe_mk]
  norm_num
  rw [Real.sq_sqrt ht.le, max_eq_left ht.le]
  ring

private theorem map_increments_wienerD_sqrt_two {T : ℝ}
    (k : ℕ) (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) (ht : StrictMono t) :
    Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ) - f (t i.castSucc))
      (wienerD (NNReal.sqrt 2) T : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin k =>
        (stableLawAt 2 ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ)) := by
  let P : Measure (D T ℝ) := wienerD (NNReal.sqrt 2) T
  let X : Fin k → Unit → D T ℝ → ℝ := fun i _ f => f (t i.succ) - f (t i.castSucc)
  have hG : IsGaussianProcess (fun (s : Set.Icc (0 : ℝ) T) (f : D T ℝ) => f s) P :=
    isGaussianProcess_eval_wienerD (NNReal.sqrt 2) T
  have hmeas (i : Fin k) : AEMeasurable (X i ()) P :=
    ((measurable_eval (t i.succ)).sub (measurable_eval (t i.castSucc))).aemeasurable
  have hX : IsGaussianProcess (fun (p : (i : Fin k) × Unit) => X p.1 p.2) P := by
    apply hG.of_isGaussianProcess
    rintro ⟨i, ⟨⟩⟩
    refine ⟨{t i.succ, t i.castSucc},
      { toFun := fun x => x ⟨t i.succ, by simp⟩ - x ⟨t i.castSucc, by simp⟩
        map_add' := ?_
        map_smul' := ?_ }, ?_⟩
    · intro x y
      simp only [Pi.add_apply]
      ring
    · intro c x
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      ring
    · intro f
      rfl
  have hmem (s : Set.Icc (0 : ℝ) T) := (hG.hasGaussianLaw_eval s).memLp_two
  have hcov (i j : Fin k) (hij : i < j) :
      cov[X i (), X j (); P] = 0 := by
    have hcs : i.castSucc ≤ j.castSucc := hij.le
    have hss : i.succ ≤ j.succ := Fin.succ_le_succ_iff.mpr hij.le
    have hsc : i.succ ≤ j.castSucc := by
      apply Fin.le_def.mpr
      simp only [Fin.val_succ, Fin.val_castSucc]
      omega
    rw [covariance_fun_sub_fun_sub (hmem _) (hmem _) (hmem _) (hmem _),
      covariance_eval_wienerD, covariance_eval_wienerD, covariance_eval_wienerD,
      covariance_eval_wienerD]
    have hss' : (t i.succ : ℝ) ≤ t j.succ := ht.monotone hss
    have hsc' : (t i.succ : ℝ) ≤ t j.castSucc := ht.monotone hsc
    have hcsj : (t i.castSucc : ℝ) ≤ t j.succ :=
      (ht.monotone hcs).trans (ht (show j.castSucc < j.succ from Fin.castSucc_lt_succ)).le
    have hcs' : (t i.castSucc : ℝ) ≤ t j.castSucc := ht.monotone hcs
    rw [min_eq_left hss', min_eq_left hsc', min_eq_left hcsj, min_eq_left hcs']
    ring
  have hindP : iIndepFun (fun i f (_ : Unit) => X i () f) P := by
    apply hX.iIndepFun_of_covariance_eq_zero (fun i _ => hmeas i)
    intro i j hij _ _
    rcases lt_or_gt_of_ne hij with h | h
    · exact hcov i j h
    · rw [covariance_comm]
      exact hcov j i h
  have hind : iIndepFun (fun i f => X i () f) P := by
    have hcomp := hindP.comp (fun _ (g : Unit → ℝ) => g ()) (fun _ => measurable_pi_apply ())
    simpa only [Function.comp_def] using hcomp
  change Measure.map (fun f : D T ℝ => fun i : Fin k => X i () f) P = _
  rw [hind.map_fun_eq_pi_map (fun i => hmeas i)]
  congr 1
  funext i
  have hΔ : 0 < (t i.succ : ℝ) - t i.castSucc := sub_pos.mpr (ht Fin.castSucc_lt_succ)
  rw [stableLawAt_two hΔ]
  have hlaw := hG.hasGaussianLaw_fun_sub (s := t i.succ) (t := t i.castSucc)
  have hmap := hlaw.map_eq_gaussianReal
  have hint : ∫ f : D T ℝ, f (t i.succ) - f (t i.castSucc) ∂P = 0 := by
    rw [integral_sub (hG.hasGaussianLaw_eval _).integrable (hG.hasGaussianLaw_eval _).integrable,
      integral_eval_wienerD, integral_eval_wienerD, sub_self]
  have hvar : Var[fun f : D T ℝ => f (t i.succ) - f (t i.castSucc); P] =
      2 * ((t i.succ : ℝ) - t i.castSucc) := by
    rw [variance_fun_sub (hmem _) (hmem _), ← covariance_self (measurable_eval _).aemeasurable,
      ← covariance_self (measurable_eval _).aemeasurable, covariance_eval_wienerD,
      covariance_eval_wienerD, covariance_eval_wienerD, min_self]
    norm_num
    have hle : (t i.castSucc : ℝ) ≤ t i.succ := (ht Fin.castSucc_lt_succ).le
    rw [min_eq_right hle]
    ring
  rw [hint, hvar, Real.toNNReal_mul (by positivity)] at hmap
  norm_num at hmap ⊢
  exact hmap

private theorem isStableLevyLaw_wienerD_sqrt_two {T : ℝ} :
    IsStableLevyLaw 2 T (wienerD (NNReal.sqrt 2) T) where
  start hT := ae_eval_zero_wienerD (NNReal.sqrt 2) hT
  increments k t ht _ := map_increments_wienerD_sqrt_two k t ht

/-- At `θ = 2` the stable process law is the law of `√2 · B`. -/
theorem stableProcessLaw_two {T : ℝ} (hT : 0 < T) :
    stableProcessLaw 2 T = wienerD (NNReal.sqrt 2) T := by
  exact ((eq_stableProcessLaw_iff (by norm_num) hT).2
    isStableLevyLaw_wienerD_sqrt_two).symm

/-- Measure form of `stableProcessLaw_two`. -/
theorem coe_stableProcessLaw_two {T : ℝ} (hT : 0 < T) :
    (stableProcessLaw 2 T : Measure (D T ℝ)) =
      (wienerD (NNReal.sqrt 2) T : Measure (D T ℝ)) := by
  rw [stableProcessLaw_two hT]

/-- The index-two stable law is carried by continuous paths. -/
theorem ae_mem_range_ofContinuous_stableProcessLaw_two {T : ℝ} (hT : 0 < T) :
    ∀ᵐ f ∂(stableProcessLaw 2 T : Measure (D T ℝ)),
      f ∈ Set.range (ofContinuous : C(Set.Icc (0 : ℝ) T, ℝ) → D T ℝ) := by
  rw [coe_stableProcessLaw_two hT]
  exact ae_mem_range_ofContinuous_wienerD (NNReal.sqrt 2) T

/-- Donsker form: a critical nondegenerate offspring law in the index-2 stable domain with
normalizer `a` has FCLT limit `wienerD (√2) T`. -/
theorem StableDomain.tendsto_stepPathLaw_wienerD {μ : PMF ℕ} {a : ℕ → ℝ}
    (h : StableDomain μ 2 a) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => stepPathLaw (realOffspringStepLaw μ) T a n) atTop
      (𝓝 (wienerD (NNReal.sqrt 2) T)) := by
  rw [← stableProcessLaw_two hT]
  exact h.tendsto_stepPathLaw hT

/-- Donsker's theorem for critical finite-variance offspring laws: with `σ² = E[(ξ - 1)²]`, the
step paths normalized by `σ √n / √2` converge to `wienerD (√2) T`. -/
theorem tendsto_stepPathLaw_wienerD_of_finiteVariance {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hfinite : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => stepPathLaw (realOffspringStepLaw μ) T
        (fun n : ℕ => (Real.sqrt (∫ z : ℤ, (z : ℝ) ^ 2 ∂stepLaw μ) / Real.sqrt 2) *
          Real.sqrt n) n) atTop
      (𝓝 (wienerD (NNReal.sqrt 2) T)) := by
  exact (Scalar.stableDomain_of_finiteVariance hc hne hfinite).tendsto_stepPathLaw_wienerD hT

end BGW.StableTrees
