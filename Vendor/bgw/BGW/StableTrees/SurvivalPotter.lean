/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SurvivalRegularity
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Bounds for the offspring defect near zero

Sequential regular variation gives a right-hand filter limit. A fixed doubling estimate
then gives a lower Potter bound, by iteration on dyadic scales.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace BGW.StableTrees.Survival

/-- Regular variation of the offspring defect as a right-hand filter limit at zero. -/
theorem tendsto_offspringDefect_ratio_nhdsGT {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u => offspringDefect μ (c * u) / offspringDefect μ u)
      (𝓝[>] 0) (𝓝 (c ^ θ)) := by
  apply tendsto_iff_seq_tendsto.mpr
  intro u hu
  exact tendsto_offspringDefect_ratio h hc (hu.eventually self_mem_nhdsWithin) hu

/-- A uniform doubling lower bound with any exponent strictly below the stable index. -/
theorem exists_offspringDefect_doubling {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {p : ℝ} (hp : p < θ) :
    ∃ v₀ : ℝ, 0 < v₀ ∧ v₀ ≤ 1 / 2 ∧ ∀ v : ℝ, 0 < v → v ≤ v₀ →
      (2 : ℝ) ^ p * offspringDefect μ v ≤ offspringDefect μ (2 * v) := by
  have hpow : (2 : ℝ) ^ p < (2 : ℝ) ^ θ :=
    Real.rpow_lt_rpow_of_exponent_lt (by norm_num) hp
  have he := (tendsto_offspringDefect_ratio_nhdsGT h (by norm_num : (0 : ℝ) < 2)).eventually
    (lt_mem_nhds hpow)
  rcases mem_nhdsGT_iff_exists_Ioc_subset.mp he with ⟨v₁, hv₁, hv⟩
  refine ⟨min v₁ (1 / 2), lt_min hv₁ (by norm_num), min_le_right _ _, ?_⟩
  intro v hv0 hv1
  have hvv : v ≤ v₁ := hv1.trans (min_le_left _ _)
  have hvle : v ≤ 1 := (hv1.trans (min_le_right _ _)).trans (by norm_num)
  have hD := offspringDefect_pos h.critical h.nondegenerate hv0 hvle
  exact ((lt_div_iff₀ hD).mp (hv ⟨hv0, hvv⟩)).le

/-- Iteration of a doubling lower bound, up to a fixed small scale. -/
theorem offspringDefect_dyadic_lower {μ : PMF ℕ}
    {p v₀ : ℝ}
    (hd : ∀ v : ℝ, 0 < v → v ≤ v₀ →
      (2 : ℝ) ^ p * offspringDefect μ v ≤ offspringDefect μ (2 * v))
    {u : ℝ} (hu : 0 < u) (j : ℕ) (hj : (2 : ℝ) ^ j * u ≤ v₀) :
    ((2 : ℝ) ^ p) ^ j * offspringDefect μ u ≤
      offspringDefect μ ((2 : ℝ) ^ j * u) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hj' : (2 : ℝ) ^ j * u ≤ v₀ := by
      have hp : 0 ≤ (2 : ℝ) ^ j * u := by positivity
      rw [pow_succ] at hj
      nlinarith
    have hi := ih hj'
    have he := hd ((2 : ℝ) ^ j * u) (by positivity) hj'
    calc
      ((2 : ℝ) ^ p) ^ (j + 1) * offspringDefect μ u =
          (2 : ℝ) ^ p * (((2 : ℝ) ^ p) ^ j * offspringDefect μ u) := by ring
      _ ≤ (2 : ℝ) ^ p * offspringDefect μ ((2 : ℝ) ^ j * u) := by
        exact mul_le_mul_of_nonneg_left hi (Real.rpow_nonneg (by norm_num) _)
      _ ≤ offspringDefect μ (2 * ((2 : ℝ) ^ j * u)) := he
      _ = offspringDefect μ ((2 : ℝ) ^ (j + 1) * u) := by congr 1; ring

/-- A lower Potter bound for all multipliers at least one, below a fixed small scale. -/
theorem exists_offspringDefect_potter_lower {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {p : ℝ} (hp0 : 0 ≤ p) (hp : p < θ) :
    ∃ v₀ : ℝ, 0 < v₀ ∧ v₀ ≤ 1 ∧ ∀ u lam : ℝ, 0 < u → 1 ≤ lam → lam * u ≤ v₀ →
      (lam / 2) ^ p * offspringDefect μ u ≤ offspringDefect μ (lam * u) := by
  obtain ⟨v₀, hv₀, hv₀le, hd⟩ := exists_offspringDefect_doubling h hp
  have hv₀1 : v₀ ≤ 1 := hv₀le.trans (by norm_num)
  refine ⟨v₀, hv₀, hv₀1, ?_⟩
  intro u lam hu hlam hscale
  obtain ⟨j, hjlo, hjhi⟩ := exists_nat_pow_near hlam (by norm_num : (1 : ℝ) < 2)
  have hj : (2 : ℝ) ^ j * u ≤ v₀ :=
    (mul_le_mul_of_nonneg_right hjlo hu.le).trans hscale
  have hdyad := offspringDefect_dyadic_lower hd hu j hj
  have hpow : (lam / 2) ^ p ≤ ((2 : ℝ) ^ p) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
      mul_comm p (j : ℝ), Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_natCast]
    apply Real.rpow_le_rpow (by positivity) _ hp0
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 2)]
    simpa [pow_succ, mul_comm] using hjhi.le
  calc
    (lam / 2) ^ p * offspringDefect μ u ≤
        ((2 : ℝ) ^ p) ^ j * offspringDefect μ u :=
      mul_le_mul_of_nonneg_right hpow
        (offspringDefect_nonneg h.critical hu.le
          ((show u ≤ lam * u by nlinarith).trans (hscale.trans hv₀1)))
    _ ≤ offspringDefect μ ((2 : ℝ) ^ j * u) := hdyad
    _ ≤ offspringDefect μ (lam * u) :=
      offspringDefect_monotoneOn h.critical ⟨by positivity, hj.trans hv₀1⟩
        ⟨by positivity, hscale.trans hv₀1⟩ (mul_le_mul_of_nonneg_right hjlo hu.le)

end BGW.StableTrees.Survival
