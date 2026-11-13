/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Algebra.Order.Archimedean.Basic

/-!
# Regularity of real paths and dyadic limits

Continuous real paths are determined by almost-everywhere interior equalities and by rational
samples. Vanishing dyadic quotients extend to a full one-sided filter for monotone numerators.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.Skorokhod

/-- Continuous real functions agreeing a.e. on an open interval agree on its closure. -/
theorem eqOn_Icc_of_ae_eq_Ioo {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g)
    (h : f =ᵐ[volume.restrict (Ioo a b)] g) : Set.EqOn f g (Icc a b) := by
  have he := MeasureTheory.Measure.eqOn_open_of_ae_eq h isOpen_Ioo
    hf.continuousOn hg.continuousOn
  have hc : closure (Ioo a b) ⊆ {x | f x = g x} :=
    (isClosed_eq hf hg).closure_subset_iff.mpr he
  rw [closure_Ioo hab.ne] at hc
  exact hc

/-- Equality of two continuous functions is determined by nonnegative rational ages. -/
theorem continuous_eq_iff_rat_toNNReal {f g : ℝ≥0 → ℝ} (hf : Continuous f)
    (hg : Continuous g) : (∀ t, f t = g t) ↔
      ∀ q : ℚ, f (q : ℝ).toNNReal = g (q : ℝ).toNNReal := by
  have hd : Dense {t : ℝ≥0 | ∃ q : ℚ, (q : ℝ) = t} := by
    apply dense_iff_exists_between.mpr
    intro a b hab
    obtain ⟨q, haq, hqb⟩ := exists_rat_btwn (show (a : ℝ) < b from hab)
    have hq : 0 ≤ (q : ℝ) := a.2.trans haq.le
    exact ⟨⟨q, hq⟩, ⟨q, rfl⟩, haq, hqb⟩
  refine ⟨fun h q => h _, fun h t => ?_⟩
  apply congrFun (Continuous.ext_on hd hf hg ?_) t
  intro u hu
  obtain ⟨q, hq⟩ := hu
  simpa only [hq, Real.toNNReal_coe] using h q

/-- Vanishing dyadic quotients of a monotone numerator imply full-filter vanishing. -/
theorem tendsto_div_zero_of_dyadic {U : ℝ → ℝ} (hU : MonotoneOn U (Ioi 0))
    (hU0 : ∀ ε : ℝ, 0 < ε → 0 ≤ U ε) {b : ℝ} (hb : 0 < b)
    (hseq : Tendsto (fun n : ℕ => U (b * (1 / 2 : ℝ) ^ n) / (b * (1 / 2 : ℝ) ^ n))
      atTop (𝓝 0)) :
    Tendsto (fun ε : ℝ => U ε / ε) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with ε hε
    exact ha.trans_le (div_nonneg (hU0 ε hε) hε.le)
  · intro η hη
    obtain ⟨N, hN⟩ := eventually_atTop.mp (hseq.eventually (gt_mem_nhds (half_pos hη)))
    have hbN : 0 < b * (1 / 2 : ℝ) ^ N := mul_pos hb (by positivity)
    filter_upwards [Ioo_mem_nhdsGT hbN] with ε hε
    obtain ⟨n, hnlo, hnhi⟩ := exists_nat_pow_near_of_lt_one
      (div_pos hε.1 hbN) ((div_le_one hbN).mpr hε.2.le)
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    let z : ℝ := b * (1 / 2 : ℝ) ^ (N + n)
    have hz : 0 < z := mul_pos hb (by positivity)
    have hεz : ε ≤ z := by
      dsimp [z]
      rw [pow_add, ← mul_assoc]
      simpa only [mul_comm] using (div_le_iff₀ hbN).mp hnhi
    have hzε : z < 2 * ε := by
      have hh := (lt_div_iff₀ hbN).mp hnlo
      dsimp [z]
      rw [pow_add, ← mul_assoc]
      rw [pow_succ] at hh
      nlinarith only [hh]
    have hUz : U z < η / 2 * z :=
      (div_lt_iff₀ hz).mp (hN (N + n) (Nat.le_add_right N n))
    have hUε : U ε ≤ U z := hU hε.1 hz hεz
    apply (div_lt_iff₀ hε.1).mpr
    nlinarith only [hUz, hUε, hzε, hη]

end BGW.Skorokhod
