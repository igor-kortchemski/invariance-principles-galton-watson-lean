/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.CompleteMetric
import BGW.Skorokhod.CompleteMetricInterpolation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Topology.MetricSpace.Pseudo.Pi

/-!
# Matching small-oscillation partitions

Matching partition nodes controls the complete Skorokhod distance without constructing
auxiliary step paths.
-/

@[expose] public section

open Set
open scoped ENNReal BigOperators

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

/-- Every time strictly before the last node lies in a half-open partition block. -/
theorem exists_halfOpen_partition_block {n : ℕ} (t : Fin (n + 1) → ℝ) {u : ℝ}
    (h₀ : t 0 ≤ u) (hT : u < t (Fin.last n)) :
    ∃ i : Fin n, t i.castSucc ≤ u ∧ u < t i.succ := by
  induction n with
  | zero => exact (not_lt_of_ge h₀ hT).elim
  | succ n ih =>
    by_cases h : u < t (0 : Fin (n + 1)).succ
    · exact ⟨0, h₀, h⟩
    · obtain ⟨i, hi, hi'⟩ := ih (fun j => t j.succ) (le_of_not_gt h) hT
      exact ⟨i.succ, by simpa only [Fin.succ_castSucc] using hi, hi'⟩

/-- A lower bound on adjacent partition gaps also bounds every nonzero node gap. -/
theorem partition_gap_lt {n : ℕ} (p : Fin (n + 1) → ℝ) (hp : StrictMono p)
    {δ : ℝ} (hgap : ∀ i : Fin n, δ < p i.succ - p i.castSucc)
    {i j : Fin (n + 1)} (hij : i < j) : δ < p j - p i := by
  have hi : i.val < n := by have hj := j.isLt; change i.val < j.val at hij; omega
  let k : Fin n := ⟨i.val, hi⟩
  have hki : k.castSucc = i := Fin.ext rfl
  have hkj : k.succ ≤ j := by change i.val + 1 ≤ j.val; exact hij
  exact (hgap k).trans_le (by rw [hki]; exact sub_le_sub_right (hp.monotone hkj) _)

/-- Positive minimum spacing bounds the number of blocks. -/
theorem partition_length_le {n : ℕ} (p : Fin (n + 1) → ℝ)
    (hp0 : p 0 = 0) (hpT : p (Fin.last n) = T) {δ : ℝ} (hδ : 0 < δ)
    (hgap : ∀ i : Fin n, δ < p i.succ - p i.castSucc) : n ≤ ⌈T / δ⌉₊ := by
  have hsum : ∑ i : Fin n, (p i.succ - p i.castSucc) = T := by
    rw [Finset.sum_sub_distrib]
    have h₁ := Fin.sum_univ_succ p
    have h₂ := Fin.sum_univ_castSucc p
    rw [hp0] at h₁
    rw [hpT] at h₂
    linarith
  have hle : (n : ℝ) * δ ≤ T := by
    have := Finset.sum_le_sum (fun (i : Fin n) (_ : i ∈ Finset.univ) => (hgap i).le)
    simpa [hsum] using this
  have hcast : (n : ℝ) ≤ (⌈T / δ⌉₊ : ℝ) :=
    ((le_div_iff₀ hδ).mpr hle).trans (Nat.le_ceil _)
  exact_mod_cast hcast

/-- Matching all partition nodes, together with bounds on node values and block oscillations,
controls Billingsley's complete distance. -/
theorem j1CompleteDist_le_of_partition_match [MetricSpace E] (f g : D T E)
    {n : ℕ} (x y : Fin (n + 1) → Icc (0 : ℝ) T)
    (hx0 : (x 0 : ℝ) = 0) (hxT : (x (Fin.last n) : ℝ) = T)
    (hx : StrictMono x) (hy : StrictMono y) {a b r : ℝ}
    (ha : 0 ≤ a) (hr : 0 ≤ r)
    (hf : ∀ (i : Fin n) (s t : Icc (0 : ℝ) T),
      x i.castSucc ≤ s → s < x i.succ → x i.castSucc ≤ t → t < x i.succ →
        dist (f s) (f t) ≤ a)
    (hg : ∀ (i : Fin n) (s t : Icc (0 : ℝ) T),
      y i.castSucc ≤ s → s < y i.succ → y i.castSucc ≤ t → t < y i.succ →
        dist (g s) (g t) ≤ a)
    (hnode : ∀ i, dist (f (x i)) (g (y i)) ≤ b)
    (σ : TimeChange T) (hσ : ∀ i, σ (x i) = y i)
    (hlog : σ.logSlope ≤ ENNReal.ofReal r) :
    j1CompleteDist f g ≤ max r (2 * a + b) := by
  apply j1CompleteDist_le_of_completeCost_le f g σ (le_max_of_le_left hr)
  apply max_le
  · exact hlog.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  · refine iSup_le fun t => ?_
    rw [edist_dist]
    apply ENNReal.ofReal_le_ofReal
    apply le_trans _ (le_max_right _ _)
    by_cases ht : (t : ℝ) = T
    · have heq : t = x (Fin.last n) := Subtype.ext (ht.trans hxT.symm)
      rw [heq, hσ]
      exact (hnode _).trans (by linarith)
    · obtain ⟨i, hi, hi'⟩ := exists_halfOpen_partition_block (fun i => (x i : ℝ))
        (by simpa only [hx0] using t.2.1)
        (by simpa only [hxT] using lt_of_le_of_ne t.2.2 ht)
      have hσi : y i.castSucc ≤ σ t := by simpa only [hσ] using σ.monotone hi
      have hσi' : σ t < y i.succ := by simpa only [hσ] using σ.strictMono hi'
      have hft := hf i t (x i.castSucc) hi hi' le_rfl (hx i.castSucc_lt_succ)
      have hgt := hg i (y i.castSucc) (σ t) le_rfl (hy i.castSucc_lt_succ) hσi hσi'
      calc
        dist (f t) (g (σ t)) ≤ dist (f t) (f (x i.castSucc)) +
            dist (f (x i.castSucc)) (g (y i.castSucc)) +
            dist (g (y i.castSucc)) (g (σ t)) := dist_triangle4 _ _ _ _
        _ ≤ 2 * a + b := by linarith [hnode i.castSucc]

/-- Close node times and values of two small-oscillation partitions give a small complete
distance. The time tolerance is chosen relative to the minimum partition spacing. -/
theorem j1CompleteDist_lt_of_close_partition_nodes [MetricSpace E] (f g : D T E)
    {n : ℕ} (x y : Fin (n + 1) → Icc (0 : ℝ) T)
    (hx0 : (x 0 : ℝ) = 0) (hxT : (x (Fin.last n) : ℝ) = T)
    (hy0 : (y 0 : ℝ) = 0) (hyT : (y (Fin.last n) : ℝ) = T)
    (hx : StrictMono x) (hy : StrictMono y) {ε δ κ : ℝ} (hε : 0 < ε)
    (hκ : κ ≤ ε / 16)
    (hκlow : 8 * κ ≤ (1 - Real.exp (-(ε / 2))) * δ)
    (hκupp : 8 * κ ≤ (Real.exp (ε / 2) - 1) * δ)
    (hgap : ∀ i : Fin n, δ < (x i.succ : ℝ) - x i.castSucc)
    (hf : ∀ (i : Fin n) (s t : Icc (0 : ℝ) T),
      x i.castSucc ≤ s → s < x i.succ → x i.castSucc ≤ t → t < x i.succ →
        dist (f s) (f t) ≤ ε / 8)
    (hg : ∀ (i : Fin n) (s t : Icc (0 : ℝ) T),
      y i.castSucc ≤ s → s < y i.succ → y i.castSucc ≤ t → t < y i.succ →
        dist (g s) (g t) ≤ ε / 8)
    (hnode : ∀ i, dist ((x i : ℝ), f (x i)) ((y i : ℝ), g (y i)) < 2 * κ) :
    j1CompleteDist f g < ε := by
  have htime (i) : |(y i : ℝ) - x i| < 2 * κ := by
    have hi := (max_lt_iff.mp (hnode i)).1
    simpa only [Real.dist_eq, abs_sub_comm] using hi
  have hval (i) : dist (f (x i)) (g (y i)) ≤ 2 * κ :=
    (max_lt_iff.mp (hnode i)).2.le
  have hlow : 0 ≤ 1 - Real.exp (-(ε / 2)) := by
    have := Real.exp_le_one_iff.mpr (show -(ε / 2) ≤ 0 by linarith)
    linarith
  have hupp : 0 ≤ Real.exp (ε / 2) - 1 := by
    have := Real.one_le_exp_iff.mpr (show 0 ≤ ε / 2 by linarith)
    linarith
  have hxy : ∀ i j, x i ≤ x j →
      Real.exp (-(ε / 2)) * ((x j : ℝ) - x i) ≤ (y j : ℝ) - y i ∧
        (y j : ℝ) - y i ≤ Real.exp (ε / 2) * ((x j : ℝ) - x i) := by
    intro i j hij
    by_cases heq : i = j
    · subst j; simp
    have hij' : i < j := lt_of_le_of_ne (hx.le_iff_le.mp hij) heq
    have hgij := partition_gap_lt (fun i => (x i : ℝ)) hx hgap hij'
    have hli := (abs_lt.mp (htime i)).1
    have hui := (abs_lt.mp (htime i)).2
    have hlj := (abs_lt.mp (htime j)).1
    have huj := (abs_lt.mp (htime j)).2
    have hlow' := mul_le_mul_of_nonneg_left hgij.le hlow
    have hupp' := mul_le_mul_of_nonneg_left hgij.le hupp
    constructor <;> nlinarith
  obtain ⟨σ, hσ, hb⟩ := exists_timeChange_of_finite_secant_bounds x y 0 (Fin.last n)
    hx0 hxT hy0 hyT (Real.exp_pos (-(ε / 2)))
    (Real.exp_le_exp.mpr (by linarith)) hxy
  have hlog := σ.logSlope_le_of_secant_bounds (fun s t hst => hb s t hst.le)
  have hdist := j1CompleteDist_le_of_partition_match f g x y hx0 hxT hx hy
    (show 0 ≤ ε / 8 by linarith) (show 0 ≤ ε / 2 by linarith) hf hg hval σ hσ hlog
  exact hdist.trans_lt (max_lt (by linarith) (by linarith))

end BGW.Skorokhod
