/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.CompleteMetricSpace
import BGW.Skorokhod.CompleteMetricInterpolation
import BGW.Skorokhod.TightnessPartitions
import Mathlib.Order.Filter.Finite

/-!
# Compatibility of the logarithmic-slope metric

Finite interpolation of a small-oscillation partition replaces J1 time changes by
ones whose logarithmic slopes tend to zero.
-/

@[expose] public section

open Set Filter
open scoped Topology ENNReal

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*}

private theorem eventually_exists_small_logSlope_match {ι κ : Type*} [Fintype ι] [Nonempty ι]
    {l : Filter κ} (x : ι → Icc (0 : ℝ) T) (i₀ iT : ι)
    (hx₀ : (x i₀ : ℝ) = 0) (hxT : (x iT : ℝ) = T)
    (σ : κ → TimeChange T)
    (hσ : ∀ i, Tendsto (fun n => (σ n (x i) : ℝ)) l (𝓝 (x i : ℝ)))
    {r : ℝ} (hr : 0 < r) :
    ∀ᶠ n in l, ∃ ρ : TimeChange T,
      ρ.logSlope ≤ ENNReal.ofReal r ∧ ∀ i, ρ (x i) = σ n (x i) := by
  have hpair (i j : ι) : ∀ᶠ n in l, x i ≤ x j →
      Real.exp (-r) * ((x j : ℝ) - x i) ≤ (σ n (x j) : ℝ) - σ n (x i) ∧
        (σ n (x j) : ℝ) - σ n (x i) ≤ Real.exp r * ((x j : ℝ) - x i) := by
    by_cases hij : x i < x j
    · have hgap : 0 < (x j : ℝ) - x i := sub_pos.mpr hij
      have hlow : Real.exp (-r) * ((x j : ℝ) - x i) < (x j : ℝ) - x i := by
        have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hr)
        nlinarith
      have hupp : (x j : ℝ) - x i < Real.exp r * ((x j : ℝ) - x i) := by
        have := Real.one_lt_exp_iff.mpr hr
        nlinarith
      filter_upwards [((hσ j).sub (hσ i)).eventually (Ioo_mem_nhds hlow hupp)]
        with n hn _ using ⟨hn.1.le, hn.2.le⟩
    · exact Filter.Eventually.of_forall fun n hle => by
        have heq : x i = x j := le_antisymm hle (le_of_not_gt hij)
        simp [heq]
  have hall : ∀ᶠ n in l, ∀ i j, x i ≤ x j →
      Real.exp (-r) * ((x j : ℝ) - x i) ≤ (σ n (x j) : ℝ) - σ n (x i) ∧
        (σ n (x j) : ℝ) - σ n (x i) ≤ Real.exp r * ((x j : ℝ) - x i) :=
    eventually_all.mpr fun i => eventually_all.mpr fun j => hpair i j
  filter_upwards [hall] with n hn
  have hT : 0 ≤ T := (x i₀).2.1.trans (x i₀).2.2
  have hy₀ : (σ n (x i₀) : ℝ) = 0 := by
    have hx : x i₀ = ⟨0, le_rfl, hT⟩ := Subtype.ext hx₀
    rw [hx, TimeChange.apply_zero (σ n) hT]
  have hyT : (σ n (x iT) : ℝ) = T := by
    have hx : x iT = ⟨T, hT, le_rfl⟩ := Subtype.ext hxT
    rw [hx, TimeChange.apply_top (σ n) hT]
  obtain ⟨ρ, hρ, hb⟩ := exists_timeChange_of_finite_secant_bounds
    x (fun i => σ n (x i)) i₀ iT hx₀ hxT hy₀ hyT (Real.exp_pos (-r))
      (Real.exp_le_exp.mpr (by linarith)) hn
  exact ⟨ρ, ρ.logSlope_le_of_secant_bounds (fun s t hst => hb s t hst.le), hρ⟩

private theorem exists_partition_block {n : ℕ} (t : Fin (n + 1) → ℝ) {u : ℝ}
    (h₀ : t 0 ≤ u) (hT : u < t (Fin.last n)) :
    ∃ i : Fin n, t i.castSucc ≤ u ∧ u < t i.succ := by
  induction n with
  | zero => exact (not_lt_of_ge h₀ hT).elim
  | succ n ih =>
    by_cases h : u < t (0 : Fin (n + 1)).succ
    · exact ⟨0, h₀, h⟩
    · obtain ⟨i, hi, hi'⟩ := ih (fun j => t j.succ) (le_of_not_gt h) hT
      exact ⟨i.succ, by simpa only [Fin.succ_castSucc] using hi, hi'⟩

private theorem aligned_path_bound [MetricSpace E] (u f : D T E)
    {n : ℕ} (x : Fin (n + 1) → Icc (0 : ℝ) T)
    (hx₀ : (x 0 : ℝ) = 0) (hxT : (x (Fin.last n) : ℝ) = T)
    {ε δ : ℝ} (hε : 0 ≤ ε)
    (hosc : ∀ (i : Fin n) (s t : Icc (0 : ℝ) T),
      x i.castSucc ≤ s → s < x i.succ →
      x i.castSucc ≤ t → t < x i.succ → dist (f s) (f t) ≤ ε)
    (σ ρ : TimeChange T) (hmatch : ∀ i, ρ (x i) = σ (x i))
    (hpath : ∀ t, dist (u (σ t)) (f t) ≤ δ) (t : Icc (0 : ℝ) T) :
    dist (f t) (u (ρ t)) ≤ δ + ε := by
  let v := σ.symm (ρ t)
  have hclose : dist (u (ρ t)) (f v) ≤ δ := by
    simpa only [v, OrderIso.apply_symm_apply] using hpath v
  have hfv : dist (f v) (f t) ≤ ε := by
    by_cases ht : (t : ℝ) = T
    · have htv : v = t := by
        have hT : 0 ≤ T := t.2.1.trans t.2.2
        have ht' : t = ⟨T, hT, le_rfl⟩ := Subtype.ext ht
        simp only [v, ht', TimeChange.apply_top ρ hT, TimeChange.apply_top σ.symm hT]
      simpa [htv] using hε
    · have htT : (t : ℝ) < T := lt_of_le_of_ne t.2.2 ht
      obtain ⟨i, hi, hi'⟩ := exists_partition_block (fun i => (x i : ℝ))
        (by simpa only [hx₀] using t.2.1) (by simpa only [hxT] using htT)
      have hv₀ : x i.castSucc ≤ v := by
        have := σ.symm.monotone (ρ.monotone hi)
        simpa only [hmatch, OrderIso.symm_apply_apply] using this
      have hvT : v < x i.succ := by
        have := σ.symm.strictMono (ρ.strictMono hi')
        simpa only [hmatch, OrderIso.symm_apply_apply] using this
      exact hosc i v t hv₀ hvT hi hi'
  calc
    dist (f t) (u (ρ t)) = dist (u (ρ t)) (f t) := dist_comm _ _
    _ ≤ dist (u (ρ t)) (f v) + dist (f v) (f t) := dist_triangle _ _ _
    _ ≤ δ + ε := add_le_add hclose hfv

/-- The identity from J1 paths to logarithmic-slope paths is continuous. -/
theorem continuous_toDComplete_fun [MetricSpace E] :
    @Continuous (D T E) (DComplete T E) _ _ (fun f => f) := by
  apply continuous_iff_seqContinuous.mpr
  intro u f hu
  by_cases hT : 0 ≤ T
  · obtain ⟨σ, hdisp, hpath⟩ := tendsto_iff_exists_timeChange.mp hu
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    obtain ⟨n, t, ht₀, htT, htmono, hosc⟩ :=
      exists_partition_dist_le f hT (show 0 < ε / 4 by linarith)
    let x : Fin (n + 1) → Icc (0 : ℝ) T := fun i =>
      ⟨t i, by
        constructor
        · rw [← ht₀]; exact htmono.monotone (Fin.zero_le i)
        · rw [← htT]; exact htmono.monotone (Fin.le_last i)⟩
    have hx₀ : (x 0 : ℝ) = 0 := ht₀
    have hxT : (x (Fin.last n) : ℝ) = T := htT
    have hσ (i : Fin (n + 1)) :
        Tendsto (fun k => (σ k (x i) : ℝ)) atTop (𝓝 (x i : ℝ)) := by
      apply tendsto_iff_dist_tendsto_zero.mpr
      apply squeeze_zero (fun _ => dist_nonneg) _ hdisp
      intro k
      rw [Real.dist_eq]
      have hb : BddAbove (Set.range fun t : Icc (0 : ℝ) T => |(σ k t : ℝ) - t|) :=
        ⟨T, by rintro _ ⟨t, rfl⟩; exact (σ k).abs_sub_le hT t⟩
      exact le_ciSup hb (x i)
    have hinterp := eventually_exists_small_logSlope_match x 0 (Fin.last n)
      hx₀ hxT σ hσ (show 0 < ε / 2 by linarith)
    have hsmall := hpath.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 4 by linarith))
    filter_upwards [hinterp, hsmall] with k hk hsmall
    obtain ⟨ρ, hρ, hmatch⟩ := hk
    have hbpath : BddAbove (Set.range fun s => dist (u k (σ k s)) (f s)) := by
      obtain ⟨C, hC⟩ := bddAbove_range_dist (u k) f (σ k).symm
      refine ⟨C, ?_⟩
      rintro _ ⟨s, rfl⟩
      exact hC ⟨σ k s, by simp⟩
    have hpath' (s : Icc (0 : ℝ) T) : dist (u k (σ k s)) (f s) ≤ ε / 4 :=
      (le_ciSup hbpath s).trans hsmall.le
    have hcost : completeCost f (u k) ρ ≤ ENNReal.ofReal (ε / 2) := by
      apply max_le hρ
      refine iSup_le fun s => ?_
      rw [edist_dist]
      apply ENNReal.ofReal_le_ofReal
      have hb := aligned_path_bound (u k) f x hx₀ hxT (show 0 ≤ ε / 4 by linarith)
        (fun i s t hs hs' ht ht' => hosc i s t hs hs' ht ht')
        (σ k) ρ hmatch hpath' s
      linarith
    change j1CompleteDist (u k) f < ε
    rw [j1CompleteDist_comm]
    exact (j1CompleteDist_le_of_completeCost_le f (u k) ρ
      (by linarith) hcost).trans_lt (by linarith)
  · have heq : ∀ k, u k = f := by
      intro k
      ext t
      exact (hT (t.2.1.trans t.2.2)).elim
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    exact Filter.Eventually.of_forall fun k => by
      change j1CompleteDist (u k) f < ε
      rw [heq, j1CompleteDist_self]
      exact hε

/-- The identity from logarithmic-slope paths to J1 paths is continuous. -/
theorem continuous_fromDComplete_fun [MetricSpace E] :
    @Continuous (DComplete T E) (D T E) _ _ (fun f => f) := by
  apply continuous_iff_seqContinuous.mpr
  intro u f hu
  apply tendsto_iff_dist_tendsto_zero.mpr
  have hdist : Tendsto (fun k => j1CompleteDist (u k) f) atTop (𝓝 0) :=
    tendsto_iff_dist_tendsto_zero.mp hu
  have hlim : Tendsto (fun k => max 1 T * (Real.exp (j1CompleteDist (u k) f) - 1))
      atTop (𝓝 0) := by
    simpa using tendsto_const_nhds.mul (Real.continuous_exp.continuousAt.tendsto.comp
      hdist |>.sub_const 1)
  exact squeeze_zero (fun _ => dist_nonneg)
    (fun k => dist_le_exp_j1CompleteDist_sub_one (u k) f) hlim

/-- The identity map `D T E → DComplete T E`: `d°` and the J1 metric induce the same topology
(Billingsley 1999, Theorem 12.1). -/
noncomputable def toDComplete [MetricSpace E] : D T E ≃ₜ DComplete T E where
  toEquiv := Equiv.refl _
  continuous_toFun := continuous_toDComplete_fun
  continuous_invFun := continuous_fromDComplete_fun

/-- The distance of `DComplete` is `d°`. -/
theorem dist_toDComplete [MetricSpace E] (f g : D T E) :
    dist (toDComplete f) (toDComplete g) = j1CompleteDist f g := rfl

end BGW.Skorokhod
