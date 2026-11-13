/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionLadder

/-!
# Time-change bounds for deterministic extraction

The uniform errors in the J1 convergence criterion control every time, including moving times.
-/

@[expose] public section

open Filter Topology
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Vanishing clock displacement gives convergence at every fixed time.
Reference: Billingsley (1999), Chapter 3. -/
theorem tendsto_extraction_clock {M : ℝ} (hM : 0 ≤ M) {σ : ℕ → TimeChange M}
    (hσ : Tendsto (fun n => ⨆ t, |(σ n t : ℝ) - t|) atTop (𝓝 0))
    (t : Set.Icc (0 : ℝ) M) :
    Tendsto (fun n => (σ n t : ℝ)) atTop (𝓝 (t : ℝ)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => ?_) hσ
  rw [Real.dist_eq]
  exact le_ciSup (⟨M, by
    rintro _ ⟨s, rfl⟩
    exact TimeChange.abs_sub_le (σ n) hM s⟩) t

/-- Vanishing uniform path error bounds the error simultaneously at all times.
Reference: Billingsley (1999), Chapter 3. -/
theorem eventually_extraction_error_lt {M : ℝ} {u : ℕ → D M ℝ} {f : D M ℝ}
    {σ : ℕ → TimeChange M}
    (hu : Tendsto (fun n => ⨆ t, dist (u n (σ n t)) (f t)) atTop (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ t, dist (u n (σ n t)) (f t) < ε := by
  filter_upwards [hu.eventually (gt_mem_nhds hε)] with n hn t
  have hb : BddAbove (Set.range fun s => dist (u n (σ n s)) (f s)) := by
    simpa only [dist_comm] using bddAbove_range_dist f (u n) (σ n)
  exact (le_ciSup hb t).trans_lt hn

/-- Aligned path evaluations converge even at jumps of the limit.
Reference: Billingsley (1999), Chapter 3. -/
theorem tendsto_extraction_aligned_eval {M : ℝ} {u : ℕ → D M ℝ} {f : D M ℝ}
    {σ : ℕ → TimeChange M}
    (hu : Tendsto (fun n => ⨆ t, dist (u n (σ n t)) (f t)) atTop (𝓝 0))
    (t : Set.Icc (0 : ℝ) M) :
    Tendsto (fun n => u n (σ n t)) atTop (𝓝 (f t)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  exact Filter.eventually_atTop.mp
    ((eventually_extraction_error_lt hu hε).mono fun _ hn => hn t)

end BGW.StableTrees
