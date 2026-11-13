/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.RestrictContinuityTimeChange
import BGW.Skorokhod.CompleteMetricLimits

/-!
# Extending a linear time scaling

A linear map on a proper initial subinterval extends to an ambient time change with
arbitrarily small displacement as its slope tends to one.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

/-- Reparametrize a path by an increasing homeomorphism of its time interval. -/
def reparam {T : ℝ} {E : Type*} [TopologicalSpace E] (g : D T E) (σ : TimeChange T) : D T E :=
  ⟨g ∘ σ, by exact isCadlag_comp_timeChange (isCadlag g) σ⟩

/-- Reparametrization costs at most the uniform displacement of the time change. -/
theorem dist_reparam_le {T : ℝ} {E : Type*} [MetricSpace E] (hT : 0 ≤ T)
    (g : D T E) (σ : TimeChange T) :
    dist (reparam g σ) g ≤ ⨆ t, |(σ t : ℝ) - t| := by
  rw [dist_eq_j1Dist]
  have h := j1Dist_le_timeChange_cost hT (reparam g σ) g σ
  simpa [reparam, max_eq_left (displacement_nonneg σ hT)] using h

/-- Linear scalings tending to one have arbitrarily small ambient endpoint corrections. -/
theorem eventually_exists_timeChange_scale {T a : ℝ} (ha : 0 < a) (haT : a < T)
    {ι : Type*} {l : Filter ι} {s : ι → Ioi (0 : ℝ)}
    (hs : Tendsto (fun i => (s i : ℝ)) l (𝓝 1)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ i in l, ∃ γ : TimeChange T,
      (∀ t : Icc (0 : ℝ) T, (t : ℝ) ≤ a → (γ t : ℝ) = s i * t) ∧
      ∀ t : Icc (0 : ℝ) T, |(γ t : ℝ) - t| ≤ ε := by
  let δ := min ((T - a) / 2) (ε / 4)
  have hδ : 0 < δ := lt_min (by linarith) (by positivity)
  have hδT : δ ≤ (T - a) / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 4 := min_le_right _ _
  let r := T - δ
  have har : a ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := ha.le.trans har
  have hrT : r < T := by dsimp [r]; linarith
  have hsmall : ∀ᶠ i in l, |(s i : ℝ) - 1| * r < min (δ / 2) (ε / 4) := by
    have hh := ((hs.sub_const 1).abs.mul_const r)
    have hh' : Tendsto (fun i => |(s i : ℝ) - 1| * r) l (𝓝 0) := by simpa using hh
    exact (tendsto_order.1 hh').2 _ (lt_min (by positivity) (by positivity))
  filter_upwards [hsmall] with i hi
  have hsr : |(s i : ℝ) * r - r| < min (δ / 2) (ε / 4) := by
    rw [show (s i : ℝ) * r - r = ((s i : ℝ) - 1) * r by ring,
      abs_mul, abs_of_nonneg hr]
    exact hi
  have hsrT : (s i : ℝ) * r < T := by
    have hh := (abs_lt.mp (hsr.trans_le (min_le_left _ _))).2
    dsimp [r] at hh ⊢
    linarith
  obtain ⟨γ, hhead, htail⟩ := exists_endpoint_timeChange hr hrT
    (fun t => (s i : ℝ) * t) (continuous_const.mul continuous_subtype_val)
    (fun x y hxy => mul_lt_mul_of_pos_left hxy (s i).2) (by simp) hsrT
  refine ⟨γ, fun t ht => hhead t (ht.trans har), ?_⟩
  intro t
  by_cases ht : (t : ℝ) ≤ r
  · rw [hhead t ht, show (s i : ℝ) * t - t = ((s i : ℝ) - 1) * t by ring,
      abs_mul, abs_of_nonneg t.2.1]
    exact (mul_le_mul_of_nonneg_left ht (abs_nonneg _)).trans
      (hi.le.trans ((min_le_right _ _).trans (by linarith)))
  · have hlow := htail t (le_of_not_ge ht)
    have hupp := (γ t).2.2
    have hta := t.2.2
    have hsrl := abs_lt.mp (hsr.trans_le (min_le_right _ _))
    rw [abs_le]
    dsimp [r] at *
    constructor <;> linarith

end BGW.Skorokhod
