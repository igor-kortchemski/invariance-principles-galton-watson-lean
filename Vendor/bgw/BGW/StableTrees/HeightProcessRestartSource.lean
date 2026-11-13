/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessRestartMeasure
import BGW.Probability.Stieltjes

/-!
# Old and fresh exploration source windows

A deterministic split at the restart time retains its endpoint in the old source.
The fresh source is the translated Stieltjes measure of the centered shifted path.
A height translation therefore pushes it to the fresh summand in concatenation.
Ordered supports and fixed-time gap-freeness identify the old summand's support top.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees
open BGW.Probability

/-- The future-infimum window after a time shift is translated by the path value at that time. -/
theorem futureInf_shift_window (f : DLoc) (t r : ℝ≥0) {u : ℝ≥0} (hu : u ≤ r) :
    futureInf f (t + r) (t + u) = f.1 t + futureInf (DLoc.shift t f) r u := by
  rw [futureInf_eq_runningInf_shift, min_eq_left (add_le_add le_rfl hu),
    add_tsub_add_eq_tsub_left, futureInf_eq_runningInf_shift, min_eq_left hu, DLoc.shift_shift]
  change f.1 (t + u) + runningInfLoc (DLoc.shift (t + u) f) (r - u) =
    f.1 t + (f.1 (t + u) - f.1 t + runningInfLoc (DLoc.shift (t + u) f) (r - u))
  ring

/-- The fresh exploration source is the translated source of the centered shifted path. -/
theorem exploration_source_fresh (f : DLoc) (t r : ℝ≥0) :
    ((explorationStieltjes (DLoc.shift t f) r).measure.restrict (Ioc 0 (r : ℝ))).map
      (fun x : ℝ => (t : ℝ) + x) =
      (explorationStieltjes f (t + r)).measure.restrict (Ioc (t : ℝ) ((t + r : ℝ≥0) : ℝ)) := by
  have hF (g : DLoc) (v : ℝ≥0) (x : ℝ) :
      explorationStieltjes g v x = futureInf g v x.toNNReal := by
    simp only [explorationStieltjes, dite_eq_left (explorationStieltjes_spec g v), futureInfFun]
  have hh := stieltjes_translate_window (F := explorationStieltjes (DLoc.shift t f) r)
    (G := explorationStieltjes f (t + r)) (t := (t : ℝ)) (C := f.1 t) r.2
  simp only [NNReal.coe_add]
  apply hh
  intro x hx
  have hsum : ((t : ℝ) + x).toNNReal = t + x.toNNReal := by
    apply NNReal.coe_injective
    change max ((t : ℝ) + x) 0 = (t : ℝ) + max x 0
    exact (max_eq_left (show (0 : ℝ) ≤ (t : ℝ) + x from add_nonneg t.2 hx.1)).trans
      (congrArg (fun y : ℝ => (t : ℝ) + y)
        (max_eq_left (show (0 : ℝ) ≤ x from hx.1))).symm
  rw [hF, hF, hsum, futureInf_shift_window f t r (Real.toNNReal_le_iff_le_coe.mpr hx.2)]

/-- Splitting the exploration source at an intermediate deterministic time retains the endpoint. -/
theorem exploration_source_split (θ : ℝ) (f : DLoc) (t r : ℝ≥0) :
    exploration θ f (t + r) =
      ((explorationStieltjes f (t + r)).measure.restrict (Ioc 0 (t : ℝ))).map
        (fun x : ℝ => (height θ f x.toNNReal).toNNReal) +
      ((explorationStieltjes f (t + r)).measure.restrict
        (Ioc (t : ℝ) ((t + r : ℝ≥0) : ℝ))).map
        (fun x : ℝ => (height θ f x.toNNReal).toNNReal) := by
  have hU : Ioc (0 : ℝ) ((t + r : ℝ≥0) : ℝ) =
      Ioc 0 (t : ℝ) ∪ Ioc (t : ℝ) ((t + r : ℝ≥0) : ℝ) := by
    exact (Ioc_union_Ioc_eq_Ioc t.2 (by exact_mod_cast (le_add_right le_rfl : t ≤ t + r))).symm
  rw [exploration, hU, Measure.restrict_union (by
    exact disjoint_left.mpr (fun _ hx hy => (not_lt_of_ge hx.2) hy.1)) measurableSet_Ioc,
    Measure.map_add _ _ (measurable_exploration_heightMap θ f)]



/-- Ordered source summands and fixed-time gap-freeness identify the left summand's top. -/
theorem topHeight_left_of_ordered_sum {ρ σ : Measure ℝ≥0} {K H : ℝ}
    (hK : 0 ≤ K) (hKH : K ≤ H) (hρ : ρ (Ioi K.toNNReal) = 0)
    (hσ : σ (Iio K.toNNReal) = 0)
    (hgap : ∀ h : ℝ≥0, (h : ℝ) < H → ∀ ε : ℝ, 0 < ε →
      0 < (ρ + σ) (Metric.ball h ε)) : (topHeight ρ : ℝ) = K := by
  apply topHeight_eq_of_support_bounds hK hρ
  intro h hh ε hε
  let δ := min ε ((K - (h : ℝ)) / 2)
  have hδ : 0 < δ := lt_min hε (half_pos (sub_pos.mpr hh))
  have hsub : Metric.ball h δ ⊆ Iio K.toNNReal := by
    intro x hx
    have hx' : |(x : ℝ) - h| < δ := hx
    have hxle := le_abs_self ((x : ℝ) - h)
    have hδK : δ ≤ (K - (h : ℝ)) / 2 := min_le_right _ _
    have hxK : (x : ℝ) < K := by linarith only [hx', hxle, hδK, hh]
    change x < K.toNNReal
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hK]
    exact hxK
  have hz : σ (Metric.ball h δ) = 0 := measure_mono_null hsub hσ
  have hp := hgap h (hh.trans_le hKH) δ hδ
  rw [Measure.add_apply, hz, add_zero] at hp
  exact hp.trans_le (measure_mono (Metric.ball_subset_ball (min_le_left _ _)))


/-- A fresh ancestral height translation gives the fresh summand of exploration concatenation. -/
theorem exploration_fresh_source_map (θ : ℝ) (f : DLoc) (t r : ℝ≥0) (K : ℝ≥0)
    (he : ∀ᵐ x ∂(explorationStieltjes (DLoc.shift t f) r).measure.restrict (Ioc 0 (r : ℝ)),
      (height θ f (((t : ℝ) + x).toNNReal)).toNNReal =
        (height θ (DLoc.shift t f) x.toNNReal).toNNReal + K) :
    ((explorationStieltjes f (t + r)).measure.restrict
      (Ioc (t : ℝ) ((t + r : ℝ≥0) : ℝ))).map
        (fun x : ℝ => (height θ f x.toNNReal).toNNReal) =
      (exploration θ (DLoc.shift t f) r).map (fun h => h + K) := by
  rw [← exploration_source_fresh f t r]
  exact map_fresh_height_translation (measurable_const.add measurable_id)
    (measurable_exploration_heightMap θ f)
    (measurable_exploration_heightMap θ (DLoc.shift t f)) K he

end BGW.StableTrees
