/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.ContourComparison
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!+# From uniform contour convergence to rooted measured tree convergence

The distance divisor tends to infinity and its ratio to the number of vertices
tends to zero. Uniform convergence of the contours, normalized to duration one
and divided by that divisor, then implies rooted GHP convergence of the vertex
spaces with uniform mass on all vertices. No probabilistic invariance principle
is assumed to have been proved by this deterministic result.
-/

@[expose] public section

open Filter
open scoped Topology
open BGW.MetricMeasure

namespace BGW.ContinuumTrees

namespace Coding

/-- Uniformly converging continuous functions have uniformly small oscillations on
any sequence of time scales tending to zero. -/
theorem eventually_oscillation_le_of_tendsto
    {f : ℕ → C(unitInterval, ℝ)} {g : C(unitInterval, ℝ)}
    (hf : Tendsto f atTop (𝓝 g)) {δ : ℕ → ℝ}
    (hδ : Tendsto δ atTop (𝓝 0)) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∀ s t : unitInterval,
      |(s : ℝ) - (t : ℝ)| ≤ δ n → |f n s - f n t| ≤ ε := by
  obtain ⟨η, hη, hcont⟩ := Metric.uniformContinuous_iff.mp
    (CompactSpace.uniformContinuous_of_continuous g.continuous) (ε / 3) (by linarith)
  have hnear : ∀ᶠ n in atTop, dist (f n) g < ε / 3 :=
    (Metric.tendsto_nhds.mp hf) _ (by linarith)
  have htime : ∀ᶠ n in atTop, δ n < η := hδ.eventually_lt_const hη
  filter_upwards [hnear, htime] with n hn hδn
  intro s t hst
  have hclose : dist s t < η := by
    simpa only [Subtype.dist_eq, Real.dist_eq] using hst.trans_lt hδn
  have hg : |g s - g t| < ε / 3 := by
    simpa only [Real.dist_eq] using hcont hclose
  have hs : |f n s - g s| < ε / 3 := by
    have h : |f n s - g s| ≤ ‖f n - g‖ := by
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using
        (f n - g).norm_coe_le_norm s
    rw [dist_eq_norm] at hn
    exact h.trans_lt hn
  have ht : |f n t - g t| < ε / 3 := by
    have h : |f n t - g t| ≤ ‖f n - g‖ := by
      simpa only [ContinuousMap.sub_apply, Real.norm_eq_abs] using
        (f n - g).norm_coe_le_norm t
    rw [dist_eq_norm] at hn
    exact h.trans_lt hn
  obtain ⟨hs₁, hs₂⟩ := abs_lt.mp hs
  obtain ⟨ht₁, ht₂⟩ := abs_lt.mp ht
  obtain ⟨hg₁, hg₂⟩ := abs_lt.mp hg
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Coding

namespace FiniteTree

/-- Once the divisor is at least one, the first-visit time error is controlled by its
ratio to tree size and the norm of the divided contour. -/
theorem contour_time_error_le (t : PlaneTree) (hn : 2 ≤ t.size)
    (b : ℝ) (hb : 1 ≤ b) :
    ‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) + 2 / (t.size : ℝ) ≤
      (‖b⁻¹ • t.contourFunction‖ + 2) * (b / (t.size : ℝ)) := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hN : (0 : ℝ) < t.size := by exact_mod_cast BGW.PlaneTree.size_pos t
  have hcast : ((t.size - 1 : ℕ) : ℝ) + 1 = (t.size : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel (show 1 ≤ t.size by omega)
  have hden : (t.size : ℝ) ≤ 2 * ((t.size - 1 : ℕ) : ℝ) := by
    have htwo : (2 : ℝ) ≤ t.size := by exact_mod_cast hn
    linarith
  have hnorm : ‖b⁻¹ • t.contourFunction‖ * b = ‖t.contourFunction‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hb0)]
    field_simp
  have hfirst := div_le_div_of_nonneg_left (norm_nonneg t.contourFunction) hN hden
  have hsecond : 2 / (t.size : ℝ) ≤ 2 * (b / (t.size : ℝ)) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right (by linarith) hN.le
  calc
    _ ≤ ‖t.contourFunction‖ / (t.size : ℝ) + 2 * (b / (t.size : ℝ)) :=
      add_le_add hfirst hsecond
    _ = (‖b⁻¹ • t.contourFunction‖ + 2) * (b / (t.size : ℝ)) := by
      simp only [add_mul, ← mul_div_assoc, hnorm]
      ring

/-- Contour convergence transfers to rooted GHP convergence with uniform vertex mass.
The divisor and size assumptions include sequences whose sizes vary irregularly. -/
theorem tendsto_rooted_scale_of_contour
    (t : ℕ → PlaneTree) (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hbinfty : Tendsto b atTop atTop)
    (hratio : Tendsto (fun n => b n / ((t n).size : ℝ)) atTop (𝓝 0))
    {g : C(unitInterval, ℝ)}
    (hcontour : Tendsto (fun n => (b n)⁻¹ • (t n).contourFunction) atTop (𝓝 g)) :
    Tendsto (fun n => RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
      (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n))))
      atTop (𝓝 (Coding.rootedMeasuredGHSpace g)) := by
  let f : ℕ → C(unitInterval, ℝ) := fun n => (b n)⁻¹ • (t n).contourFunction
  let δ : ℕ → ℝ := fun n =>
    ‖(t n).contourFunction‖ / (2 * (((t n).size - 1 : ℕ) : ℝ)) +
      2 / ((t n).size : ℝ)
  have hb1 : ∀ᶠ n in atTop, 1 ≤ b n := hbinfty.eventually (eventually_ge_atTop 1)
  have hhalf : ∀ᶠ n in atTop, b n / ((t n).size : ℝ) < 1 / 2 :=
    hratio.eventually_lt_const (by norm_num)
  have hsize : ∀ᶠ n in atTop, 2 ≤ (t n).size := by
    filter_upwards [hb1, hhalf] with n hbn hrn
    by_contra hn
    have hsingle : (t n).size = 1 := by have := BGW.PlaneTree.size_pos (t n); omega
    rw [hsingle, Nat.cast_one, div_one] at hrn
    linarith
  have hbound : Tendsto (fun n => (‖f n‖ + 2) * (b n / ((t n).size : ℝ)))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using (hcontour.norm.add_const 2).mul hratio
  have hδ : Tendsto δ atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall fun n => by dsimp [δ]; positivity) ?_ hbound
    filter_upwards [hb1, hsize] with n hbn hn
    exact contour_time_error_le (t n) hn (b n) hbn
  have herror : Tendsto (fun n => dist
      (RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n))))
      (Coding.rootedMeasuredGHSpace (f n))) atTop (𝓝 0) := by
    rw [Metric.tendsto_nhds]
    intro ε hε
    have hosc := Coding.eventually_oscillation_le_of_tendsto hcontour hδ
      (show 0 < ε / 12 by linarith)
    filter_upwards [hsize, hosc] with n hn hosc
    rw [Real.dist_eq, sub_zero, abs_of_nonneg dist_nonneg]
    have h := rooted_distance_scale_contour_le (t n) hn (b n)⁻¹
      (inv_pos.mpr (hb n)) (show 0 < ε / 12 by linarith) hosc
    change dist
      (RootedMeasuredGHSpace.scale (b n)⁻¹ (inv_pos.mpr (hb n))
        (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t n))))
      (Coding.rootedMeasuredGHSpace (f n)) ≤ 6 * (ε / 12) at h
    linarith
  have hcode := (Coding.continuous_rootedMeasuredGHSpace.tendsto g).comp hcontour
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => dist_triangle _ (Coding.rootedMeasuredGHSpace (f n)) _)
  simpa only [add_zero, Function.comp_def] using
    herror.add (tendsto_iff_dist_tendsto_zero.mp hcode)

end FiniteTree

end BGW.ContinuumTrees
