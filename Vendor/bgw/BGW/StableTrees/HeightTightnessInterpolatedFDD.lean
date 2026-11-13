/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessModulus
public import BGW.StableTrees.DiscreteHeightApprox
import BGW.MetricMeasure.WeakPerturbation

/-!
# Joint finite-dimensional limits for interpolated heights

Each interpolation error is bounded by the largest adjacent height jump.
Vanishing jumps transfer K09 to interpolated height observations while retaining
the entire walk coordinate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest BGW.Skorokhod BGW.StableTrees.DiscreteHeightApprox
namespace BGW.StableTrees.HeightTightness

/-- The interpolation error at a fixed time is bounded by the largest adjacent height jump. -/
theorem forestHeightPath_sub_scaledHeight_le {B : ℕ → ℝ} {n : ℕ}
    {T : ℝ≥0} {t : ℝ≥0} (ht : t ≤ T) (hB : 0 ≤ B n) (ω : ℕ → ℕ) :
    |forestHeightPath B n T ω ⟨t, t.coe_nonneg, ht⟩ - scaledHeight B n ω t| ≤
      maxHeightJump B n T ω := by
  let u := (n : ℝ) * (t : ℝ)
  let k := ⌊u⌋₊
  let a := u - (k : ℝ)
  let c := B n / (n : ℝ)
  have hc : 0 ≤ c := div_nonneg hB (Nat.cast_nonneg n)
  have ha0 : 0 ≤ a := sub_nonneg.mpr (Nat.floor_le (by dsimp [u]; positivity))
  have ha1 : a ≤ 1 := by have hh := Nat.lt_floor_add_one u; dsimp [a, k]; linarith
  have hk : k ∈ Finset.range (⌊(n : ℝ) * (T : ℝ)⌋₊ + 1) := by
    apply Finset.mem_range.mpr
    have hh := Nat.floor_mono (mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg n))
    change k ≤ ⌊(n : ℝ) * (T : ℝ)⌋₊ at hh
    omega
  have hsup := Finset.le_sup (f := fun k =>
    ((forestHeight ω (k + 1) : ℤ) - forestHeight ω k).natAbs) hk
  have he : (((forestHeight ω (k + 1) : ℤ) - forestHeight ω k).natAbs : ℝ) =
      |(forestHeight ω (k + 1) : ℝ) - forestHeight ω k| := by
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  have hb : c * |(forestHeight ω (k + 1) : ℝ) - forestHeight ω k| ≤ maxHeightJump B n T ω := by
    rw [← he]
    exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hsup) hc
  have hid : forestHeightPath B n T ω ⟨t, t.coe_nonneg, ht⟩ - scaledHeight B n ω t =
      a * c * ((forestHeight ω (k + 1) : ℝ) - forestHeight ω k) := by
    change c * forestHeightLin ω u - c * (forestHeight ω k : ℝ) = _
    unfold forestHeightLin
    dsimp only [a, k]
    ring
  rw [hid, abs_mul, abs_mul, abs_of_nonneg ha0, abs_of_nonneg hc]
  nlinarith [mul_nonneg hc (abs_nonneg ((forestHeight ω (k + 1) : ℝ) - forestHeight ω k))]

/-- The walk and the interpolated height observations at finitely many times. -/
noncomputable def interpolatedHeightJoint (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    {r : ℕ} (t : Fin r → Set.Icc (0 : ℝ) (T : ℝ)) (ω : ℕ → ℕ) :
    D (T : ℝ) ℝ × (Fin r → ℝ) :=
  (forestWalkPath B n T ω, fun i => forestHeightPath B n T ω (t i))

/-- Interpolated height observations are measurable. -/
theorem measurable_interpolatedHeightJoint (B : ℕ → ℝ) (n : ℕ) (T : ℝ≥0)
    {r : ℕ} (t : Fin r → Set.Icc (0 : ℝ) (T : ℝ)) :
    Measurable (interpolatedHeightJoint B n T t) := by
  exact (measurable_forestPairPath B n T).fst.prodMk (Measurable.of_eval fun i =>
    (ContinuousMap.measurable_eval (t i)).comp (measurable_forestPairPath B n T).snd)

/-- K09 extends to interpolated height observations because the adjacent jumps vanish. -/
theorem tendsto_interpolatedHeightJoint {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) {r : ℕ}
    (t : Fin r → Set.Icc (0 : ℝ) (T : ℝ)) :
    Tendsto (fun n : ℕ => (offspringSeqLaw μ).map (interpolatedHeightJoint B n T t)) atTop
      (𝓝 ((stableLocalLaw θ).map
        (heightLimitJoint θ T (fun i => ⟨t i, (t i).property.1⟩)))) := by
  let τ : Fin r → ℝ≥0 := fun i => ⟨t i, (t i).property.1⟩
  have hτ (i : Fin r) : τ i ≤ T := (t i).property.2
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun _ => offspringSeqLaw μ) (fun n => measurable_interpolatedHeightJoint B n T t)
    (fun n => measurable_heightJoint B n T τ) ?_ (tendsto_walk_height_fdd h hT τ hτ)
  intro ε hε
  have hjump := (tendstoInMeasure_iff_measureReal_norm.mp
    (maxHeightJump_tendstoInMeasure h hT)) ε hε
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hjump
  · exact Eventually.of_forall fun _ => measureReal_nonneg
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply measureReal_mono ?_ (measure_ne_top _ _)
    intro ω hω
    have hB := h.pos n hn
    have hnonneg : 0 ≤ maxHeightJump B n T ω := by unfold maxHeightJump; positivity
    have hd : dist (interpolatedHeightJoint B n T t ω) (heightJoint B n T τ ω) ≤
        maxHeightJump B n T ω := by
      simp only [interpolatedHeightJoint, heightJoint, dist_prod_same_left]
      apply (dist_pi_le_iff hnonneg).mpr
      intro i
      rw [Real.dist_eq]
      exact forestHeightPath_sub_scaledHeight_le (hτ i) hB.le ω
    change ε ≤ ‖maxHeightJump B n T ω - 0‖
    rw [sub_zero, Real.norm_eq_abs, abs_of_nonneg hnonneg]
    exact (hω.trans_le hd).le

end BGW.StableTrees.HeightTightness
