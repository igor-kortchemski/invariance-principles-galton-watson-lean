/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Continuous

/-!
# Multiplication of paths by a convergent spatial factor

Uniform bounds on the fixed limiting path suffice for multiplication at factor one.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ} {E : Type*} [NormedRing E]

/-- Left multiplication of a càdlàg path by a constant. -/
def mulPath (k : E) (f : D T E) : D T E :=
  ⟨fun t => k * f t, (isCadlag f).continuous_comp (continuous_const.mul continuous_id)⟩

/-- Multiplication by spatial factors tending to one preserves J1 convergence. -/
theorem tendsto_mulPath_one {ι : Type*} {l : Filter ι} (hT : 0 ≤ T)
    {u : ι → D T E} {f : D T E} {k : ι → E}
    (hu : Tendsto u l (𝓝 f)) (hk : Tendsto k l (𝓝 1)) :
    Tendsto (fun i => mulPath (k i) (u i)) l (𝓝 f) := by
  have : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  let z : D T E := ⟨fun _ => 0, IsCadlag.const⟩
  obtain ⟨B, hB⟩ := bddAbove_range_dist f z (OrderIso.refl _)
  have hnorm (t : Icc (0 : ℝ) T) : ‖f t‖ ≤ B := by
    simpa [z, dist_zero_right] using hB ⟨t, rfl⟩
  obtain ⟨σ, hd, hp⟩ := tendsto_iff_exists_timeChange.mp hu
  apply tendsto_iff_exists_timeChange.mpr
  refine ⟨σ, hd, ?_⟩
  let e := fun i => ⨆ t, dist (u i (σ i t)) (f t)
  have hbound (i : ι) (t : Icc (0 : ℝ) T) :
      dist (mulPath (k i) (u i) (σ i t)) (f t) ≤
        ‖k i‖ * e i + ‖k i - 1‖ * B := by
    have halg : k i * u i (σ i t) - f t =
        k i * (u i (σ i t) - f t) + (k i - 1) * f t := by
      noncomm_ring
    change dist (k i * u i (σ i t)) (f t) ≤ _
    rw [dist_eq_norm, halg]
    calc
      _ ≤ ‖k i * (u i (σ i t) - f t)‖ + ‖(k i - 1) * f t‖ := norm_add_le _ _
      _ ≤ ‖k i‖ * ‖u i (σ i t) - f t‖ + ‖k i - 1‖ * ‖f t‖ :=
        add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ ‖k i‖ * e i + ‖k i - 1‖ * B := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          simpa only [e, dist_eq_norm] using
            le_ciSup (bddAbove_comp_dist hT (u i) f (σ i)) t
        · exact mul_le_mul_of_nonneg_left (hnorm t) (norm_nonneg _)
  have hlim : Tendsto (fun i => ‖k i‖ * e i + ‖k i - 1‖ * B) l (𝓝 0) := by
    have h := (hk.norm.mul hp).add (((hk.sub_const 1).norm).mul_const B)
    simpa using h
  apply squeeze_zero _ (fun i => ciSup_le (hbound i)) hlim
  intro i
  exact le_ciSup_of_le (bddAbove_comp_dist hT (mulPath (k i) (u i)) f (σ i))
    ⟨0, le_rfl, hT⟩ dist_nonneg

end BGW.Skorokhod
