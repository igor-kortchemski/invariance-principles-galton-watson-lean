/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCorrectionExit

/-!
# Divergence of the state and time cutoffs

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Càdlàg reflection is bounded on every compact interval, so its cutoffs diverge on every path. -/
theorem tendsto_errCutoff_top (f : DLoc) :
    Tendsto (fun n : ℕ => errCutoff n f) atTop (𝓝 ⊤) := by
  apply ENNReal.tendsto_nhds_top_iff_nnreal.mpr
  intro T
  have hc : IsCompact (Iic (T + 1 : ℝ≥0)) := by
    simpa only [Icc, Iic, zero_le, true_and] using
      (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) (T + 1)))
  have hb := isBounded_image_of_isCadlag_of_isCompact (isCadlag_supReflectedFrom 0 f) hc
  obtain ⟨C, hC⟩ := hb.bddAbove
  obtain ⟨N, hN⟩ := exists_nat_gt (max C (T : ℝ))
  filter_upwards [eventually_ge_atTop N] with n hn
  have hCn : C < (n : ℝ) := (lt_of_le_of_lt (le_max_left _ _) hN).trans_le
    (Nat.cast_le.mpr hn)
  have hTn : (T : ℝ) < n := (lt_of_le_of_lt (le_max_right _ _) hN).trans_le
    (Nat.cast_le.mpr hn)
  have he : ((T + 1 : ℝ≥0) : ℝ≥0∞) ≤ supReflectedExit n f := by
    apply le_iInf
    intro s
    split_ifs with hs
    · have hTs : T + 1 ≤ s := by
        by_contra h
        have hb := hC (mem_image_of_mem (supReflectedFrom 0 f) (le_of_not_ge h))
        exact (hCn.trans hs).not_ge hb
      exact ENNReal.coe_le_coe.mpr hTs
    · exact le_top
  exact lt_min ((ENNReal.coe_lt_coe.mpr (lt_add_one T)).trans_le he)
    (by exact_mod_cast hTn)

end BGW.StableTrees
