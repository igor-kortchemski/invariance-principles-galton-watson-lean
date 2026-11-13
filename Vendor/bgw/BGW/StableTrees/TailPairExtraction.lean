/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.TailPairBasic
import BGW.StableTrees.PathTailLocalization
import BGW.StableTrees.PathTailReconstruction
import Mathlib.Topology.CompactOpen

/-!
# Continuous endpoint-aligned height cuts

Subtracting the endpoint height gives a continuous stopped cut for arbitrary continuous host
paths. At ladder endpoints and at limiting excursion endpoints this subtraction vanishes.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees BGW.Probability.RealWalk

namespace BGW.StableTrees.TailPair

open BGW.StableTrees.DiscreteForest BGW.StableTrees.PathTail

/-- A continuous stopped height cut, clipped to the host horizon and centered at its endpoint. -/
noncomputable def cutHeightPath (M T : ℝ≥0)
    (H : C(Icc (0 : ℝ) (M : ℝ), ℝ)) (g d : ℝ) : C(Icc (0 : ℝ) (T : ℝ), ℝ) :=
  ⟨fun t => H (projIcc 0 (M : ℝ) M.2 (min (g + t) d)) -
      H (projIcc 0 (M : ℝ) M.2 d),
    (H.continuous.comp (continuous_projIcc.comp
      ((continuous_const.add continuous_subtype_val).min continuous_const))).sub
        continuous_const⟩

/-- Cutting a continuous height depends continuously on the host and both endpoints. -/
theorem continuous_cutHeightPath (M T : ℝ≥0) :
    Continuous (fun p : C(Icc (0 : ℝ) (M : ℝ), ℝ) × ℝ × ℝ =>
      cutHeightPath M T p.1 p.2.1 p.2.2) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : (C(Icc (0 : ℝ) (M : ℝ), ℝ) × ℝ × ℝ) ×
    Icc (0 : ℝ) (T : ℝ) =>
      p.1.1 (projIcc 0 (M : ℝ) M.2 (min (p.1.2.1 + p.2) p.1.2.2)) -
        p.1.1 (projIcc 0 (M : ℝ) M.2 p.1.2.2))
  fun_prop

/-- At a zero endpoint, the continuous cut equals the stopped extraction on nonnegative ages. -/
theorem cutHeightPath_eq_extractedHeight (M T : ℝ≥0)
    (H : C(Icc (0 : ℝ) (M : ℝ), ℝ)) {g d : ℝ}
    (hg : 0 ≤ g) (hgd : g ≤ d) (hdM : d ≤ M)
    (hd : H ⟨d, hg.trans hgd, hdM⟩ = 0) (t : Icc (0 : ℝ) (T : ℝ)) :
    cutHeightPath M T H g d t =
      extractedHeight (fun s => H (projIcc 0 (M : ℝ) M.2 s)) g d t := by
  have hproj : projIcc 0 (M : ℝ) M.2 d = ⟨d, hg.trans hgd, hdM⟩ := by
    exact projIcc_of_mem M.2 ⟨hg.trans hgd, hdM⟩
  change H (projIcc 0 (M : ℝ) M.2 (min (g + t) d)) -
    H (projIcc 0 (M : ℝ) M.2 d) = _
  rw [hproj, hd, sub_zero, extractedHeight]
  split_ifs with ht
  · rw [min_eq_left (by linarith)]
  · rw [min_eq_right (by linarith), hproj, hd]

end BGW.StableTrees.TailPair
