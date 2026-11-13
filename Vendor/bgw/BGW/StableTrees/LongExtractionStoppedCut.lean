/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionCutMiddle
public import BGW.Skorokhod.ShiftIncrement
public import BGW.Skorokhod.Scaling

/-!
# Translated stopped cuts on a fixed horizon

The finite-horizon cut is centered at its initial point and continued constantly after its end.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Center a finite path at `g`, stop at `d`, and continue constantly to the horizon `T`.
Reference: Billingsley (1999), Chapter 3. -/
noncomputable def translatedStoppedCut {M : ℝ} (T : ℝ≥0) (p : D M ℝ)
    (g d : Icc (0 : ℝ) M) (hgd : g ≤ d) : D (T : ℝ) ℝ :=
  timeSpaceScale (T : ℝ) (sub_nonneg.mpr hgd)
    (shiftIncrement g.2.1 hgd (restrict d.2.2 p), 1, ⟨1, zero_lt_one⟩)

/-- The finite stopped cut has the usual translated, clipped evaluation formula.
Reference: Billingsley (1999), Chapter 3. -/
theorem translatedStoppedCut_apply {M : ℝ} (T : ℝ≥0) (p : D M ℝ)
    (g d : Icc (0 : ℝ) M) (hgd : g ≤ d) (t : Icc (0 : ℝ) (T : ℝ)) :
    translatedStoppedCut T p g d hgd t =
      p ⟨min ((g : ℝ) + t) d, le_min (add_nonneg g.2.1 t.2.1) d.2.1,
        (min_le_right _ _).trans d.2.2⟩ - p g := by
  simp only [translatedStoppedCut, timeSpaceScale, shiftIncrement,
    BGW.Skorokhod.restrict, BGW.Skorokhod.coe_mk, one_mul]
  congr 2
  apply Subtype.ext
  change (g : ℝ) + min (t : ℝ) ((d : ℝ) - g) = min ((g : ℝ) + t) d
  rw [add_min]
  congr 1
  ring

end BGW.StableTrees
