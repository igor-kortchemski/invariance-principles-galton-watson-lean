/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.VervaatRotate
public import BGW.Skorokhod.Continuous
public import BGW.ContinuumTrees.Vervaat

/-!
# Comparison with the continuous-loop Vervaat map

On a continuous loop, the first minimizing time agrees with the existing
continuous-path choice, and the endpoint correction vanishes.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

private theorem iInf_ofContinuous (g : C(unitInterval, ℝ)) :
    (⨅ s, ofContinuous g s) = ContinuumTrees.Coding.intervalMin g 0 1 := by
  have hb := (isBounded_range (ofContinuous g)).bddBelow
  apply le_antisymm
  · have h := (ContinuumTrees.Vervaat.isLeast_firstMinimum g).1
    exact (ciInf_le hb (ContinuumTrees.Vervaat.firstMinimum g)).trans_eq h
  · apply le_ciInf
    intro t
    apply ContinuumTrees.Coding.intervalMin_le
    rw [uIcc_of_le (show (0 : unitInterval) ≤ 1 from unitInterval.nonneg')]
    exact ⟨unitInterval.nonneg', unitInterval.le_one'⟩

/-- On continuous paths, the first minimizing time agrees with the continuous-path choice. -/
theorem vervaatTime_ofContinuous (g : C(unitInterval, ℝ)) :
    vervaatTime (ofContinuous g) = ContinuumTrees.Vervaat.firstMinimum g := by
  have hl (t : unitInterval) : Function.leftLim (ofContinuous g) t = g t :=
    g.continuous.continuousAt.continuousWithinAt.leftLim_eq
  apply le_antisymm
  · apply vervaatTime_le
    rw [hl, show ofContinuous g (ContinuumTrees.Vervaat.firstMinimum g) =
      g (ContinuumTrees.Vervaat.firstMinimum g) from rfl, min_self, iInf_ofContinuous]
    exact (ContinuumTrees.Vervaat.isLeast_firstMinimum g).1
  · apply (ContinuumTrees.Vervaat.isLeast_firstMinimum g).2
    have h := min_leftLim_vervaatTime (ofContinuous g)
    rw [hl, show ofContinuous g (vervaatTime (ofContinuous g)) =
      g (vervaatTime (ofContinuous g)) from rfl, min_self, iInf_ofContinuous] at h
    exact h

private theorem loop_value_fract (g : C(unitInterval, ℝ)) (hloop : g 0 = g 1)
    (t : unitInterval) :
    g ⟨Int.fract (t : ℝ), unitInterval.fract_mem _⟩ = g t := by
  by_cases ht : (t : ℝ) = 1
  · have ht' : t = 1 := Subtype.ext ht
    subst t
    simpa using hloop
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
    exact congrArg g (Subtype.ext (Int.fract_eq_self.mpr ⟨t.2.1, hlt⟩))

/-- On continuous loops, the càdlàg Vervaat map agrees with the existing continuous-loop
transform (C33, comparison with `ContinuumTrees.Vervaat.vervaat`). -/
theorem vervaatD_ofContinuous (g : C(unitInterval, ℝ)) (hloop : g 0 = g 1) :
    vervaatD (ofContinuous g) = ofContinuous (ContinuumTrees.Vervaat.vervaat ⟨g, hloop⟩) := by
  apply BGW.Skorokhod.ext
  intro t
  change (if (vervaatTime (ofContinuous g) : ℝ) + t ≤ 1 then _ else _) =
    g (ContinuumTrees.Coding.circularShift (ContinuumTrees.Vervaat.firstMinimum g) t) -
      ContinuumTrees.Coding.intervalMin g 0 1
  rw [vervaatTime_ofContinuous, iInf_ofContinuous]
  let r := ContinuumTrees.Vervaat.firstMinimum g
  change (if (r : ℝ) + t ≤ 1 then _ else _) = _
  split_ifs with ht
  · have hmem : (r : ℝ) + t ∈ Icc (0 : ℝ) 1 :=
      ⟨add_nonneg r.2.1 t.2.1, ht⟩
    rw [projIcc_of_mem zero_le_one hmem]
    exact congrArg (fun x => x - ContinuumTrees.Coding.intervalMin g 0 1)
      (loop_value_fract g hloop ⟨(r : ℝ) + t, hmem⟩).symm
  · have hmem : (r : ℝ) + t - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [r.2.2, t.2.2]
    rw [projIcc_of_mem zero_le_one hmem]
    have he := loop_value_fract g hloop ⟨(r : ℝ) + t - 1, hmem⟩
    simp only [Int.fract_sub_one] at he
    change g ⟨(r : ℝ) + t - 1, hmem⟩ + g 1 -
      ContinuumTrees.Coding.intervalMin g 0 1 - g 0 =
        g ⟨Int.fract ((r : ℝ) + t), unitInterval.fract_mem _⟩ -
          ContinuumTrees.Coding.intervalMin g 0 1
    rw [he, hloop]
    ring

end BGW.Skorokhod
