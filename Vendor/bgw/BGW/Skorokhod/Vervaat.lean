/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Basic
public import Mathlib.Topology.Order.Real
public import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.Semicontinuity.Basic

/-!
# First minimum times for càdlàg paths

The lower envelope of a path and its left limit attains the infimum, including at
the endpoints. Its minimizing set is compact, so it has a first element.

References: W. Vervaat, *A relation between Brownian bridge and Brownian excursion*, Ann.
Probab. 7 (1979); T. Duquesne, *A limit theorem for the contour process of conditioned
Galton–Watson trees*, Ann. Probab. 31 (2003), §4; items C33–C34 of `CLASSICAL_THEORY_INPUTS.md`.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

variable {T : ℝ}

private theorem eventually_lt_of_lt_min (f : D T ℝ) (t : Icc (0 : ℝ) T)
    {c : ℝ} (hc : c < min (Function.leftLim f t) (f t)) :
    ∀ᶠ s in 𝓝 t, c < f s := by
  rw [← nhdsLT_sup_nhdsGE t, eventually_sup]
  constructor
  · exact ((isCadlag f).tendsto_nhdsLT_leftLim t).eventually
      (eventually_gt_nhds (lt_min_iff.mp hc).1)
  · have hge : ContinuousWithinAt f (Ici t) t := by
      rw [ContinuousWithinAt, ← nhdsGT_sup_nhdsWithin_singleton t, tendsto_sup]
      exact ⟨(isCadlag f).isRightContinuous t,
        by simpa only [nhdsWithin_singleton] using tendsto_pure_nhds f t⟩
    exact hge.eventually (eventually_gt_nhds (lt_min_iff.mp hc).2)

private theorem lowerSemicontinuous_min_leftLim (f : D T ℝ) :
    LowerSemicontinuous (fun t => min (Function.leftLim f t) (f t)) := by
  intro t c hc
  obtain ⟨b, hcb, hbt⟩ := exists_between hc
  have he := eventually_lt_of_lt_min f t hbt
  have he' := eventually_eventually_nhds.mpr he
  filter_upwards [he, he'] with s hs hsn
  apply lt_min
  · have hlim : b ≤ Function.leftLim f s :=
      isClosed_Ici.mem_of_mapClusterPt
        ((mapClusterPt_leftLim f s).mono nhdsWithin_le_nhds)
        (hsn.mono fun _ h => h.le)
    exact hcb.trans_le hlim
  · exact hcb.trans hs

private theorem iInf_le_leftLim (f : D T ℝ) (t : Icc (0 : ℝ) T) :
    (⨅ s, f s) ≤ Function.leftLim f t := by
  apply isClosed_Ici.mem_of_mapClusterPt (mapClusterPt_leftLim f t)
  exact Eventually.of_forall fun s => ciInf_le (isBounded_range f).bddBelow s

private theorem compact_minimum_times (f : D T ℝ) (hT : 0 ≤ T) :
    IsCompact {t : ℝ | ∃ h : t ∈ Icc (0 : ℝ) T,
      min (Function.leftLim f ⟨t, h⟩) (f ⟨t, h⟩) = ⨅ s, f s} ∧
    {t : ℝ | ∃ h : t ∈ Icc (0 : ℝ) T,
      min (Function.leftLim f ⟨t, h⟩) (f ⟨t, h⟩) = ⨅ s, f s}.Nonempty := by
  let : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  let F : Icc (0 : ℝ) T → ℝ := fun t => min (Function.leftLim f t) (f t)
  have hbound (t : Icc (0 : ℝ) T) : (⨅ s, f s) ≤ F t :=
    le_min (iInf_le_leftLim f t) (ciInf_le (isBounded_range f).bddBelow t)
  have hclosed : IsClosed {t | F t = ⨅ s, f s} := by
    have heq : {t | F t = ⨅ s, f s} = F ⁻¹' Iic (⨅ s, f s) := by
      ext t
      exact ⟨fun h => h.le, fun h => le_antisymm h (hbound t)⟩
    rw [heq]
    exact (lowerSemicontinuous_min_leftLim f).isClosed_preimage _
  have hne : {t | F t = ⨅ s, f s}.Nonempty := by
    obtain ⟨t, _, ht⟩ := LowerSemicontinuousOn.exists_isMinOn
      (s := (univ : Set (Icc (0 : ℝ) T))) ⟨⟨0, le_rfl, hT⟩, mem_univ _⟩
      isCompact_univ ((lowerSemicontinuous_min_leftLim f).lowerSemicontinuousOn univ)
    refine ⟨t, le_antisymm ?_ (hbound t)⟩
    exact le_ciInf fun s => (ht (mem_univ s)).trans (min_le_right _ _)
  have heq : {t : ℝ | ∃ h : t ∈ Icc (0 : ℝ) T,
      min (Function.leftLim f ⟨t, h⟩) (f ⟨t, h⟩) = ⨅ s, f s} =
      Subtype.val '' {t | F t = ⨅ s, f s} := by
    ext t
    constructor
    · rintro ⟨h, ht⟩
      exact ⟨⟨t, h⟩, ht, rfl⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨t.property, ht⟩
  rw [heq]
  exact ⟨hclosed.isCompact.image continuous_subtype_val, hne.image _⟩

/-- A real càdlàg path on a nonempty compact interval attains its infimum as a
value or as a left limit. -/
theorem exists_min_leftLim (f : D T ℝ) (hT : 0 ≤ T) :
    ∃ t, min (Function.leftLim f t) (f t) = ⨅ s, f s := by
  obtain ⟨t, h, ht⟩ := (compact_minimum_times f hT).2
  exact ⟨⟨t, h⟩, ht⟩

/-- The first time at which a real càdlàg path on `[0,1]` attains its infimum, either as a
value or as a left limit (with `f (0-) = f 0`); C33. -/
noncomputable def vervaatTime (f : D 1 ℝ) : Set.Icc (0 : ℝ) 1 :=
  Set.projIcc 0 1 zero_le_one (sInf {t : ℝ | ∃ h : t ∈ Set.Icc (0 : ℝ) 1,
    min (Function.leftLim f ⟨t, h⟩) (f ⟨t, h⟩) = ⨅ s, f s})

private theorem sInf_minimum_times_mem (f : D 1 ℝ) :
    sInf {t : ℝ | ∃ h : t ∈ Icc (0 : ℝ) 1,
      min (Function.leftLim f ⟨t, h⟩) (f ⟨t, h⟩) = ⨅ s, f s} ∈
      {t : ℝ | ∃ h : t ∈ Icc (0 : ℝ) 1,
        min (Function.leftLim f ⟨t, h⟩) (f ⟨t, h⟩) = ⨅ s, f s} :=
  (compact_minimum_times f zero_le_one).1.sInf_mem (compact_minimum_times f zero_le_one).2

/-- The infimum is attained at `vervaatTime f`, as a value or a left limit (C33). -/
theorem min_leftLim_vervaatTime (f : D 1 ℝ) :
    min (Function.leftLim f (vervaatTime f)) (f (vervaatTime f)) = ⨅ s, f s := by
  obtain ⟨h, ht⟩ := sInf_minimum_times_mem f
  simpa only [vervaatTime, projIcc_of_mem zero_le_one h] using ht

/-- `vervaatTime f` is the first such time (C33). -/
theorem vervaatTime_le (f : D 1 ℝ) {t : Set.Icc (0 : ℝ) 1}
    (ht : min (Function.leftLim f t) (f t) = ⨅ s, f s) : vervaatTime f ≤ t := by
  obtain ⟨h, _⟩ := sInf_minimum_times_mem f
  change (vervaatTime f : ℝ) ≤ (t : ℝ)
  simp only [vervaatTime, projIcc_of_mem zero_le_one h]
  exact csInf_le (compact_minimum_times f zero_le_one).1.bddBelow ⟨t.property, ht⟩

end BGW.Skorokhod
