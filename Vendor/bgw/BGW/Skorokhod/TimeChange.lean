/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.Topology.Order.Cadlag
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Order.Real
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed

/-!
# Time changes on a compact real interval

An increasing order isomorphism of `[0,T]` fixes its endpoints and stays within distance `T`
of the identity. The displacement supremum is invariant under inversion.
-/

@[expose] public section

open Set

namespace BGW.Skorokhod

/-- Increasing order isomorphisms of the interval `[0,T]`. -/
abbrev TimeChange (T : ℝ) := Set.Icc (0 : ℝ) T ≃o Set.Icc (0 : ℝ) T

variable {T : ℝ}

/-- A time change fixes the left endpoint whenever the interval is nonempty. -/
theorem TimeChange.apply_zero (σ : TimeChange T) (hT : 0 ≤ T) :
    σ ⟨0, by simp [hT]⟩ = ⟨0, by simp [hT]⟩ := by
  apply Subtype.ext
  have hpre : (0 : ℝ) ≤ (σ.symm ⟨0, by simp [hT]⟩ : ℝ) :=
    (σ.symm ⟨0, by simp [hT]⟩).property.1
  have hpre' : (⟨0, by simp [hT]⟩ : Set.Icc (0 : ℝ) T) ≤ σ.symm ⟨0, by simp [hT]⟩ := by
    exact hpre
  have hmono := σ.monotone hpre'
  have hmono' : (σ ⟨0, by simp [hT]⟩ : ℝ) ≤ 0 := by
    exact (Subtype.coe_le_coe).2 (by simpa only [OrderIso.apply_symm_apply] using hmono)
  have hle : (σ ⟨0, by simp [hT]⟩ : ℝ) ≤ 0 := hmono'
  exact le_antisymm hle (σ ⟨0, by simp [hT]⟩).property.1

/-- A time change fixes the right endpoint whenever the interval is nonempty. -/
theorem TimeChange.apply_top (σ : TimeChange T) (hT : 0 ≤ T) :
    σ ⟨T, by simp [hT]⟩ = ⟨T, by simp [hT]⟩ := by
  apply Subtype.ext
  have hpre : (σ.symm ⟨T, by simp [hT]⟩ : ℝ) ≤ T :=
    (σ.symm ⟨T, by simp [hT]⟩).property.2
  have hpre' : σ.symm ⟨T, by simp [hT]⟩ ≤ (⟨T, by simp [hT]⟩ : Set.Icc (0 : ℝ) T) := by
    exact hpre
  have hmono := σ.monotone hpre'
  have hmono' : T ≤ (σ ⟨T, by simp [hT]⟩ : ℝ) := by
    exact (Subtype.coe_le_coe).2 (by simpa only [OrderIso.apply_symm_apply] using hmono)
  have hle : T ≤ (σ ⟨T, by simp [hT]⟩ : ℝ) := hmono'
  exact le_antisymm (σ ⟨T, by simp [hT]⟩).property.2 hle

/-- Every time change moves a time by at most the length of its interval. -/
theorem TimeChange.abs_sub_le (σ : TimeChange T) (_hT : 0 ≤ T) (t : Set.Icc (0 : ℝ) T) :
    |(σ t : ℝ) - t| ≤ T := by
  have ht := t.property
  have hσ := (σ t).property
  rw [abs_le]
  rcases ht with ⟨ht0, htT⟩
  rcases hσ with ⟨hσ0, hσT⟩
  constructor <;> linarith

/-- The displacement supremum is unchanged when a time change is inverted. -/
theorem TimeChange.iSup_abs_sub_symm (σ : TimeChange T) :
    (⨆ t : Set.Icc (0 : ℝ) T, |(σ.symm t : ℝ) - t|) =
      ⨆ t : Set.Icc (0 : ℝ) T, |(σ t : ℝ) - t| := by
  calc
    (⨆ t : Set.Icc (0 : ℝ) T, |(σ.symm t : ℝ) - t|) =
        ⨆ t : Set.Icc (0 : ℝ) T, |(σ (σ.symm t) : ℝ) - σ.symm t| := by
          apply iSup_congr
          intro t
          rw [σ.apply_symm_apply]
          simp only [abs_sub_comm]
    _ = ⨆ t : Set.Icc (0 : ℝ) T, |(σ t : ℝ) - t| := by
          exact Equiv.iSup_comp
            (g := fun t : Set.Icc (0 : ℝ) T => |(σ t : ℝ) - t|) σ.symm.toEquiv

end BGW.Skorokhod
