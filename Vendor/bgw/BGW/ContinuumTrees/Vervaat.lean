/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.CodingReroot
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-!
# The deterministic Vervaat transformation

A continuous real function on the unit interval has a first global minimizer. This canonical
choice is measurable, including for functions with several minimizers: its sublevel sets are
the closed sets on which the minimum over an initial interval equals the global minimum.

For a continuous loop, rotating time to this minimizer and subtracting the minimum gives a
continuous nonnegative function with both endpoints zero. The resulting map on the subtype
of continuous loops is measurable. Uniqueness of a Brownian bridge's minimizer, strict interior
positivity, and identification of the transformed law with a Brownian excursion are separate
probabilistic statements, not conclusions of this deterministic construction.
-/

@[expose] public section

open MeasureTheory Set

namespace BGW.ContinuumTrees.Vervaat

/-- The set of global minimizers has a least element, with both endpoint times included. -/
theorem exists_firstMinimum (g : C(unitInterval, ℝ)) :
    ∃ r, IsLeast {t : unitInterval | g t = Coding.intervalMin g 0 1} r := by
  have hcompact : IsCompact {t : unitInterval | g t = Coding.intervalMin g 0 1} :=
    (isClosed_eq g.continuous continuous_const).isCompact
  have hnonempty : {t : unitInterval | g t = Coding.intervalMin g 0 1}.Nonempty := by
    obtain ⟨r, _, hr⟩ := Coding.exists_intervalMin g 0 1
    exact ⟨r, hr.symm⟩
  exact hcompact.exists_isLeast hnonempty

/-- The first global minimizer, defined on all continuous real paths. -/
noncomputable def firstMinimum (g : C(unitInterval, ℝ)) : unitInterval :=
  (exists_firstMinimum g).choose

theorem isLeast_firstMinimum (g : C(unitInterval, ℝ)) :
    IsLeast {t : unitInterval | g t = Coding.intervalMin g 0 1} (firstMinimum g) :=
  (exists_firstMinimum g).choose_spec

private theorem globalMinimum_le (g : C(unitInterval, ℝ)) (t : unitInterval) :
    Coding.intervalMin g 0 1 ≤ g t := by
  apply Coding.intervalMin_le
  rw [uIcc_of_le (show (0 : unitInterval) ≤ 1 from unitInterval.nonneg')]
  exact ⟨unitInterval.nonneg', unitInterval.le_one'⟩

/-- The first minimum is at most `a` precisely when the initial interval already attains it. -/
theorem firstMinimum_le_iff (g : C(unitInterval, ℝ)) (a : unitInterval) :
    firstMinimum g ≤ a ↔ Coding.intervalMin g 0 a = Coding.intervalMin g 0 1 := by
  have h0a : (0 : unitInterval) ≤ a := unitInterval.nonneg'
  constructor
  · intro hle
    apply le_antisymm
    · have hmem : firstMinimum g ∈ uIcc 0 a := by
        rw [uIcc_of_le h0a]
        exact ⟨unitInterval.nonneg', hle⟩
      exact (Coding.intervalMin_le g 0 a hmem).trans_eq (isLeast_firstMinimum g).1
    · exact Coding.le_intervalMin g 0 a fun t _ => globalMinimum_le g t
  · intro heq
    obtain ⟨r, hr, hvalue⟩ := Coding.exists_intervalMin g 0 a
    have hr' : (0 : unitInterval) ≤ r ∧ r ≤ a := by
      simpa only [uIcc_of_le h0a, mem_Icc] using hr
    exact ((isLeast_firstMinimum g).2 (hvalue.symm.trans heq)).trans hr'.2

private theorem continuous_prefixMinimum (a : unitInterval) :
    Continuous (fun g : C(unitInterval, ℝ) => Coding.intervalMin g 0 a) := by
  exact (isCompact_uIcc : IsCompact (uIcc (0 : unitInterval) a)).continuous_sInf
    (f := fun g : C(unitInterval, ℝ) => fun t => g t) continuous_eval

/-- The canonical first minimizer is Borel measurable without a uniqueness assumption. -/
@[fun_prop] theorem measurable_firstMinimum : Measurable firstMinimum := by
  apply measurable_of_Iic
  intro a
  have hset : firstMinimum ⁻¹' Iic a =
      {g : C(unitInterval, ℝ) | Coding.intervalMin g 0 a = Coding.intervalMin g 0 1} := by
    ext g
    exact firstMinimum_le_iff g a
  rw [hset]
  exact (isClosed_eq (continuous_prefixMinimum a) (continuous_prefixMinimum 1)).measurableSet

private theorem value_fract (g : C(unitInterval, ℝ)) (hloop : g 0 = g 1)
    (t : unitInterval) :
    g ⟨Int.fract (t : ℝ), unitInterval.fract_mem _⟩ = g t := by
  by_cases ht : (t : ℝ) = 1
  · have ht' : t = 1 := Subtype.ext ht
    subst t
    have hz : (⟨Int.fract ((1 : unitInterval) : ℝ), unitInterval.fract_mem _⟩ :
        unitInterval) = 0 := by
      ext
      simp
    rw [hz]
    exact hloop
  · have hlt : (t : ℝ) < 1 := (lt_or_eq_of_le (unitInterval.le_one t)).resolve_right ht
    exact congrArg g (Subtype.ext (Int.fract_eq_self.mpr ⟨unitInterval.nonneg t, hlt⟩))

/-- Circular rotation of a continuous loop; the loop condition removes the jump of `fract`. -/
noncomputable def rotate (g : C(unitInterval, ℝ)) (hloop : g 0 = g 1)
    (r : unitInterval) : C(unitInterval, ℝ) where
  toFun t := g (Coding.circularShift r t)
  continuous_toFun := by
    let f : ℝ → ℝ := fun x => g (Set.projIcc 0 1 zero_le_one x)
    have hf : Continuous f := g.continuous.comp continuous_projIcc
    have hend : f 0 = f 1 := by
      have hz : (⟨0, unitInterval.zero_mem⟩ : unitInterval) = 0 := by ext; simp
      have ho : (⟨1, unitInterval.one_mem⟩ : unitInterval) = 1 := by ext; simp
      simpa only [f, Set.projIcc_of_mem zero_le_one unitInterval.zero_mem,
        Set.projIcc_of_mem zero_le_one unitInterval.one_mem, hz, ho] using hloop
    have hperiodic : Continuous (f ∘ Int.fract) := hf.continuousOn.comp_fract'' hend
    have hsum : Continuous (fun t : unitInterval => (r : ℝ) + t) :=
      continuous_const.add continuous_subtype_val
    have hclamp (x : ℝ) : Set.projIcc 0 1 zero_le_one (Int.fract x) =
        ⟨Int.fract x, unitInterval.fract_mem x⟩ :=
      Set.projIcc_of_mem zero_le_one (unitInterval.fract_mem x)
    simpa only [Function.comp_def, f, hclamp, Coding.circularShift] using hperiodic.comp hsum

@[simp] theorem rotate_apply (g : C(unitInterval, ℝ)) (hloop : g 0 = g 1)
    (r t : unitInterval) : rotate g hloop r t = g (Coding.circularShift r t) := rfl

@[simp] theorem rotate_zero (g : C(unitInterval, ℝ)) (hloop : g 0 = g 1)
    (r : unitInterval) : g (Coding.circularShift r 0) = g r := by
  simpa only [Coding.circularShift, Set.Icc.coe_zero, add_zero] using
    value_fract g hloop r

@[simp] theorem rotate_one (g : C(unitInterval, ℝ)) (hloop : g 0 = g 1)
    (r : unitInterval) : g (Coding.circularShift r 1) = g r := by
  have hs : Coding.circularShift r 1 = Coding.circularShift r 0 := by
    apply Subtype.ext
    change Int.fract ((r : ℝ) + 1) = Int.fract ((r : ℝ) + 0)
    rw [Int.fract_add_one, add_zero]
  rw [hs]
  exact rotate_zero g hloop r

/-- Rotate a continuous loop at its first global minimum and subtract that minimum. -/
noncomputable def vervaat (g : {g : C(unitInterval, ℝ) // g 0 = g 1}) :
    C(unitInterval, ℝ) where
  toFun t := rotate g.1 g.2 (firstMinimum g.1) t - Coding.intervalMin g.1 0 1
  continuous_toFun := (rotate g.1 g.2 (firstMinimum g.1)).continuous.sub continuous_const

@[simp] theorem vervaat_apply (g : {g : C(unitInterval, ℝ) // g 0 = g 1})
    (t : unitInterval) :
    vervaat g t = g.1 (Coding.circularShift (firstMinimum g.1) t) -
      Coding.intervalMin g.1 0 1 := rfl

theorem vervaat_nonneg (g : {g : C(unitInterval, ℝ) // g 0 = g 1}) (t : unitInterval) :
    0 ≤ vervaat g t := by
  rw [vervaat_apply]
  exact sub_nonneg.mpr (globalMinimum_le g.1 _)

@[simp] theorem vervaat_zero (g : {g : C(unitInterval, ℝ) // g 0 = g 1}) :
    g.1 (Coding.circularShift (firstMinimum g.1) 0) - Coding.intervalMin g.1 0 1 = 0 := by
  rw [rotate_zero g.1 g.2]
  exact sub_eq_zero.mpr (isLeast_firstMinimum g.1).1

@[simp] theorem vervaat_one (g : {g : C(unitInterval, ℝ) // g 0 = g 1}) :
    g.1 (Coding.circularShift (firstMinimum g.1) 1) - Coding.intervalMin g.1 0 1 = 0 := by
  rw [rotate_one g.1 g.2]
  exact sub_eq_zero.mpr (isLeast_firstMinimum g.1).1

/-- Measurability of the Vervaat transformation on the subtype of continuous loops. -/
@[fun_prop] theorem measurable_vervaat : Measurable vervaat := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro t
  have hm : Measurable (fun g : {g : C(unitInterval, ℝ) // g 0 = g 1} =>
      firstMinimum g.1) := measurable_firstMinimum.comp measurable_subtype_coe
  have hs : Measurable (fun g : {g : C(unitInterval, ℝ) // g 0 = g 1} =>
      Coding.circularShift (firstMinimum g.1) t) :=
    ((hm.subtype_coe.add measurable_const).fract).subtype_mk
  have heval : Measurable (fun p : C(unitInterval, ℝ) × unitInterval => p.1 p.2) :=
    continuous_eval.measurable
  change Measurable (fun g : {g : C(unitInterval, ℝ) // g 0 = g 1} =>
    g.1 (Coding.circularShift (firstMinimum g.1) t) - Coding.intervalMin g.1 0 1)
  exact (heval.comp (measurable_subtype_coe.prodMk hs)).sub
    ((continuous_prefixMinimum 1).measurable.comp measurable_subtype_coe)

end BGW.ContinuumTrees.Vervaat
