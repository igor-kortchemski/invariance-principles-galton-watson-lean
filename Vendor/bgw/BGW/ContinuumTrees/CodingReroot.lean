/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.CodingMeasure
public import BGW.MetricMeasure.RootedMeasuredGHSpace
public import Mathlib.Topology.Algebra.Order.Floor
public import Mathlib.Topology.Order.ProjIcc
public import Mathlib.MeasureTheory.Function.Floor
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The continuous excursion obtained by changing the root

Circular time shift uses the representative in `[0, 1)`. This time map is measurable, but
is neither continuous nor surjective on the closed unit interval in general. Composing with
the coding projection closes the endpoints and gives a continuous surjection onto the tree.
Distance from the point represented by the chosen root time then gives a nonnegative
continuous coding function with zero endpoints.

This is the construction in Le Gall, *Random trees and applications*, Lemma 2.3,
pp. 273–274, <https://arxiv.org/pdf/math/0511515v1>. The exact distance identity is proved
from attained interval minima, treating both sides of the circular cut and intervals crossing
it. It descends to a surjective isometry sending the new root to the chosen vertex.
Circular time shift preserves Lebesgue probability, by translation invariance of Haar measure
on the unit additive circle. Consequently this same isometry preserves the actual mass measure.
-/

@[expose] public section

open MeasureTheory Set

namespace BGW.ContinuumTrees.Coding

/-- Circular time shift with its value represented in `[0, 1)`. -/
noncomputable def circularShift (r t : unitInterval) : unitInterval :=
  ⟨Int.fract ((r : ℝ) + t), unitInterval.fract_mem _⟩

theorem measurable_circularShift (r : unitInterval) : Measurable (circularShift r) :=
  ((measurable_const.add measurable_subtype_coe).fract).subtype_mk

private theorem projection_fract (g : C(unitInterval, ℝ)) (hg : ∀ t, 0 ≤ g t)
    (h0 : g 0 = 0) (h1 : g 1 = 0) (t : unitInterval) :
    projection g ⟨Int.fract (t : ℝ), unitInterval.fract_mem _⟩ = projection g t := by
  by_cases ht : (t : ℝ) = 1
  · have ht' : t = 1 := Subtype.ext ht
    subst t
    simpa using projection_zero_eq_one g hg h0 h1
  · have hlt : (t : ℝ) < 1 := (lt_or_eq_of_le t.property.2).resolve_right ht
    have hf : Int.fract (t : ℝ) = (t : ℝ) := Int.fract_eq_self.mpr ⟨t.property.1, hlt⟩
    exact congrArg (projection g) (Subtype.ext hf)

/-- The circular traversal of the coded tree, continuous because its endpoint images agree. -/
noncomputable def circularProjection (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) : C(unitInterval, Space g) where
  toFun t := projection g (circularShift r t)
  continuous_toFun := by
    let f : ℝ → Space g := fun x => projection g (Set.projIcc 0 1 zero_le_one x)
    have hf : Continuous f := (continuous_projection g).comp continuous_projIcc
    have hend : f 0 = f 1 := by
      have hz : (⟨0, unitInterval.zero_mem⟩ : unitInterval) = 0 := by ext; simp
      have ho : (⟨1, unitInterval.one_mem⟩ : unitInterval) = 1 := by ext; simp
      simpa only [f, Set.projIcc_of_mem zero_le_one unitInterval.zero_mem,
        Set.projIcc_of_mem zero_le_one unitInterval.one_mem, hz, ho] using
        projection_zero_eq_one g hg h0 h1
    have hperiodic : Continuous (f ∘ Int.fract) := hf.continuousOn.comp_fract'' hend
    have hsum : Continuous (fun t : unitInterval => (r : ℝ) + t) :=
      continuous_const.add continuous_subtype_val
    have hclamp (x : ℝ) : Set.projIcc 0 1 zero_le_one (Int.fract x) =
        ⟨Int.fract x, unitInterval.fract_mem x⟩ :=
      Set.projIcc_of_mem zero_le_one (unitInterval.fract_mem x)
    simpa only [Function.comp_def, f, hclamp, circularShift] using hperiodic.comp hsum

@[simp] theorem circularProjection_apply (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) (t : unitInterval) :
    circularProjection g r hg h0 h1 t = projection g (circularShift r t) := rfl

/-- Although circular time shift omits time one, its image under the coding projection is full. -/
theorem circularProjection_surjective (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    Function.Surjective (circularProjection g r hg h0 h1) := by
  intro x
  obtain ⟨s, rfl⟩ := projection_surjective g x
  let t : unitInterval := ⟨Int.fract ((s : ℝ) - r), unitInterval.fract_mem _⟩
  refine ⟨t, ?_⟩
  have ht : circularShift r t = ⟨Int.fract (s : ℝ), unitInterval.fract_mem _⟩ := by
    apply Subtype.ext
    change Int.fract ((r : ℝ) + Int.fract ((s : ℝ) - r)) = Int.fract (s : ℝ)
    have hsum : (r : ℝ) + ((s : ℝ) - r) = s := by linarith
    rw [Int.fract_add_fract, hsum]
  exact (congrArg (projection g) ht).trans (projection_fract g hg h0 h1 s)

@[simp] theorem circularProjection_zero (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    projection g (circularShift r 0) = projection g r := by
  simpa only [circularShift, Set.Icc.coe_zero, add_zero] using
    projection_fract g hg h0 h1 r

@[simp] theorem circularProjection_one (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    projection g (circularShift r 1) = projection g r := by
  have hs : circularShift r 1 = circularShift r 0 := by
    apply Subtype.ext
    change Int.fract ((r : ℝ) + 1) = Int.fract ((r : ℝ) + 0)
    rw [Int.fract_add_one, add_zero]
  rw [hs]
  exact circularProjection_zero g r hg h0 h1

/-- The continuous function recording distance from the new root during circular traversal. -/
noncomputable def reroot (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) : C(unitInterval, ℝ) where
  toFun t := dist (projection g r) (circularProjection g r hg h0 h1 t)
  continuous_toFun := continuous_const.dist (circularProjection g r hg h0 h1).continuous

/-- The construction is exactly the interval-minimum rerooting formula. -/
@[simp] theorem reroot_apply (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) (t : unitInterval) :
    reroot g r hg h0 h1 t = codingDist g r (circularShift r t) := rfl

theorem reroot_nonneg (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) (t : unitInterval) :
    0 ≤ reroot g r hg h0 h1 t := by
  change 0 ≤ dist (projection g r) (circularProjection g r hg h0 h1 t)
  exact dist_nonneg

@[simp] theorem reroot_zero (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    codingDist g r (circularShift r 0) = 0 := by
  change dist (projection g r) (projection g (circularShift r 0)) = 0
  rw [circularProjection_zero g r hg h0 h1, dist_self]

@[simp] theorem reroot_one (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    codingDist g r (circularShift r 1) = 0 := by
  change dist (projection g r) (projection g (circularShift r 1)) = 0
  rw [circularProjection_one g r hg h0 h1, dist_self]

private theorem intervalMin_subinterval (g : C(unitInterval, ℝ)) {a b c d : unitInterval}
    (h : uIcc a b ⊆ uIcc c d) : intervalMin g c d ≤ intervalMin g a b := by
  apply le_intervalMin
  intro v hv
  exact intervalMin_le g c d (h hv)

private theorem intervalMin_split (g : C(unitInterval, ℝ)) {r a b : unitInterval}
    (ha : a ∈ uIcc r b) :
    intervalMin g r b = min (intervalMin g r a) (intervalMin g a b) := by
  apply le_antisymm
  · exact le_min (intervalMin_subinterval g (uIcc_subset_uIcc_left ha))
      (intervalMin_subinterval g (uIcc_subset_uIcc_right ha))
  · exact min_intervalMin_le g r a b

private theorem mem_uIcc_of_between {r a b v : unitInterval}
    (ha : a ∈ uIcc r b) (hv : v ∈ uIcc a b) : a ∈ uIcc r v := by
  rcases le_total r b with hrb | hbr
  · have ha' : r ≤ a ∧ a ≤ b := by simpa only [uIcc_of_le hrb, mem_Icc] using ha
    have hv' : a ≤ v ∧ v ≤ b := by simpa only [uIcc_of_le ha'.2, mem_Icc] using hv
    exact mem_uIcc_of_le ha'.1 hv'.1
  · have ha' : b ≤ a ∧ a ≤ r := by simpa only [uIcc_of_ge hbr, mem_Icc] using ha
    have hv' : b ≤ v ∧ v ≤ a := by simpa only [uIcc_of_ge ha'.1, mem_Icc] using hv
    exact mem_uIcc_of_ge hv'.2 ha'.2

private theorem exists_level_with_runningMin (g : C(unitInterval, ℝ)) (a b : unitInterval)
    {A : ℝ} (hmin : intervalMin g a b ≤ A) (hA : A ≤ g a) :
    ∃ v ∈ uIcc a b, g v = A ∧ intervalMin g a v = A := by
  have hc : Continuous (fun v : unitInterval => intervalMin g a v) :=
    (continuous_intervalMin g).comp (continuous_const.prodMk continuous_id)
  have hlevel : A ∈ uIcc (intervalMin g a a) (intervalMin g a b) := by
    rw [intervalMin_self]
    exact mem_uIcc_of_ge hmin hA
  obtain ⟨w, hw, hwm⟩ := (intermediate_value_uIcc hc.continuousOn) hlevel
  obtain ⟨v, hv, hvm⟩ := exists_intervalMin g a w
  have hgv : g v = A := hvm.symm.trans hwm
  refine ⟨v, (uIcc_subset_uIcc_left hw) hv, hgv, ?_⟩
  apply le_antisymm
  · exact (intervalMin_le_right g a v).trans_eq hgv
  · rw [← hwm]
    exact intervalMin_subinterval g (uIcc_subset_uIcc_left hv)

private noncomputable def distanceProfile (g : C(unitInterval, ℝ)) (r : unitInterval) :
    C(unitInterval, ℝ) where
  toFun v := codingDist g r v
  continuous_toFun :=
    (continuous_codingDist g).comp (continuous_const.prodMk continuous_id)

private theorem intervalMin_distanceProfile (g : C(unitInterval, ℝ)) {r a b : unitInterval}
    (ha : a ∈ uIcc r b) :
    intervalMin (distanceProfile g r) a b = g r + intervalMin g a b - intervalMin g r a -
      min (intervalMin g r a) (intervalMin g a b) := by
  let A := intervalMin g r a
  let B := intervalMin g a b
  have hminv (v : unitInterval) (hv : v ∈ uIcc a b) :
      intervalMin g r v = min A (intervalMin g a v) :=
    intervalMin_split g (mem_uIcc_of_between ha hv)
  change intervalMin (distanceProfile g r) a b = g r + B - A - min A B
  rcases le_total A B with hAB | hBA
  · rw [min_eq_left hAB]
    apply le_antisymm
    · obtain ⟨v, hv, hvm⟩ := exists_intervalMin g a b
      have hAv : A ≤ intervalMin g a v :=
        hAB.trans (intervalMin_subinterval g (uIcc_subset_uIcc_left hv))
      have hu := intervalMin_le (distanceProfile g r) a b hv
      change intervalMin (distanceProfile g r) a b ≤
        g r + g v - 2 * intervalMin g r v at hu
      rw [hminv v hv, min_eq_left hAv] at hu
      change B = g v at hvm
      linarith
    · apply le_intervalMin
      intro v hv
      have hAv : A ≤ intervalMin g a v :=
        hAB.trans (intervalMin_subinterval g (uIcc_subset_uIcc_left hv))
      have hBv : B ≤ g v := intervalMin_le g a b hv
      change g r + B - A - A ≤ g r + g v - 2 * intervalMin g r v
      rw [hminv v hv, min_eq_left hAv]
      linarith
  · rw [min_eq_right hBA]
    apply le_antisymm
    · obtain ⟨v, hv, hgv, hAv⟩ :=
        exists_level_with_runningMin g a b hBA (intervalMin_le_right g r a)
      have hu := intervalMin_le (distanceProfile g r) a b hv
      change intervalMin (distanceProfile g r) a b ≤
        g r + g v - 2 * intervalMin g r v at hu
      rw [hminv v hv, hAv, min_self, hgv] at hu
      linarith
    · apply le_intervalMin
      intro v hv
      have hleft := min_le_left A (intervalMin g a v)
      have hright := (min_le_right A (intervalMin g a v)).trans (intervalMin_le_right g a v)
      change g r + B - A - B ≤ g r + g v - 2 * intervalMin g r v
      rw [hminv v hv]
      linarith

private theorem intervalMin_translate (f k : C(unitInterval, ℝ))
    {s t a b : unitInterval} {c : ℝ} (hst : s ≤ t)
    (ha : (a : ℝ) = c + s) (hb : (b : ℝ) = c + t)
    (hval : ∀ u v : unitInterval, u ∈ Icc s t → (v : ℝ) = c + u → k u = f v) :
    intervalMin k s t = intervalMin f a b := by
  have hst' : (s : ℝ) ≤ t := hst
  have hab : a ≤ b := by change (a : ℝ) ≤ b; linarith
  apply le_antisymm
  · obtain ⟨v, hv, hvm⟩ := exists_intervalMin f a b
    have hv' : a ≤ v ∧ v ≤ b := by simpa only [uIcc_of_le hab, mem_Icc] using hv
    have hav : (a : ℝ) ≤ v := hv'.1
    have hvb : (v : ℝ) ≤ b := hv'.2
    let u : unitInterval := ⟨(v : ℝ) - c, by
      constructor <;> linarith [s.property.1, t.property.2]⟩
    have hu : u ∈ Icc s t := by
      constructor
      · change (s : ℝ) ≤ (v : ℝ) - c
        linarith
      · change (v : ℝ) - c ≤ (t : ℝ)
        linarith
    have heq : (v : ℝ) = c + u := by dsimp [u]; linarith
    have hm := intervalMin_le k s t (Icc_subset_uIcc hu)
    rw [hval u v hu heq] at hm
    exact hm.trans_eq hvm.symm
  · apply le_intervalMin
    intro u hu
    have hu' : s ≤ u ∧ u ≤ t := by simpa only [uIcc_of_le hst, mem_Icc] using hu
    have hsu : (s : ℝ) ≤ u := hu'.1
    have hut : (u : ℝ) ≤ t := hu'.2
    let v : unitInterval := ⟨c + u, by
      constructor <;> linarith [a.property.1, b.property.2]⟩
    have hav : a ≤ v := by change (a : ℝ) ≤ c + u; linarith
    have hvb : v ≤ b := by change c + (u : ℝ) ≤ b; linarith
    rw [hval u v hu' rfl]
    exact intervalMin_le f a b (mem_uIcc_of_le hav hvb)

private theorem projection_circularShift_of_add (g : C(unitInterval, ℝ))
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0)
    (r u v : unitInterval) (hv : (v : ℝ) = (r : ℝ) + u) :
    projection g (circularShift r u) = projection g v := by
  have hs : circularShift r u = ⟨Int.fract (v : ℝ), unitInterval.fract_mem _⟩ := by
    apply Subtype.ext
    change Int.fract ((r : ℝ) + u) = Int.fract (v : ℝ)
    rw [hv]
  exact (congrArg (projection g) hs).trans (projection_fract g hg h0 h1 v)

private theorem projection_circularShift_of_sub (g : C(unitInterval, ℝ))
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0)
    (r u v : unitInterval) (hv : (v : ℝ) = (r : ℝ) + u - 1) :
    projection g (circularShift r u) = projection g v := by
  have hs : circularShift r u = ⟨Int.fract (v : ℝ), unitInterval.fract_mem _⟩ := by
    apply Subtype.ext
    change Int.fract ((r : ℝ) + u) = Int.fract (v : ℝ)
    rw [hv, Int.fract_sub_one]
  exact (congrArg (projection g) hs).trans (projection_fract g hg h0 h1 v)

private theorem reroot_eq_profile_of_add (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0)
    (u v : unitInterval) (hv : (v : ℝ) = (r : ℝ) + u) :
    reroot g r hg h0 h1 u = distanceProfile g r v := by
  change dist (projection g r) (projection g (circularShift r u)) =
    dist (projection g r) (projection g v)
  rw [projection_circularShift_of_add g hg h0 h1 r u v hv]

private theorem reroot_eq_profile_of_sub (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0)
    (u v : unitInterval) (hv : (v : ℝ) = (r : ℝ) + u - 1) :
    reroot g r hg h0 h1 u = distanceProfile g r v := by
  change dist (projection g r) (projection g (circularShift r u)) =
    dist (projection g r) (projection g v)
  rw [projection_circularShift_of_sub g hg h0 h1 r u v hv]

private theorem intervalMin_reroot_before (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0)
    {s t a b : unitInterval} (hst : s ≤ t)
    (ha : (a : ℝ) = (r : ℝ) + s) (hb : (b : ℝ) = (r : ℝ) + t) :
    intervalMin (reroot g r hg h0 h1) s t =
      g r + intervalMin g a b - intervalMin g r a -
        min (intervalMin g r a) (intervalMin g a b) := by
  have hst' : (s : ℝ) ≤ t := hst
  have hra : r ≤ a := by change (r : ℝ) ≤ a; linarith [s.property.1]
  have hab : a ≤ b := by change (a : ℝ) ≤ b; linarith
  calc
    _ = intervalMin (distanceProfile g r) a b :=
      intervalMin_translate _ _ hst ha hb
        (fun u v _ hv => reroot_eq_profile_of_add g r hg h0 h1 u v hv)
    _ = _ := intervalMin_distanceProfile g (mem_uIcc_of_le hra hab)

private theorem intervalMin_reroot_after (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0)
    {s t a b : unitInterval} (hst : s ≤ t)
    (ha : (a : ℝ) = (r : ℝ) + s - 1) (hb : (b : ℝ) = (r : ℝ) + t - 1) :
    intervalMin (reroot g r hg h0 h1) s t =
      g r + intervalMin g a b - intervalMin g r b -
        min (intervalMin g r b) (intervalMin g a b) := by
  have hst' : (s : ℝ) ≤ t := hst
  have hab : a ≤ b := by change (a : ℝ) ≤ b; linarith
  have hbr : b ≤ r := by change (b : ℝ) ≤ r; linarith [t.property.2]
  have ha' : (a : ℝ) = ((r : ℝ) - 1) + s := by linarith
  have hb' : (b : ℝ) = ((r : ℝ) - 1) + t := by linarith
  calc
    _ = intervalMin (distanceProfile g r) a b :=
      intervalMin_translate _ _ hst ha' hb' (fun u v _ hv =>
        reroot_eq_profile_of_sub g r hg h0 h1 u v (by linarith))
    _ = intervalMin (distanceProfile g r) b a := intervalMin_comm _ _ _
    _ = _ := by
      simpa only [intervalMin_comm g b a] using
        intervalMin_distanceProfile g (mem_uIcc_of_ge hab hbr)

private theorem codingDist_reroot_before (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0)
    {s t a b : unitInterval} (hst : s ≤ t)
    (ha : (a : ℝ) = (r : ℝ) + s) (hb : (b : ℝ) = (r : ℝ) + t) :
    codingDist (reroot g r hg h0 h1) s t = codingDist g a b := by
  have hst' : (s : ℝ) ≤ t := hst
  have hra : r ≤ a := by change (r : ℝ) ≤ a; linarith [s.property.1]
  have hab : a ≤ b := by change (a : ℝ) ≤ b; linarith
  have hsplit := intervalMin_split g (mem_uIcc_of_le hra hab)
  rw [codingDist, reroot_eq_profile_of_add g r hg h0 h1 s a ha,
    reroot_eq_profile_of_add g r hg h0 h1 t b hb,
    intervalMin_reroot_before g r hg h0 h1 hst ha hb]
  change (g r + g a - 2 * intervalMin g r a) + (g r + g b - 2 * intervalMin g r b) -
    2 * (g r + intervalMin g a b - intervalMin g r a -
      min (intervalMin g r a) (intervalMin g a b)) = g a + g b - 2 * intervalMin g a b
  rw [hsplit]
  ring

private theorem codingDist_reroot_after (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0)
    {s t a b : unitInterval} (hst : s ≤ t)
    (ha : (a : ℝ) = (r : ℝ) + s - 1) (hb : (b : ℝ) = (r : ℝ) + t - 1) :
    codingDist (reroot g r hg h0 h1) s t = codingDist g a b := by
  have hst' : (s : ℝ) ≤ t := hst
  have hab : a ≤ b := by change (a : ℝ) ≤ b; linarith
  have hbr : b ≤ r := by change (b : ℝ) ≤ r; linarith [t.property.2]
  have hsplit : intervalMin g r a = min (intervalMin g r b) (intervalMin g a b) := by
    simpa only [intervalMin_comm g b a] using
      intervalMin_split g (mem_uIcc_of_ge hab hbr)
  rw [codingDist, reroot_eq_profile_of_sub g r hg h0 h1 s a ha,
    reroot_eq_profile_of_sub g r hg h0 h1 t b hb,
    intervalMin_reroot_after g r hg h0 h1 hst ha hb]
  change (g r + g a - 2 * intervalMin g r a) + (g r + g b - 2 * intervalMin g r b) -
    2 * (g r + intervalMin g a b - intervalMin g r b -
      min (intervalMin g r b) (intervalMin g a b)) = g a + g b - 2 * intervalMin g a b
  rw [hsplit]
  ring

private theorem codingDist_reroot_across (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0)
    {s t a b : unitInterval}
    (ha : (a : ℝ) = (r : ℝ) + s) (hb : (b : ℝ) = (r : ℝ) + t - 1) :
    codingDist (reroot g r hg h0 h1) s t = codingDist g a b := by
  let c := unitInterval.symm r
  have hc : (c : ℝ) = 1 - r := unitInterval.coe_symm_eq r
  have hsc : s ≤ c := by change (s : ℝ) ≤ c; linarith [a.property.2]
  have hct : c ≤ t := by change (c : ℝ) ≤ t; linarith [b.property.1]
  have hra : r ≤ a := by change (r : ℝ) ≤ a; linarith [s.property.1]
  have hbr : b ≤ r := by change (b : ℝ) ≤ r; linarith [t.property.2]
  have hc1 : ((1 : unitInterval) : ℝ) = (r : ℝ) + c := by
    rw [Set.Icc.coe_one, hc]
    ring
  have hc0 : ((0 : unitInterval) : ℝ) = (r : ℝ) + c - 1 := by
    rw [Set.Icc.coe_zero, hc]
    ring
  have hm1 : intervalMin g a 1 = 0 := by
    apply le_antisymm
    · exact (intervalMin_le_right g a 1).trans_eq h1
    · exact le_intervalMin g a 1 (fun v _ => hg v)
  have hm0 : intervalMin g 0 b = 0 := by
    apply le_antisymm
    · exact (intervalMin_le_left g 0 b).trans_eq h0
    · exact le_intervalMin g 0 b (fun v _ => hg v)
  have hA : 0 ≤ intervalMin g r a := le_intervalMin g r a (fun v _ => hg v)
  have hB : 0 ≤ intervalMin g r b := le_intervalMin g r b (fun v _ => hg v)
  have hm : intervalMin (reroot g r hg h0 h1) s t =
      min (g r - intervalMin g r a) (g r - intervalMin g r b) := by
    rw [intervalMin_split _ (mem_uIcc_of_le hsc hct),
      intervalMin_reroot_before g r hg h0 h1 hsc ha hc1,
      intervalMin_reroot_after g r hg h0 h1 hct hc0 hb, hm1, hm0]
    simp only [min_eq_right hA, min_eq_right hB, add_zero, sub_zero]
  have hsplit : intervalMin g a b = min (intervalMin g r a) (intervalMin g r b) := by
    simpa only [intervalMin_comm g a r] using
      intervalMin_split g (mem_uIcc_of_ge hbr hra)
  rw [codingDist, reroot_eq_profile_of_add g r hg h0 h1 s a ha,
    reroot_eq_profile_of_sub g r hg h0 h1 t b hb, hm]
  change (g r + g a - 2 * intervalMin g r a) + (g r + g b - 2 * intervalMin g r b) -
    2 * min (g r - intervalMin g r a) (g r - intervalMin g r b) =
      g a + g b - 2 * intervalMin g a b
  rw [hsplit]
  rcases le_total (intervalMin g r a) (intervalMin g r b) with hAB | hBA
  · rw [min_eq_left hAB, min_eq_right (by linarith :
      g r - intervalMin g r b ≤ g r - intervalMin g r a)]
    ring
  · rw [min_eq_right hBA, min_eq_left (by linarith :
      g r - intervalMin g r a ≤ g r - intervalMin g r b)]
    ring

private theorem codingDist_reroot_of_le (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0)
    {s t : unitInterval} (hst : s ≤ t) :
    codingDist (reroot g r hg h0 h1) s t =
      codingDist g (circularShift r s) (circularShift r t) := by
  have hst' : (s : ℝ) ≤ t := hst
  by_cases ht : (r : ℝ) + t ≤ 1
  · let a : unitInterval := ⟨(r : ℝ) + s, by
      constructor
      · exact add_nonneg r.property.1 s.property.1
      · linarith⟩
    let b : unitInterval := ⟨(r : ℝ) + t, add_nonneg r.property.1 t.property.1, ht⟩
    have hd := codingDist_reroot_before g r hg h0 h1 hst (a := a) (b := b) rfl rfl
    have hpa := projection_circularShift_of_add g hg h0 h1 r s a rfl
    have hpb := projection_circularShift_of_add g hg h0 h1 r t b rfl
    exact hd.trans (by simpa only [dist_projection] using (congrArg₂ dist hpa hpb).symm)
  · by_cases hs : 1 ≤ (r : ℝ) + s
    · let a : unitInterval := ⟨(r : ℝ) + s - 1, by
        constructor <;> linarith [r.property.2, s.property.2]⟩
      let b : unitInterval := ⟨(r : ℝ) + t - 1, by
        constructor <;> linarith [r.property.2, t.property.2]⟩
      have hd := codingDist_reroot_after g r hg h0 h1 hst (a := a) (b := b) rfl rfl
      have hpa := projection_circularShift_of_sub g hg h0 h1 r s a rfl
      have hpb := projection_circularShift_of_sub g hg h0 h1 r t b rfl
      exact hd.trans (by simpa only [dist_projection] using (congrArg₂ dist hpa hpb).symm)
    · let a : unitInterval := ⟨(r : ℝ) + s, by
        constructor
        · exact add_nonneg r.property.1 s.property.1
        · linarith⟩
      let b : unitInterval := ⟨(r : ℝ) + t - 1, by
        constructor <;> linarith [r.property.2, t.property.2]⟩
      have hd := codingDist_reroot_across g r hg h0 h1 (a := a) (b := b) rfl rfl
      have hpa := projection_circularShift_of_add g hg h0 h1 r s a rfl
      have hpb := projection_circularShift_of_sub g hg h0 h1 r t b rfl
      exact hd.trans (by simpa only [dist_projection] using (congrArg₂ dist hpa hpb).symm)

/-- Changing the root preserves all coded distances after the circular change of time. -/
theorem codingDist_reroot (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) (s t : unitInterval) :
    codingDist (reroot g r hg h0 h1) s t =
      codingDist g (circularShift r s) (circularShift r t) := by
  rcases le_total s t with hst | hts
  · exact codingDist_reroot_of_le g r hg h0 h1 hst
  · calc
      _ = codingDist (reroot g r hg h0 h1) t s := codingDist_comm _ _ _
      _ = codingDist g (circularShift r t) (circularShift r s) :=
        codingDist_reroot_of_le g r hg h0 h1 hts
      _ = _ := codingDist_comm _ _ _

/-- The map on coding quotients induced by circular traversal of the original tree. -/
noncomputable def rerootMap (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    Space (reroot g r hg h0 h1) → Space g :=
  SeparationQuotient.lift
    (fun x : Point (reroot g r hg h0 h1) => projection g (circularShift r x.time)) (by
      intro x y hxy
      apply dist_eq_zero.mp
      rw [dist_projection, ← codingDist_reroot g r hg h0 h1 x.time y.time]
      exact Metric.inseparable_iff.mp hxy)

theorem rerootMap_isometry (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    Isometry (rerootMap g r hg h0 h1) := by
  apply Isometry.of_dist_eq
  intro x y
  obtain ⟨s, rfl⟩ := projection_surjective (reroot g r hg h0 h1) x
  obtain ⟨t, rfl⟩ := projection_surjective (reroot g r hg h0 h1) y
  change dist (projection g (circularShift r s)) (projection g (circularShift r t)) =
    dist (projection (reroot g r hg h0 h1) s) (projection (reroot g r hg h0 h1) t)
  rw [dist_projection, dist_projection, codingDist_reroot]

theorem rerootMap_surjective (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    Function.Surjective (rerootMap g r hg h0 h1) := by
  intro x
  obtain ⟨t, ht⟩ := circularProjection_surjective g r hg h0 h1 x
  exact ⟨projection (reroot g r hg h0 h1) t, ht⟩

/-- The surjective isometry from the rerooted coding quotient to the original tree. -/
noncomputable def rerootIsometry (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    Space (reroot g r hg h0 h1) ≃ᵢ Space g where
  toEquiv := Equiv.ofBijective (rerootMap g r hg h0 h1)
    ⟨(rerootMap_isometry g r hg h0 h1).injective, rerootMap_surjective g r hg h0 h1⟩
  isometry_toFun := rerootMap_isometry g r hg h0 h1

@[simp] theorem rerootIsometry_projection (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) (t : unitInterval) :
    rerootIsometry g r hg h0 h1 (projection (reroot g r hg h0 h1) t) =
      projection g (circularShift r t) := rfl

/-- The new coding root is sent to the chosen vertex, rather than necessarily to the old root. -/
@[simp] theorem rerootIsometry_root (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    rerootIsometry g r hg h0 h1 (root (reroot g r hg h0 h1)) = projection g r := by
  change rerootIsometry g r hg h0 h1 (projection (reroot g r hg h0 h1) 0) = projection g r
  rw [rerootIsometry_projection]
  exact circularProjection_zero g r hg h0 h1

private def timeToCircle (t : unitInterval) : UnitAddCircle := ((t : ℝ) : UnitAddCircle)

private theorem measurePreserving_timeToCircle :
    MeasurePreserving timeToCircle (volume : Measure unitInterval) (volume : Measure UnitAddCircle) := by
  have hm := UnitAddCircle.measurePreserving_mk (0 : ℝ)
  rw [zero_add, restrict_Ioc_eq_restrict_Icc] at hm
  exact hm.comp unitInterval.measurePreserving_coe

private noncomputable def circleRepresentative (x : UnitAddCircle) : unitInterval :=
  ⟨(AddCircle.equivIco 1 0 x : ℝ), by
    have hx := (AddCircle.equivIco 1 0 x).property
    exact ⟨hx.1, by simpa only [zero_add] using hx.2.le⟩⟩

private theorem measurable_circleRepresentative : Measurable circleRepresentative := by
  have hm : Measurable (fun x : UnitAddCircle => (AddCircle.equivIco 1 0 x : ℝ)) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  exact hm.subtype_mk

private theorem circleRepresentative_coe (x : ℝ) :
    circleRepresentative (x : UnitAddCircle) =
      ⟨Int.fract x, unitInterval.fract_mem x⟩ := by
  apply Subtype.ext
  change (AddCircle.equivIco 1 0 (QuotientAddGroup.mk x) : ℝ) = Int.fract x
  simpa only [div_one, mul_one] using AddCircle.coe_equivIco_mk_apply (p := (1 : ℝ)) x

private theorem measurePreserving_circleRepresentative :
    MeasurePreserving circleRepresentative (volume : Measure UnitAddCircle)
      (volume : Measure unitInterval) := by
  have hae : circleRepresentative ∘ timeToCircle =ᵐ[(volume : Measure unitInterval)] id := by
    filter_upwards [(volume : Measure unitInterval).ae_ne (1 : unitInterval)] with t ht
    have ht' : (t : ℝ) ≠ 1 := fun h => ht (Subtype.ext h)
    have hlt : (t : ℝ) < 1 := (lt_or_eq_of_le t.property.2).resolve_right ht'
    have hf : Int.fract (t : ℝ) = (t : ℝ) := Int.fract_eq_self.mpr ⟨t.property.1, hlt⟩
    change circleRepresentative ((t : ℝ) : UnitAddCircle) = t
    rw [circleRepresentative_coe]
    exact Subtype.ext hf
  refine ⟨measurable_circleRepresentative, ?_⟩
  calc
    (volume : Measure UnitAddCircle).map circleRepresentative =
        ((volume : Measure unitInterval).map timeToCircle).map circleRepresentative := by
      rw [measurePreserving_timeToCircle.map_eq]
    _ = (volume : Measure unitInterval).map (circleRepresentative ∘ timeToCircle) :=
      Measure.map_map measurable_circleRepresentative measurePreserving_timeToCircle.measurable
    _ = (volume : Measure unitInterval).map id := Measure.map_congr hae
    _ = volume := Measure.map_id

/-- Circular time shift preserves Lebesgue probability, including the endpoint convention. -/
theorem measurePreserving_circularShift (r : unitInterval) :
    MeasurePreserving (circularShift r) (volume : Measure unitInterval) volume := by
  have hfun : circularShift r =
      circleRepresentative ∘ (timeToCircle r + ·) ∘ timeToCircle := by
    funext t
    change circularShift r t =
      circleRepresentative (((r : ℝ) : UnitAddCircle) + ((t : ℝ) : UnitAddCircle))
    rw [← AddCircle.coe_add, circleRepresentative_coe]
    rfl
  rw [hfun]
  exact measurePreserving_circleRepresentative.comp
    ((measurePreserving_add_left (volume : Measure UnitAddCircle) (timeToCircle r)).comp
      measurePreserving_timeToCircle)

/-- The rerooting isometry carries the genuine pushforward mass to the original mass measure. -/
theorem map_mass_rerootIsometry (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    (mass (reroot g r hg h0 h1) : Measure (Space (reroot g r hg h0 h1))).map
      (rerootIsometry g r hg h0 h1) = (mass g : Measure (Space g)) := by
  let e := rerootIsometry g r hg h0 h1
  change ((volume : Measure unitInterval).map (projection (reroot g r hg h0 h1))).map e =
    (volume : Measure unitInterval).map (projection g)
  rw [Measure.map_map e.continuous.measurable (measurable_projection _)]
  have hcomp : e ∘ projection (reroot g r hg h0 h1) = projection g ∘ circularShift r := by
    funext t
    exact rerootIsometry_projection g r hg h0 h1 t
  rw [hcomp, ← Measure.map_map (measurable_projection g) (measurable_circularShift r),
    (measurePreserving_circularShift r).map_eq]

/-- The rerooted coding is measured-isometric to the original tree rooted at time `r`. -/
theorem measuredIsometry_reroot (g : C(unitInterval, ℝ)) (r : unitInterval)
    (hg : ∀ t, 0 ≤ g t) (h0 : g 0 = 0) (h1 : g 1 = 0) :
    BGW.MetricMeasure.RootedCompactMeasuredSpace.MeasuredIsometry
      (rootedCompactMeasuredSpace (reroot g r hg h0 h1))
      { space := compactMeasuredSpace g, root := projection g r } :=
  ⟨rerootIsometry g r hg h0 h1, map_mass_rerootIsometry g r hg h0 h1,
    rerootIsometry_root g r hg h0 h1⟩

end BGW.ContinuumTrees.Coding
