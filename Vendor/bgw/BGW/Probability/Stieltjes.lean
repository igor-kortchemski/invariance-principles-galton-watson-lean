/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.Stieltjes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto

/-! # Finite-window operations on Stieltjes measures

Agreement, translation, and capping of Stieltjes functions on an initial interval give the
corresponding identities and inequalities for their associated measures.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

namespace BGW.Probability

private theorem ofReal_min_increment {A B C D : ℝ} (hAB : A ≤ B) (hCD : C ≤ D) :
    ENNReal.ofReal (min B C - min A C) = min (ENNReal.ofReal (B - A))
      (ENNReal.ofReal (D - A) - ENNReal.ofReal (D - C)) := by
  by_cases hCA : C ≤ A
  · rw [min_eq_right (hCA.trans hAB), min_eq_right hCA, sub_self, ENNReal.ofReal_zero,
      tsub_eq_zero_of_le (ENNReal.ofReal_le_ofReal (sub_le_sub_left hCA D)), min_zero]
  · rw [min_eq_left (not_le.mp hCA).le,
      ← ENNReal.ofReal_sub _ (sub_nonneg.mpr hCD)]
    have he : D - A - (D - C) = C - A := by ring
    rw [he, ← min_sub_sub_right, ENNReal.ofReal_min]

/-- Agreement of Stieltjes functions on a closed window gives agreement of their source measures. -/
theorem stieltjes_restrict_Ioc_congr {F G : StieltjesFunction ℝ} {T : ℝ} (hT : 0 ≤ T)
    (he : ∀ x ∈ Icc 0 T, F x = G x) :
    F.measure.restrict (Ioc 0 T) = G.measure.restrict (Ioc 0 T) := by
  let : IsFiniteMeasure (F.measure.restrict (Ioc 0 T)) := ⟨by
    rw [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  by_cases ha : a ≤ 0
  · have hz : Iic a ∩ Ioc 0 T = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt_of_ge ha) (hx.2.1.trans_le hx.1)
    simp only [hz, measure_empty]
  · have hA : 0 ≤ min a T := le_min (not_le.mp ha).le hT
    have hi : Iic a ∩ Ioc 0 T = Ioc 0 (min a T) := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
      tauto
    rw [hi, StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
      he _ ⟨hA, min_le_right _ _⟩, he 0 ⟨le_rfl, hT⟩]

/-- Capping a Stieltjes function decreases its restricted source measure. -/
theorem stieltjes_min_restrict_le {F G : StieltjesFunction ℝ} {T c : ℝ} (hT : 0 ≤ T)
    (he : ∀ x ∈ Icc 0 T, G x = min (F x) c) :
    G.measure.restrict (Ioc 0 T) ≤ F.measure.restrict (Ioc 0 T) := by
  let H : StieltjesFunction ℝ :=
    { toFun := fun x => max (F x - c) 0
      mono' := fun _ _ hxy => max_le_max (sub_le_sub_right (F.mono hxy) c) le_rfl
      right_continuous' := fun x => ((F.right_continuous x).sub_const c).max
        continuousWithinAt_const }
  have heq : F.measure.restrict (Ioc 0 T) =
      (G.measure + H.measure).restrict (Ioc 0 T) := by
    rw [← StieltjesFunction.measure_add]
    apply stieltjes_restrict_Ioc_congr hT
    intro x hx
    rw [StieltjesFunction.add_apply, he x hx]
    change F x = min (F x) c + max (F x - c) 0
    by_cases hc : F x ≤ c
    · rw [min_eq_left hc, max_eq_right (sub_nonpos.mpr hc), add_zero]
    · rw [min_eq_right (not_le.mp hc).le, max_eq_left (sub_nonneg.mpr (not_le.mp hc).le)]
      ring
  rw [heq, Measure.restrict_add]
  apply Measure.le_iff.mpr
  intro B _hB
  rw [Measure.add_apply]
  exact le_add_right le_rfl

/-- Capping a Stieltjes function caps its finite-window cumulative masses, including atoms. -/
theorem stieltjes_min_initial_cdf {F G : StieltjesFunction ℝ} {T c : ℝ}
    (hT : 0 ≤ T) (hc : c ≤ F T)
    (he : ∀ x ∈ Icc 0 T, G x = min (F x) c) (a : ℝ) :
    (G.measure.restrict (Ioc 0 T)) (Iic a) =
      min ((F.measure.restrict (Ioc 0 T)) (Iic a))
        ((F.measure.restrict (Ioc 0 T)) univ - ENNReal.ofReal (F T - c)) := by
  rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply measurableSet_Iic,
    Measure.restrict_apply_univ]
  by_cases ha : a ≤ 0
  · have hz : Iic a ∩ Ioc 0 T = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro x hx
      exact (not_lt_of_ge ha) (hx.2.1.trans_le hx.1)
    simp only [hz, measure_empty, zero_min]
  · have hA : 0 ≤ min a T := le_min (not_le.mp ha).le hT
    have hi : Iic a ∩ Ioc 0 T = Ioc 0 (min a T) := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
      tauto
    rw [hi, StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc,
      StieltjesFunction.measure_Ioc, he (min a T) ⟨hA, min_le_right _ _⟩, he 0 ⟨le_rfl, hT⟩]
    exact ofReal_min_increment (F.mono hA) hc

/-- Capping a Stieltjes function gives the prescribed surviving total mass on a finite window. -/
theorem stieltjes_min_total {F G : StieltjesFunction ℝ} {T c : ℝ}
    (hT : 0 ≤ T) (hc : c ≤ F T)
    (he : ∀ x ∈ Icc 0 T, G x = min (F x) c) :
    (G.measure.restrict (Ioc 0 T)) univ =
      (F.measure.restrict (Ioc 0 T)) univ - ENNReal.ofReal (F T - c) := by
  have hh := stieltjes_min_initial_cdf hT hc he T
  have hI (μ : Measure ℝ) : (μ.restrict (Ioc 0 T)) (Iic T) =
      (μ.restrict (Ioc 0 T)) univ := by
    rw [Measure.restrict_apply measurableSet_Iic, Measure.restrict_apply_univ,
      inter_eq_right.mpr (fun _ hx => hx.2)]
  rw [hI, hI, min_eq_right tsub_le_self] at hh
  exact hh

/-- Translation of a Stieltjes function on a finite window translates its restricted measure. -/
theorem stieltjes_translate_window {F G : StieltjesFunction ℝ} {t r C : ℝ}
    (hr : 0 ≤ r) (he : ∀ x ∈ Icc 0 r, G (t + x) = C + F x) :
    (F.measure.restrict (Ioc 0 r)).map (fun x => t + x) =
      G.measure.restrict (Ioc t (t + r)) := by
  have htrans : Measurable (fun x : ℝ => t + x) := measurable_const.add measurable_id
  let : IsFiniteMeasure (F.measure.restrict (Ioc 0 r)) := ⟨by
    rw [Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc]
    exact ENNReal.ofReal_lt_top⟩
  apply Measure.ext_of_Iic
  intro a
  rw [Measure.map_apply htrans measurableSet_Iic,
    Measure.restrict_apply (htrans measurableSet_Iic), Measure.restrict_apply measurableSet_Iic]
  have hleft : (fun x : ℝ => t + x) ⁻¹' Iic a ∩ Ioc 0 r =
      Ioc 0 (min (a - t) r) := by
    ext x
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioc, le_min_iff]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h2, by linarith only [h1], h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨by linarith only [h2], h1, h3⟩
  have hright : Iic a ∩ Ioc t (t + r) = Ioc t (min a (t + r)) := by
    ext x
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, le_min_iff]
    tauto
  rw [hleft, hright]
  by_cases ha : a ≤ t
  · have h₁ : min (a - t) r ≤ 0 := (min_le_left _ _).trans (sub_nonpos.mpr ha)
    have h₂ : min a (t + r) ≤ t := (min_le_left _ _).trans ha
    simp only [Ioc_eq_empty_of_le h₁, Ioc_eq_empty_of_le h₂, measure_empty]
  · let x := min (a - t) r
    have hx : x ∈ Icc 0 r := ⟨le_min (sub_nonneg.mpr (not_le.mp ha).le) hr,
      min_le_right _ _⟩
    have htx : t + x = min a (t + r) := by
      dsimp [x]
      rw [add_min]
      simp only [add_sub_cancel]
    rw [StieltjesFunction.measure_Ioc, StieltjesFunction.measure_Ioc, ← htx, he x hx,
      show G t = C + F 0 from by simpa only [add_zero] using he 0 ⟨le_rfl, hr⟩]
    congr 1
    ring

end BGW.Probability
