/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.MeasurableCylinders
public import BGW.Skorokhod.Restrict
public import BGW.Skorokhod.Scaling
public import BGW.Skorokhod.Continuous
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# Measurability of path maps

Restriction and fixed time–space scaling are measurable because the Borel σ-algebra is generated
by path evaluations.
-/

@[expose] public section

open Set MeasureTheory

namespace BGW.Skorokhod

/-- Continuous paths are Borel-measurably embedded in Skorokhod space. -/
theorem measurable_ofContinuous {T : ℝ} :
    Measurable (ofContinuous : C(Set.Icc (0 : ℝ) T, ℝ) → D T ℝ) := by
  exact lipschitzWith_one_ofContinuous.continuous.measurable

/-- Restriction of a Skorokhod path is Borel measurable. -/
theorem measurable_restrict {T a : ℝ} (haT : a ≤ T) :
    Measurable (restrict (E := ℝ) haT) := by
  by_cases ha : 0 ≤ a
  · have hEval (t : Set.Icc (0 : ℝ) a) :
        Measurable (fun f : D T ℝ => (restrict haT f) t) := by
      simpa only [restrict, coe_mk] using
        (measurable_eval (t := ⟨(t : ℝ), t.property.1, t.property.2.trans haT⟩))
    rw [measurable_iff_comap_le]
    change MeasurableSpace.comap (restrict haT)
        (inferInstance : MeasurableSpace (D a ℝ)) ≤
      (inferInstance : MeasurableSpace (D T ℝ))
    rw [measurableSpace_eq_iSup_comap_eval (T := a) (E := ℝ) (S := Set.univ)
      dense_univ ha (by simp)]
    simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp,
      Function.comp_def]
    intro t ht
    exact (hEval t).comap_le
  · have ha' : a < 0 := lt_of_not_ge ha
    have hsub : Subsingleton (D a ℝ) := by
      refine ⟨fun f g => ext fun t => ?_⟩
      have : False := not_le_of_gt ha' (le_trans t.property.1 t.property.2)
      exact this.elim
    let c : D a ℝ := ⟨fun t => (False.elim (not_le_of_gt ha' (le_trans t.property.1 t.property.2))),
      by
        constructor
        · intro t
          exact (not_le_of_gt ha' (le_trans t.property.1 t.property.2)).elim
        · intro t
          exact (not_le_of_gt ha' (le_trans t.property.1 t.property.2)).elim⟩
    have hconst : (restrict (E := ℝ) haT : D T ℝ → D a ℝ) = fun _ => c := by
      funext f
      exact hsub.elim _ _
    rw [hconst]
    exact measurable_const

/-- Fixed horizon-to-horizon time–space scaling is Borel measurable. -/
theorem measurable_timeSpaceScale_fixed {T : ℝ} (hT : 0 < T) {c : ℝ} (hc : 0 < c) (k : ℝ) :
    Measurable (fun f : D (c * T) ℝ =>
      timeSpaceScale T (mul_pos hc hT).le
        (f, k, (⟨c, Set.mem_Ioi.mpr hc⟩ : Set.Ioi (0 : ℝ)))) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap
      (fun f : D (c * T) ℝ => timeSpaceScale T (mul_pos hc hT).le
        (f, k, (⟨c, Set.mem_Ioi.mpr hc⟩ : Set.Ioi (0 : ℝ))))
      (inferInstance : MeasurableSpace (D T ℝ)) ≤
    (inferInstance : MeasurableSpace (D (c * T) ℝ))
  rw [measurableSpace_eq_iSup_comap_eval (T := T) (E := ℝ) (S := Set.univ)
    dense_univ hT.le (by simp)]
  simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp,
    Function.comp_def]
  intro t
  have heval : Measurable (fun f : D (c * T) ℝ =>
      f ⟨min (c * (t : ℝ)) (c * T),
        le_min (mul_nonneg hc.le t.property.1) (mul_nonneg hc.le hT.le),
        min_le_right _ _⟩) := measurable_eval _
  have hmul : Measurable (fun f : D (c * T) ℝ =>
      k * f ⟨min (c * (t : ℝ)) (c * T),
        le_min (mul_nonneg hc.le t.property.1) (mul_nonneg hc.le hT.le),
        min_le_right _ _⟩) := measurable_const.mul heval
  simpa [timeSpaceScale] using hmul.comap_le

end BGW.Skorokhod
