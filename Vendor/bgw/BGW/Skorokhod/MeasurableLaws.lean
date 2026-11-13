/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.MeasurableCylinders
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Constructions.Projective

/-!
# Determination of Skorokhod laws by finite-dimensional distributions

Cylinder generation and uniqueness of projective limits identify path laws.
-/

@[expose] public section

namespace BGW.Skorokhod

open Set MeasureTheory

variable {T : ℝ} {E : Type*}

/-- Laws on `D` are determined by their finite-dimensional distributions at times of a dense
set containing the terminal time (C12(1)). -/
theorem ext_of_finiteDimensional [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    [MeasurableSpace E] [BorelSpace E] {P Q : ProbabilityMeasure (D T E)}
    {S : Set (Set.Icc (0 : ℝ) T)} (hS : Dense S) (hT0 : 0 ≤ T)
    (hTS : (⟨T, hT0, le_rfl⟩ : Set.Icc (0 : ℝ) T) ∈ S)
    (h : ∀ s : Finset (Set.Icc (0 : ℝ) T), (↑s : Set (Set.Icc (0 : ℝ) T)) ⊆ S →
      P.map (fun f : D T E => fun t : s => f t) = Q.map (fun f : D T E => fun t : s => f t)) :
    P = Q := by
  classical
  let ev : D T E → S → E := fun f t => f t
  have hev : Measurable ev := Measurable.of_eval fun t => measurable_eval t.val
  let F (s : Finset S) : D T E → s → E := fun f t => f t.val.val
  have hfin (s : Finset S) : (P : Measure (D T E)).map (F s) =
      (Q : Measure (D T E)).map (F s) := by
    let u := s.image Subtype.val
    have hu : (↑u : Set (Icc (0 : ℝ) T)) ⊆ S := by
      intro t ht
      obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp ht
      exact q.property
    let k : (u → E) → s → E := fun z t => z ⟨t.val.val,
      Finset.mem_image.mpr ⟨t.val, t.property, rfl⟩⟩
    have hk : Measurable k := Measurable.of_eval fun _ => measurable_pi_apply _
    have hU : Measurable (fun f : D T E => fun t : u => f t) :=
      Measurable.of_eval fun t => measurable_eval t.val
    have hh := congrArg (fun R : ProbabilityMeasure (u → E) => (R : Measure (u → E))) (h u hu)
    have hh' := congrArg (Measure.map k) hh
    simpa only [ProbabilityMeasure.toMeasure_map, Measure.map_map hk hU,
      Function.comp_def] using hh'
  let R (s : Finset S) := (P : Measure (D T E)).map (F s)
  let (s : Finset S) : IsFiniteMeasure (R s) := inferInstance
  have hmaps : (P : Measure (D T E)).map ev = (Q : Measure (D T E)).map ev := by
    apply IsProjectiveLimit.unique (P := R)
    · intro s
      rw [Measure.map_map (Finset.measurable_restrict s) hev]
      rfl
    · intro s
      rw [Measure.map_map (Finset.measurable_restrict s) hev]
      exact (hfin s).symm
  have hcomap : MeasurableSpace.comap ev (inferInstance : MeasurableSpace (S → E)) =
      (inferInstance : MeasurableSpace (D T E)) := by
    rw [measurableSpace_eq_iSup_comap_eval hS hT0 hTS]
    simp only [MeasurableSpace.pi, MeasurableSpace.comap_iSup,
      MeasurableSpace.comap_comp, ev, Function.comp_def, iSup_subtype]
  apply Subtype.ext
  apply Measure.ext
  intro A hA
  have hA' : MeasurableSet[MeasurableSpace.comap ev
      (inferInstance : MeasurableSpace (S → E))] A := by
    rw [hcomap]
    exact hA
  obtain ⟨B, hB, rfl⟩ := hA'
  rw [← Measure.map_apply hev hB, ← Measure.map_apply hev hB]
  exact congrArg (fun μ : Measure (S → E) => μ B) hmaps

end BGW.Skorokhod
