/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionLawBasic

/-! # Uniqueness of measures from positive lifetime tail rectangles

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set MeasurableSpace
open scoped NNReal ENNReal

namespace BGW.StableTrees

private noncomputable def tailLevel (n : ℕ) : Ioi (0 : ℝ) :=
  ⟨1 / (n + 1 : ℝ), by change (0 : ℝ) < 1 / (n + 1 : ℝ); positivity⟩

private theorem tailLevel_cover : (⋃ n, Ioi (tailLevel n)) = univ := by
  ext x
  simp only [mem_iUnion, mem_Ioi, mem_univ, iff_true]
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt x.2
  exact ⟨n, hn⟩

/-- Finite positive tails suffice for uniqueness on lifetime/shape space. -/
theorem measure_eq_of_lifetime_tail_rectangles
    {μ ν : Measure (Ioi (0 : ℝ) × Excursion)}
    (hfin : ∀ t : Ioi (0 : ℝ), μ (Ioi t ×ˢ univ) < ⊤)
    (heq : ∀ (t : Ioi (0 : ℝ)) (A : Set Excursion), MeasurableSet A →
      μ (Ioi t ×ˢ A) = ν (Ioi t ×ˢ A)) : μ = ν := by
  let C : Set (Set (Ioi (0 : ℝ))) := range Ioi
  let D : Set (Set Excursion) := {A | MeasurableSet A}
  have hC : MeasurableSpace.generateFrom C =
      (inferInstance : MeasurableSpace (Ioi (0 : ℝ))) :=
    ((@BorelSpace.measurable_eq (Ioi (0 : ℝ)) _ _ _).trans
      (borel_eq_generateFrom_Ioi _)).symm
  have hspan : IsCountablySpanning C :=
    ⟨fun n => Ioi (tailLevel n), fun n => mem_range_self _, tailLevel_cover⟩
  apply Measure.ext_of_generateFrom_of_iUnion (image2 (· ×ˢ ·) C D)
    (fun n => Ioi (tailLevel n) ×ˢ univ)
    (generateFrom_eq_prod hC generateFrom_measurableSet hspan
      isCountablySpanning_measurableSet).symm
    (isPiSystem_Ioi.prod isPiSystem_measurableSet)
  · rw [← iUnion_prod_const, tailLevel_cover, univ_prod_univ]
  · intro n
    refine mem_image2_of_mem (mem_range_self _) ?_
    change MeasurableSet (univ : Set Excursion)
    exact MeasurableSet.univ
  · intro n
    exact (hfin (tailLevel n)).ne
  · rintro _ ⟨_, ⟨t, rfl⟩, A, hA, rfl⟩
    exact heq t A hA

end BGW.StableTrees
