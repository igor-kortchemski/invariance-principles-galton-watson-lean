module

public import BGWLeaves.ForestLaw.Defs

import BGW.LocallyFinite.Atoms

/-!
# Transport of the finite-tree law to the forest weight
-/

@[expose] public section

namespace BGWLeaves.ForestLaw.Transport

open MeasureTheory ProbabilityTheory BGW
open scoped ENNReal

private theorem forestLeafWeight_eq_tsum_fin (w : ℕ → ℝ≥0∞) (j p n : ℕ) :
    forestLeafWeight w j p n =
      ∑' f : Fin j → PlaneTree,
        if (∑ i, (f i).size = p) ∧ (∑ i, (f i).degreeCount 0 = n) then
          ∏ i, PlaneTree.weight w (f i) else 0 := by
  unfold forestLeafWeight
  rw [← List.equivSigmaTuple.symm.tsum_eq, ENNReal.tsum_sigma', tsum_eq_single j]
  · simp only [List.equivSigmaTuple_symm_apply, List.length_ofFn, true_and,
      PlaneForest.size, forestLeafCount, List.map_ofFn, List.sum_ofFn, List.prod_ofFn]
    apply tsum_congr
    intro f
    rfl
  · intro k hk
    simp [List.equivSigmaTuple_symm_apply, hk]

/-- The law of `j` independent locally finite Galton--Watson trees on the forest event is the
total weight of the corresponding ordered forests. -/
theorem pi_bienaymeLaw_forestEvent (μ : Measure ℕ) [IsProbabilityMeasure μ] (j p n : ℕ) :
    Measure.pi (fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestEvent j p n) =
      forestLeafWeight (fun d => μ {d}) j p n := by
  let toLF : (Fin j → PlaneTree) → (Fin j → LocallyFinite.Tree) :=
    fun ts i => (ts i).toLocallyFinite
  have hinj : Function.Injective toLF := by
    intro ts us h
    funext i
    exact PlaneTree.toLocallyFinite_injective (congrFun h i)
  let good : Set (Fin j → PlaneTree) :=
    {ts | (∑ i, (ts i).size = p) ∧ (∑ i, (ts i).degreeCount 0 = n)}
  have hevent_eq : forestEvent j p n =
      ⋃ ts : good, ({toLF ts.1} : Set (Fin j → LocallyFinite.Tree)) := by
    ext F
    constructor
    · rintro ⟨ts, hp, hn, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨ts, hp, hn⟩, rfl⟩
    · intro hF
      obtain ⟨⟨ts, hp, hn⟩, rfl⟩ := Set.mem_iUnion.mp hF
      exact ⟨ts, hp, hn, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun ts : good =>
      ({toLF ts.1} : Set (Fin j → LocallyFinite.Tree))) := by
    intro ts us hne
    apply Set.disjoint_singleton.mpr
    intro hEq
    apply hne
    apply Subtype.ext
    exact hinj hEq
  calc
    Measure.pi (fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestEvent j p n) =
        ∑' ts : good,
          Measure.pi (fun _ : Fin j => LocallyFinite.bienaymeLaw μ) {toLF ts.1} := by
      rw [hevent_eq, measure_iUnion hdisj (fun _ => measurableSet_singleton _)]
    _ = ∑' ts : good,
          ∏ i, PlaneTree.weight (fun d => μ {d}) (ts.1 i) := by
      refine tsum_congr fun ts => ?_
      rw [Measure.pi_singleton]
      apply Finset.prod_congr rfl
      intro i hi
      exact LocallyFinite.bienaymeLaw_toLocallyFinite μ (ts.1 i)
    _ = ∑' ts : Fin j → PlaneTree,
          if (∑ i, (ts i).size = p) ∧ (∑ i, (ts i).degreeCount 0 = n) then
            ∏ i, PlaneTree.weight (fun d => μ {d}) (ts i) else 0 := by
      rw [tsum_subtype good (fun ts => ∏ i, PlaneTree.weight (fun d => μ {d}) (ts i))]
      refine tsum_congr fun ts => ?_
      by_cases h : (∑ i, (ts i).size = p) ∧ (∑ i, (ts i).degreeCount 0 = n) <;>
        simp [Set.indicator, good, h]
    _ = forestLeafWeight (fun d => μ {d}) j p n :=
      (forestLeafWeight_eq_tsum_fin (fun d => μ {d}) j p n).symm

end BGWLeaves.ForestLaw.Transport

end
