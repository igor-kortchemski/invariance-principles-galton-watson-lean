module

public import BGWLeaves.ForestLaw
public import BGWLeaves.Passage.Defs
public import BGWLeaves.MarkedForest

@[expose] public section

namespace BGWLeaves.Passage.Kemperman

open BGWLeaves
open MeasureTheory ProbabilityTheory BGW
open scoped ENNReal

private theorem forestWeight_eq_tsum_fin (w : ℕ → ℝ≥0∞) (j p : ℕ) :
    BGW.forestWeight w j p =
      ∑' f : Fin j → PlaneTree,
        if (∑ i, (f i).size = p) then ∏ i, PlaneTree.weight w (f i) else 0 := by
  unfold BGW.forestWeight
  rw [← List.equivSigmaTuple.symm.tsum_eq, ENNReal.tsum_sigma', tsum_eq_single j]
  · simp only [List.equivSigmaTuple_symm_apply, List.length_ofFn, true_and,
      PlaneForest.size, List.map_ofFn, List.sum_ofFn, List.prod_ofFn]
    apply tsum_congr
    intro f
    rfl
  · intro k hk
    simp [List.equivSigmaTuple_symm_apply, hk]

private theorem pi_bienaymeLaw_forestSizeEvent (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (j p : ℕ) :
    Measure.pi (fun _ : Fin j => LocallyFinite.bienaymeLaw μ)
        (BGWLeaves.forestSizeEvent j p) =
      BGW.forestWeight (fun d => μ {d}) j p := by
  let toLF : (Fin j → PlaneTree) → (Fin j → LocallyFinite.Tree) :=
    fun ts i => (ts i).toLocallyFinite
  have hinj : Function.Injective toLF := by
    intro ts us h
    funext i
    exact PlaneTree.toLocallyFinite_injective (congrFun h i)
  let good : Set (Fin j → PlaneTree) := {ts | ∑ i, (ts i).size = p}
  have hevent_eq : BGWLeaves.forestSizeEvent j p =
      ⋃ ts : good, ({toLF ts.1} : Set (Fin j → LocallyFinite.Tree)) := by
    ext F
    constructor
    · rintro ⟨ts, hp, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨ts, hp⟩, rfl⟩
    · intro hF
      obtain ⟨⟨ts, hp⟩, rfl⟩ := Set.mem_iUnion.mp hF
      exact ⟨ts, hp, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun ts : good =>
      ({toLF ts.1} : Set (Fin j → LocallyFinite.Tree))) := by
    intro ts us hne
    apply Set.disjoint_singleton.mpr
    intro hEq
    apply hne
    apply Subtype.ext
    exact hinj hEq
  calc
    Measure.pi (fun _ : Fin j => LocallyFinite.bienaymeLaw μ)
        (BGWLeaves.forestSizeEvent j p) =
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
          if (∑ i, (ts i).size = p) then
            ∏ i, PlaneTree.weight (fun d => μ {d}) (ts i) else 0 := by
      rw [tsum_subtype good (fun ts => ∏ i, PlaneTree.weight (fun d => μ {d}) (ts i))]
      refine tsum_congr fun ts => ?_
      by_cases h : (∑ i, (ts i).size = p)
      · simp [Set.indicator, good, h]
      · simp [Set.indicator, good, h]
    _ = BGW.forestWeight (fun d => μ {d}) j p :=
      (forestWeight_eq_tsum_fin (fun d => μ {d}) j p).symm

/-- Marked Kemperman identity for the total progeny and leaf count of a forest. -/
theorem kemperman_marked (μ : Measure ℕ) [IsProbabilityMeasure μ] {j p n : ℕ}
    (hj : 1 ≤ j) (hp : 1 ≤ p) :
    (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestEvent j p n) =
      ((j : ℝ≥0∞) / p) *
        Measure.pi (fun _ : Fin p => μ) (leafMarkedForestBridges j p n) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpT : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hbridge :
      ∑' ω : Fin p → ℕ,
        (leafMarkedForestBridges j p n).indicator (fun ω => ∏ i, μ {ω i}) ω =
          Measure.pi (fun _ : Fin p => μ) (leafMarkedForestBridges j p n) :=
    (BGW.pi_eq_tsum_indicator μ (leafMarkedForestBridges j p n)).symm
  have hkey := BGWLeaves.natCast_mul_forestLeafWeight (fun d => μ {d}) hj p n
  rw [hbridge] at hkey
  calc
    (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ)
        (BGWLeaves.forestEvent j p n) =
        forestLeafWeight (fun d => μ {d}) j p n :=
      BGWLeaves.pi_bienaymeLaw_forestEvent μ j p n
    _ = (p : ℝ≥0∞)⁻¹ *
          ((p : ℝ≥0∞) * forestLeafWeight (fun d => μ {d}) j p n) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hpT, one_mul]
    _ = (p : ℝ≥0∞)⁻¹ *
          ((j : ℝ≥0∞) * Measure.pi (fun _ : Fin p => μ)
            (leafMarkedForestBridges j p n)) := by rw [hkey]
    _ = ((j : ℝ≥0∞) / p) *
          Measure.pi (fun _ : Fin p => μ) (leafMarkedForestBridges j p n) := by
      rw [div_eq_mul_inv]
      ring

/-- Unmarked Kemperman identity for the total progeny of a forest. -/
theorem kemperman_unmarked (μ : Measure ℕ) [IsProbabilityMeasure μ] {j p : ℕ}
    (hj : 1 ≤ j) (hp : 1 ≤ p) :
    (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ)
        (BGWLeaves.forestSizeEvent j p) =
      ((j : ℝ≥0∞) / p) * Measure.pi (fun _ : Fin p => μ) (countForestBridges j p) := by
  have hp0 : (p : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpT : (p : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top p
  have hkey := BGW.natCast_mul_forestWeight_eq_pi μ hj p
  calc
    (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ)
        (BGWLeaves.forestSizeEvent j p) =
        BGW.forestWeight (fun d => μ {d}) j p :=
      pi_bienaymeLaw_forestSizeEvent μ j p
    _ = (p : ℝ≥0∞)⁻¹ *
          ((p : ℝ≥0∞) * BGW.forestWeight (fun d => μ {d}) j p) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hp0 hpT, one_mul]
    _ = (p : ℝ≥0∞)⁻¹ *
          ((j : ℝ≥0∞) * Measure.pi (fun _ : Fin p => μ) (countForestBridges j p)) := by
      rw [hkey]
    _ = ((j : ℝ≥0∞) / p) *
          Measure.pi (fun _ : Fin p => μ) (countForestBridges j p) := by
      rw [div_eq_mul_inv]
      ring

/-- One-tree form of Proposition 1.6, the formula `eq:f` in the introduction. -/
theorem eq_f (μ : Measure ℕ) [IsProbabilityMeasure μ] (h0 : μ {0} ≠ 1) {p n : ℕ}
    (hp : 1 ≤ p) (hn : n ≤ p) :
    LocallyFinite.bienaymeLaw μ (BGWLeaves.treeSizeLeavesEvent p n) =
      ((1 : ℝ≥0∞) / p) * ((p.choose n : ℝ≥0∞) * μ {0} ^ n * (1 - μ {0}) ^ (p - n)) *
        Measure.pi (fun _ : Fin (p - n) => eta μ) {ω | ∑ i, ω i + 1 = n} := by
  have hevent : BGWLeaves.forestEvent 1 p n =
      (MeasurableEquiv.funUnique (Fin 1) LocallyFinite.Tree) ⁻¹'
        BGWLeaves.treeSizeLeavesEvent p n := by
    ext F
    simp only [forestEvent, treeSizeLeavesEvent, Set.mem_ofPred_eq, Set.mem_preimage]
    constructor
    · rintro ⟨ts, hpF, hnF, hF⟩
      refine ⟨ts 0, ?_, ?_, ?_⟩
      · simpa only [Fin.sum_univ_one] using hpF
      · simpa only [Fin.sum_univ_one] using hnF
      · simpa [MeasurableEquiv.funUnique] using congrFun hF 0
    · rintro ⟨t, ht, hnT, hT⟩
      refine ⟨fun _ : Fin 1 => t, ?_, ?_, ?_⟩
      · simpa only [Fin.sum_univ_one] using ht
      · simpa only [Fin.sum_univ_one] using hnT
      · have h0 : F 0 = t.toLocallyFinite := by
          simpa [MeasurableEquiv.funUnique] using hT
        funext i
        have hi : i = 0 := Subsingleton.elim _ _
        simpa [hi] using h0
  have hmeasure :
      (Measure.pi fun _ : Fin 1 => LocallyFinite.bienaymeLaw μ) (forestEvent 1 p n) =
        LocallyFinite.bienaymeLaw μ (treeSizeLeavesEvent p n) := by
    rw [hevent]
    calc
      (Measure.pi fun _ : Fin 1 => LocallyFinite.bienaymeLaw μ)
          ((MeasurableEquiv.funUnique (Fin 1) LocallyFinite.Tree) ⁻¹'
            BGWLeaves.treeSizeLeavesEvent p n) =
          Measure.map (MeasurableEquiv.funUnique (Fin 1) LocallyFinite.Tree)
            (Measure.pi fun _ : Fin 1 => LocallyFinite.bienaymeLaw μ)
            (BGWLeaves.treeSizeLeavesEvent p n) :=
              (MeasurableEquiv.funUnique (Fin 1) LocallyFinite.Tree).map_apply _ |>.symm
      _ = LocallyFinite.bienaymeLaw μ (BGWLeaves.treeSizeLeavesEvent p n) := by
        exact congrArg (fun ν : Measure LocallyFinite.Tree =>
          ν (BGWLeaves.treeSizeLeavesEvent p n))
            (MeasureTheory.measurePreserving_funUnique
              (LocallyFinite.bienaymeLaw μ) (Fin 1)).map_eq
  rw [← hmeasure]
  simpa using (BGWLeaves.prop_K μ h0 (j := 1) (by omega) hp hn)

end BGWLeaves.Passage.Kemperman

end
