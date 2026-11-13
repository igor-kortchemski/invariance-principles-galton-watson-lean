module

public import BGWLeaves.GeneralA.Marked
public import BGWLeaves.GeneralA.Arithmetic
public import BGW.LocallyFinite.Normalization
public import BGW.LocallyFinite.Atoms
public import BGW.LocallyFinite.SizeConditioning

/-! Transport of arbitrary offspring marks to the locally finite tree law. -/

@[expose] public section

namespace BGWLeaves.GeneralA.MarkedLaw

open MeasureTheory ProbabilityTheory BGW Marked
open scoped ENNReal

noncomputable section

attribute [local instance] Classical.propDecidable

variable (A : Set ℕ)

/-- The event, on locally finite forests of `j` trees, that the total size is `p` and the total number of `A`-marked vertices is `n`. -/
def forestAEvent (j p n : ℕ) : Set (Fin j → LocallyFinite.Tree) :=
  {F | ∃ ts : Fin j → PlaneTree, (∑ i, (ts i).size = p) ∧
    (∑ i, treeACount A (ts i) = n) ∧ F = fun i => (ts i).toLocallyFinite}

theorem zetaA_toLocallyFinite (t : PlaneTree) :
    zetaA A t.toLocallyFinite = (treeACount A t : ℕ∞) := by
  let p : List ℕ → Bool := fun u => decide (t.offspringAt (PlaneTree.positiveAddress u) ∈ A)
  have hmap : t.vertices.map (fun u => t.offspringAt (PlaneTree.positiveAddress u)) = t.degrees := by
    have h := congrArg (List.map (fun o : Option ℕ => o.getD 0))
      (PlaneTree.map_fringe?_vertices_rootDegree t)
    simp only [List.map_map, Function.comp_def, Option.getD_some] at h
    simpa only [PlaneTree.offspringAt_positiveAddress] using h.trans (List.map_id _)
  have hs : {u | LocallyFinite.Present t.toLocallyFinite u ∧ t.toLocallyFinite.val u ∈ A} =
      PlaneTree.positiveAddress '' (↑(t.vertices.filter p).toFinset : Set (List ℕ)) := by
    ext u
    constructor
    · rintro ⟨hu, hA⟩
      obtain ⟨v, rfl⟩ := PlaneTree.exists_positiveAddress_of_present hu
      refine ⟨v, ?_, rfl⟩
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, p, decide_eq_true_eq]
      exact ⟨(PlaneTree.mem_vertices_iff t v).2 ((PlaneTree.present_toLocallyFinite t v).1 hu), hA⟩
    · rintro ⟨v, hv, rfl⟩
      simp only [Finset.mem_coe, List.mem_toFinset, List.mem_filter, p, decide_eq_true_eq] at hv
      exact ⟨(PlaneTree.present_toLocallyFinite t v).2 ((PlaneTree.mem_vertices_iff t v).1 hv.1), hv.2⟩
  have hc : treeACount A t = (t.vertices.filter p).length := by
    rw [treeACount, ← hmap, List.countP_map, List.countP_eq_length_filter]
    rfl
  have hinj : Function.Injective PlaneTree.positiveAddress :=
    List.map_injective_iff.mpr Nat.succ_injective
  rw [zetaA, hs, hinj.encard_image, Set.encard_coe_eq_coe_finsetCard,
    List.toFinset_card_of_nodup ((PlaneTree.nodup_vertices t).filter p), hc]

theorem forestAWeight_eq_tsum_fin (w : ℕ → ℝ≥0∞) (j p n : ℕ) :
    forestAWeight A w j p n =
      ∑' f : Fin j → PlaneTree,
        if (∑ i, (f i).size = p) ∧ (∑ i, treeACount A (f i) = n) then
          ∏ i, PlaneTree.weight w (f i) else 0 := by
  unfold forestAWeight
  rw [← List.equivSigmaTuple.symm.tsum_eq, ENNReal.tsum_sigma', tsum_eq_single j]
  · simp only [List.equivSigmaTuple_symm_apply, List.length_ofFn, true_and,
      PlaneForest.size, forestACount, List.map_ofFn, List.sum_ofFn, List.prod_ofFn]
    apply tsum_congr
    intro f
    rfl
  · intro k hk
    simp [List.equivSigmaTuple_symm_apply, hk]

/-- The law of `j` independent locally finite Galton--Watson trees on the forest event is the
total weight of the corresponding ordered forests. -/
theorem pi_bienaymeLaw_forestAEvent (μ : Measure ℕ) [IsProbabilityMeasure μ] (j p n : ℕ) :
    Measure.pi (fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestAEvent A j p n) =
      forestAWeight A (fun d => μ {d}) j p n := by
  let toLF : (Fin j → PlaneTree) → (Fin j → LocallyFinite.Tree) :=
    fun ts i => (ts i).toLocallyFinite
  have hinj : Function.Injective toLF := by
    intro ts us h
    funext i
    exact PlaneTree.toLocallyFinite_injective (congrFun h i)
  let good : Set (Fin j → PlaneTree) :=
    {ts | (∑ i, (ts i).size = p) ∧ (∑ i, treeACount A (ts i) = n)}
  have hevent_eq : forestAEvent A j p n =
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
    Measure.pi (fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestAEvent A j p n) =
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
          if (∑ i, (ts i).size = p) ∧ (∑ i, treeACount A (ts i) = n) then
            ∏ i, PlaneTree.weight (fun d => μ {d}) (ts i) else 0 := by
      rw [tsum_subtype good (fun ts => ∏ i, PlaneTree.weight (fun d => μ {d}) (ts i))]
      refine tsum_congr fun ts => ?_
      by_cases h : (∑ i, (ts i).size = p) ∧ (∑ i, treeACount A (ts i) = n) <;>
        simp [Set.indicator, good, h]
    _ = forestAWeight A (fun d => μ {d}) j p n :=
      (forestAWeight_eq_tsum_fin A (fun d => μ {d}) j p n).symm


/-- The arithmetic generator contributed by one vertex. -/
noncomputable def arithStep (k : ℕ) : ℤ := if k ∈ A then (k : ℤ) else (k : ℤ) - 1

private theorem sum_arithStep (ds : List ℕ) :
    (ds.map (arithStep A)).sum = (ds.sum : ℤ) - ds.length +
      (ds.countP (fun k => decide (k ∈ A)) : ℤ) := by
  induction ds with
  | nil => simp
  | cons k ds ih =>
    by_cases hk : k ∈ A
    · simp [arithStep, hk, ih]
      ring
    · simp [arithStep, hk, ih]
      ring

/-- Every finite tree of nonzero weight has the corrected arithmetic residue. -/
theorem arithFactor_dvd_treeACount_sub_one {μ : PMF ℕ} (hc : BGW.StableTrees.IsCritical μ)
    (hne : μ 1 ≠ 1) (t : PlaneTree) (ht : PlaneTree.weight (fun k => μ k) t ≠ 0) :
    (arithFactor μ A : ℤ) ∣ (treeACount A t : ℤ) - 1 := by
  have hμ := (PlaneTree.weight_ne_zero_iff (fun k => μ k) t).1 ht
  have hd : ∀ k ∈ t.degrees, (arithFactor μ A : ℤ) ∣ arithStep A k := by
    intro k hk
    apply Arithmetic.arithFactor_dvd hc hne
    refine ⟨k, hμ k hk, ?_⟩
    by_cases hA : k ∈ A
    · exact Or.inl ⟨hA, by simp [arithStep, hA]⟩
    · exact Or.inr ⟨hA, by simp [arithStep, hA]⟩
  have hsum : (arithFactor μ A : ℤ) ∣ (t.degrees.map (arithStep A)).sum := by
    apply List.dvd_sum
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hx
    exact hd k hk
  rw [sum_arithStep, PlaneTree.length_degrees] at hsum
  have he := t.sum_degrees_add_one
  have he' : (t.degrees.sum : ℤ) + 1 = (t.size : ℤ) := by exact_mod_cast he
  change (arithFactor μ A : ℤ) ∣ (t.degrees.countP (fun k => decide (k ∈ A)) : ℤ) - 1
  convert hsum using 1; omega

/-- The finite-tree realization of a fixed A-mark count. -/
def finiteAEvent (n : ℕ) : Set LocallyFinite.Tree :=
  PlaneTree.toLocallyFinite '' {t | treeACount A t = n}

private theorem finiteAEvent_mem (t : PlaneTree) (n : ℕ) :
    t.toLocallyFinite ∈ finiteAEvent A n ↔ treeACount A t = n := by
  constructor
  · rintro ⟨s, hs, he⟩
    exact PlaneTree.toLocallyFinite_injective he ▸ hs
  · intro ht
    exact ⟨t, ht, rfl⟩

/-- The frozen count event, including possible infinite trees, has exactly the
finite-tree weight series in the critical nondegenerate case. -/
theorem bienaymeLaw_zetaA_eq_tsum {μ : PMF ℕ} (hc : BGW.StableTrees.IsCritical μ)
    (hne : μ 1 ≠ 1) (n : ℕ) :
    LocallyFinite.bienaymeLaw μ.toMeasure {T | zetaA A T = (n : ℕ∞)} =
      ∑' t : PlaneTree, if treeACount A t = n then PlaneTree.weight (fun k => μ k) t else 0 := by
  have hmean : (∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure) = 1 := by
    rw [lintegral_countable']
    simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
    exact hc
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hne
  have hae := LocallyFinite.ae_finiteVertices_bienaymeLaw μ.toMeasure hmean.le hne'
  have hevent : {T | zetaA A T = (n : ℕ∞)} =ᵐ[LocallyFinite.bienaymeLaw μ.toMeasure]
      finiteAEvent A n := by
    filter_upwards [hae] with T hT
    obtain ⟨t, rfl⟩ := (LocallyFinite.exists_toLocallyFinite_iff T).2 hT
    apply propext
    simpa only [Set.mem_ofPred_eq, zetaA_toLocallyFinite, ENat.natCast_inj] using
      (finiteAEvent_mem A t n).symm
  rw [measure_congr hevent]
  have hS : MeasurableSet (finiteAEvent A n) :=
    ((Set.to_countable _).image _).measurableSet
  have hsub : finiteAEvent A n ⊆ {T | LocallyFinite.FiniteVertices T} := by
    rintro T ⟨t, -, rfl⟩
    exact t.finiteVertices_toLocallyFinite
  have heq : LocallyFinite.bienaymeLaw μ.toMeasure (finiteAEvent A n) =
      (LocallyFinite.bienaymeLaw μ.toMeasure).restrict {T | LocallyFinite.FiniteVertices T}
        (finiteAEvent A n) := by
    rw [Measure.restrict_apply hS, Set.inter_eq_left.mpr hsub]
  rw [heq, LocallyFinite.bienaymeLaw_restrict_finiteVertices, Measure.sum_apply _ hS]
  apply tsum_congr
  intro t
  rw [Measure.smul_apply, Measure.dirac_apply' _ hS, smul_eq_mul]
  by_cases ht : treeACount A t = n
  · simp [finiteAEvent_mem, ht, PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
  · simp [finiteAEvent_mem, ht, PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]

/-- The vanishing half of the corrected Theorem 8.1(I), with no aperiodicity or
variance assumption. -/
theorem zetaA_eq_zero_of_not_dvd {μ : PMF ℕ} (hc : BGW.StableTrees.IsCritical μ)
    (hne : μ 1 ≠ 1) (n : ℕ) (hn : ¬ ((arithFactor μ A : ℤ) ∣ (n : ℤ) - 1)) :
    LocallyFinite.bienaymeLaw μ.toMeasure {T | zetaA A T = (n : ℕ∞)} = 0 := by
  rw [bienaymeLaw_zetaA_eq_tsum A hc hne, ENNReal.tsum_eq_zero]
  intro t
  by_cases ht : treeACount A t = n
  · rw [ite_eq_left ht]
    by_contra hw
    have hd := arithFactor_dvd_treeACount_sub_one A hc hne t hw
    rw [ht] at hd
    exact hn hd
  · exact ite_eq_right ht

end

end BGWLeaves.GeneralA.MarkedLaw
