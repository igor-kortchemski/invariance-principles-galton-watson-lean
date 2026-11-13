module

public import BGWLeaves.Vervaat.Cyclic
public import BGWLeaves.Vervaat.TimeReversal

/-!
# The discrete Vervaat identity (6.5)

Proofs of the discrete Vervaat identity (6.5): `vervaatAtMark_eq`, `vervaatAtMark_eq_empty`,
`treeWordLeaves_prob`, `bridgeAtMark_eq_iUnion`, `leafCountEvent_eq_iUnion`, `measurableSet_bridgeAtMark`,
`measurableSet_leafCountEvent`, `prop_vervaatdiscrete_joint`, `prop_vervaatdiscrete_total`.  The theorems are
those stated in `BGWLeaves.Vervaat`; they are exported in namespace `BGWLeaves.Vervaat.Discrete` with exactly
the types stated there.
-/

@[expose] public section

namespace BGWLeaves.Vervaat.Discrete

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGWLeaves.Vervaat.Cyclic BGWLeaves.Vervaat.TimeReversal
open scoped ENNReal Topology

local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

/-! ## Leaf counter and mark times -/

theorem walkLeafCount_succ' (ω : ℕ → ℕ) (n : ℕ) :
    walkLeafCount ω (n + 1) = walkLeafCount ω n + if ω n = 0 then 1 else 0 := by
  unfold walkLeafCount
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
  by_cases h : ω n = 0 <;> simp [h]

theorem walkLeafCount_mono' (ω : ℕ → ℕ) {q k : ℕ} (h : q ≤ k) :
    walkLeafCount ω q ≤ walkLeafCount ω k := by
  unfold walkLeafCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

theorem isMarkTime_unique' {n : ℕ} {ω : ℕ → ℕ} {k k' : ℕ} (h : IsMarkTime n ω k)
    (h' : IsMarkTime n ω k') : k = k' := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 := h'.2 k hlt
    have h2 := h.1
    omega
  · have h1 := h.2 k' hlt
    have h2 := h'.1
    omega

/-! ## Atoms of the mark-time events -/

theorem vervaatAtMark_eq {n k : ℕ} (hn : 1 ≤ n) {x : List ℤ} (hx : x ∈ SBar k n) :
    vervaatAtMark n x = {ω | vervaat (walkWord ω k) = x ∧ ω (k - 1) = 0} := by
  have _ := hn
  have hk := one_le_of_SBar hx
  obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
  ext ω
  simp only [vervaatAtMark, Set.mem_ofPred_eq, Nat.add_sub_cancel]
  constructor
  · rintro ⟨k', ⟨h1, h2⟩, h3, h4⟩
    have hk' : k' = k0 + 1 := by
      have := congrArg List.length h4
      rw [length_vervaat, length_walkWord, hx.1] at this
      exact this
    subst hk'
    refine ⟨h4, ?_⟩
    have h5 := h2 k0 (by omega)
    rw [walkLeafCount_succ'] at h1
    by_contra hne
    rw [ite_eq_right hne] at h1
    omega
  · rintro ⟨h4, h5⟩
    have hcount : walkLeafCount ω (k0 + 1) = n := by
      rw [← count_walkWord, ← count_vervaat, h4]
      exact hx.2.2.2.1
    have hsucc := walkLeafCount_succ' ω k0
    rw [ite_eq_left h5] at hsucc
    refine ⟨k0 + 1, ⟨hcount, fun q hq => ?_⟩, ?_, h4⟩
    · have := walkLeafCount_mono' ω (show q ≤ k0 by omega)
      omega
    · rw [← sum_walkWord, ← sum_vervaat, h4]
      exact hx.2.2.1

theorem vervaatAtMark_eq_empty {n : ℕ} {x : List ℤ} (hx : x ∉ SBar x.length n) :
    vervaatAtMark n x = ∅ := by
  ext ω
  simp only [vervaatAtMark, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, ⟨h1, h2⟩, h3, h4⟩
  apply hx
  have hl : x.length = k := by
    have := congrArg List.length h4
    rw [length_vervaat, length_walkWord] at this
    exact this.symm
  have hne : walkWord ω k ≠ [] := by
    intro h
    have hk0 : k = 0 := by
      have := length_walkWord ω k
      rw [h] at this
      simpa using this.symm
    subst hk0
    simp [walkSum] at h3
  have := vervaat_mem_SBar hne (walkWord_ge ω k) (by rw [sum_walkWord]; exact h3)
  rw [h4, length_walkWord, count_walkWord, h1] at this
  rw [hl]
  exact this

open Classical in
theorem treeWordLeaves_prob (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) (x : List ℤ) :
    bienaymeLaw μ (treeWordLeaves n x) =
      if x ∈ SBar x.length n then 𝐏w[μ] {ω | walkWord ω x.length = x} else 0 := by
  by_cases hx : x ∈ SBar x.length n
  · rw [ite_eq_left hx]
    obtain ⟨-, hexc, hcount⟩ := mem_SBar_iff.1 hx
    obtain ⟨t, ht, -⟩ := (PlaneTree.isTreeExcursion_iff_existsUnique x).mp hexc
    have hdeg : t.degreeCount 0 = n := by
      rw [← PlaneTree.wordDegreeCount_increments, ht]
      simpa [wordDegreeCount] using hcount
    have hset : treeWordLeaves n x = {t.toLocallyFinite} := by
      ext T
      constructor
      · rintro ⟨s, rfl, hs1, hs2⟩
        have : s = t := PlaneTree.increments_injective (hs1.trans ht.symm)
        subst this
        rfl
      · rintro rfl
        exact ⟨t, rfl, ht, hdeg⟩
    rw [hset, bienaymeLaw_toLocallyFinite, ← PlaneTree.walkWeight_increments, ht,
      walkWord_atom μ x, ite_eq_left hexc.1]
    rfl
  · rw [ite_eq_right hx]
    have : treeWordLeaves n x = ∅ := by
      ext T
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨s, rfl, h1, h2⟩
      subst h1
      apply hx
      refine mem_SBar_iff.2 ⟨rfl, PlaneTree.isTreeExcursion_increments s, ?_⟩
      have := PlaneTree.wordDegreeCount_increments s 0
      simpa [wordDegreeCount, h2] using this
    rw [this]
    simp

theorem bridgeAtMark_eq_iUnion (n : ℕ) : bridgeAtMark n = ⋃ x : List ℤ, vervaatAtMark n x := by
  ext ω
  simp only [bridgeAtMark, vervaatAtMark, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk, hs⟩
    exact ⟨vervaat (walkWord ω k), k, hk, hs, rfl⟩
  · rintro ⟨x, k, hk, hs, -⟩
    exact ⟨k, hk, hs⟩

theorem leafCountEvent_eq_iUnion (n : ℕ) :
    leafCountEvent n = ⋃ x : List ℤ, treeWordLeaves n x := by
  ext T
  simp only [leafCountEvent, treeWordLeaves, finiteTreeEvent, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨t, rfl, h⟩
    exact ⟨t.increments, t, rfl, rfl, h⟩
  · rintro ⟨x, t, rfl, -, h⟩
    exact ⟨t, rfl, h⟩

/-! ## Measurability -/

theorem measurableSet_bridgeAtMark (n : ℕ) : MeasurableSet (bridgeAtMark n) := by
  have h : bridgeAtMark n = ⋃ k : ℕ, (({ω : ℕ → ℕ | walkLeafCount ω k = n} ∩
      (⋂ q ∈ Finset.range k, {ω : ℕ → ℕ | walkLeafCount ω q < n})) ∩
        {ω : ℕ → ℕ | walkSum ω k = -1}) := by
    ext ω
    simp only [bridgeAtMark, IsMarkTime, Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, Finset.mem_range]
  rw [h]
  refine MeasurableSet.iUnion (fun k => ?_)
  refine MeasurableSet.inter (MeasurableSet.inter ?_ ?_) ?_
  · exact measurable_walkLeafCount k (measurableSet_singleton n)
  · exact Finset.measurableSet_biInter _ (fun q _ =>
      measurable_walkLeafCount q (MeasurableSet.of_discrete (s := Set.Iio n)))
  · exact measurable_walkSum k (measurableSet_singleton (-1))

theorem measurableSet_finiteTreeEvent' (Q : PlaneTree → Prop) :
    MeasurableSet (finiteTreeEvent Q) := by
  have h : finiteTreeEvent Q = PlaneTree.toLocallyFinite '' {t | Q t} := by
    ext T; simp [finiteTreeEvent, Set.mem_image, and_comm]
  rw [h]
  exact (Set.to_countable _ |>.image _).measurableSet

theorem measurableSet_leafCountEvent (n : ℕ) : MeasurableSet (leafCountEvent n) :=
  measurableSet_finiteTreeEvent' _

theorem measurableSet_vervaatAtMark {n : ℕ} (hn : 1 ≤ n) (x : List ℤ) :
    MeasurableSet (vervaatAtMark n x) := by
  by_cases hx : x ∈ SBar x.length n
  · rw [vervaatAtMark_eq hn hx]
    have hk := one_le_of_SBar hx
    have hC : MeasurableSet {ω : ℕ → ℕ | ω (x.length - 1) = 0} :=
      (measurable_pi_apply (x.length - 1)) (measurableSet_singleton 0)
    have : {ω : ℕ → ℕ | vervaat (walkWord ω x.length) = x ∧ ω (x.length - 1) = 0} =
        {ω : ℕ → ℕ | vervaat (walkWord ω x.length) = x ∧ walkSum ω x.length = -1} ∩
          {ω | ω (x.length - 1) = 0} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨⟨h1, ?_⟩, h2⟩
        rw [← sum_walkWord, ← sum_vervaat, h1]
        exact hx.2.2.1
      · rintro ⟨⟨h1, -⟩, h2⟩
        exact ⟨h1, h2⟩
    rw [this]
    exact (measurableSet_F hk x).inter hC
  · rw [vervaatAtMark_eq_empty hx]; exact MeasurableSet.empty

/-! ## 6.5 joint atoms and total mass -/

theorem prop_vervaatdiscrete_joint (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n)
    (x : List ℤ) :
    𝐏w[μ] (vervaatAtMark n x) = (n : ℝ≥0∞) * bienaymeLaw μ (treeWordLeaves n x) := by
  rw [treeWordLeaves_prob]
  by_cases hx : x ∈ SBar x.length n
  · have hcount : n ≤ x.length := by
      have h1 := hx.2.2.2.1
      have h2 := List.count_le_length (a := (-1 : ℤ)) (l := x)
      omega
    have hk := one_le_of_SBar hx
    rw [ite_eq_left hx, vervaatAtMark_eq hn hx, lem_cool_ii μ hn hcount hx,
      vervaat_prob_eq μ hx]
    have hk0 : (x.length : ℝ≥0∞) ≠ 0 := by exact_mod_cast (by omega : x.length ≠ 0)
    have hkT : (x.length : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
    rw [div_eq_mul_inv]
    calc (n : ℝ≥0∞) * (x.length : ℝ≥0∞)⁻¹ * ((x.length : ℝ≥0∞) * 𝐏w[μ] {ω | walkWord ω x.length = x})
        = (n : ℝ≥0∞) * ((x.length : ℝ≥0∞)⁻¹ * x.length) * 𝐏w[μ] {ω | walkWord ω x.length = x} := by
          ring
      _ = _ := by rw [ENNReal.inv_mul_cancel hk0 hkT, mul_one]
  · rw [ite_eq_right hx, vervaatAtMark_eq_empty hx]
    simp

theorem prop_vervaatdiscrete_total (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) :
    𝐏w[μ] (bridgeAtMark n) = (n : ℝ≥0∞) * bienaymeLaw μ (leafCountEvent n) := by
  have hdisj1 : Pairwise (Function.onFun Disjoint (fun x : List ℤ => vervaatAtMark n x)) := by
    intro x y hxy
    refine Set.disjoint_left.mpr (fun ω h1 h2 => hxy ?_)
    obtain ⟨k, hk, -, hx⟩ := h1
    obtain ⟨k', hk', -, hy⟩ := h2
    have := isMarkTime_unique' hk hk'
    subst this
    exact hx.symm.trans hy
  have hdisj2 : Pairwise (Function.onFun Disjoint (fun x : List ℤ => treeWordLeaves n x)) := by
    intro x y hxy
    refine Set.disjoint_left.mpr (fun T h1 h2 => hxy ?_)
    obtain ⟨s, rfl, hs1, -⟩ := h1
    obtain ⟨s', hs', hs1', -⟩ := h2
    have : s' = s := PlaneTree.toLocallyFinite_injective hs'
    subst this
    exact hs1.symm.trans hs1'
  rw [bridgeAtMark_eq_iUnion, measure_iUnion hdisj1 (fun x => measurableSet_vervaatAtMark hn x),
    leafCountEvent_eq_iUnion,
    measure_iUnion hdisj2 (fun x => measurableSet_finiteTreeEvent' _), ← ENNReal.tsum_mul_left]
  exact tsum_congr (fun x => prop_vervaatdiscrete_joint μ hn x)

end BGWLeaves.Vervaat.Discrete
