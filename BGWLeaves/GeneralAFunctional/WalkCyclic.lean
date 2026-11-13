module

public import BGWLeaves.GeneralA.MarkedLaw
public import BGWLeaves.Vervaat.Cyclic
public import BGWLeaves.GeneralAFunctional.Defs

/-! Arbitrary offspring marks in the length-preserving discrete Vervaat identity.
The stopping word ends at a marked letter; its Vervaat transform need not do so.
-/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.WalkCyclic

open MeasureTheory ProbabilityTheory BGW BGW.LocallyFinite
open BGWLeaves.GeneralA.Marked BGWLeaves.GeneralA.MarkedLaw
open BGWLeaves.Vervaat.Cyclic
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

/-- Number of marked offspring among the first `k` revealed vertices. -/
def walkACount (A : Set ℕ) (ω : ℕ → ℕ) (k : ℕ) : ℕ :=
  ((Finset.range k).filter fun i => ω i ∈ A).card

/-- The first time the walk has seen `n` marked offspring. -/
def IsAMarkTime (A : Set ℕ) (n : ℕ) (ω : ℕ → ℕ) (k : ℕ) : Prop :=
  walkACount A ω k = n ∧ ∀ q < k, walkACount A ω q < n

def bridgeAtAMark (A : Set ℕ) (n : ℕ) : Set (ℕ → ℕ) :=
  {ω | ∃ k, IsAMarkTime A n ω k ∧ walkSum ω k = -1}

def vervaatAtAMark (A : Set ℕ) (n : ℕ) (x : List ℤ) : Set (ℕ → ℕ) :=
  {ω | ∃ k, IsAMarkTime A n ω k ∧ walkSum ω k = -1 ∧ vervaat (walkWord ω k) = x}

def treeWordAMarks (A : Set ℕ) (n : ℕ) (x : List ℤ) : Set LocallyFinite.Tree :=
  finiteTreeEvent fun t => t.increments = x ∧ treeACount A t = n

theorem walkACount_succ (A : Set ℕ) (ω : ℕ → ℕ) (k : ℕ) :
    walkACount A ω (k + 1) = walkACount A ω k + if ω k ∈ A then 1 else 0 := by
  simp only [walkACount, Finset.card_filter, Finset.sum_range_succ]

theorem walkACount_mono (A : Set ℕ) (ω : ℕ → ℕ) {q k : ℕ} (h : q ≤ k) :
    walkACount A ω q ≤ walkACount A ω k :=
  Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono h))

theorem IsAMarkTime.unique {A : Set ℕ} {n : ℕ} {ω : ℕ → ℕ} {k k' : ℕ}
    (h : IsAMarkTime A n ω k) (h' : IsAMarkTime A n ω k') : k = k' := by
  rcases lt_trichotomy k k' with hlt | heq | hlt
  · have := h'.2 k hlt; have := h.1; omega
  · exact heq
  · have := h.2 k' hlt; have := h'.1; omega

theorem wordACount_walkWord (A : Set ℕ) (ω : ℕ → ℕ) (k : ℕ) :
    wordACount A (walkWord ω k) = walkACount A ω k := by
  induction k with
  | zero => simp [wordACount, walkWord, walkACount]
  | succ k ih =>
    have e : walkWord ω (k + 1) = walkWord ω k ++ [(ω k : ℤ) - 1] := by
      unfold walkWord; rw [List.range_succ, List.map_append]; rfl
    rw [e, wordACount, List.countP_append, ← wordACount, ih, walkACount_succ]
    simp

theorem wordACount_vervaat (A : Set ℕ) (x : List ℤ) :
    wordACount A (vervaat x) = wordACount A x := by
  rw [vervaat, cyclicShift_eq_rotate, wordACount_rotate]

/-- The last-letter condition characterizes stopping at the nth mark. -/
theorem vervaatAtAMark_eq {A : Set ℕ} {n : ℕ} {x : List ℤ}
    (hx : IsTreeExcursion x) (hcount : wordACount A x = n) :
    vervaatAtAMark A n x =
      {ω | vervaat (walkWord ω x.length) = x ∧ ω (x.length - 1) ∈ A} := by
  have hk : 1 ≤ x.length := by
    have : x ≠ [] := by intro he; simpa [he] using hx.2.1
    exact List.length_pos_iff.mpr this
  obtain ⟨k, he⟩ : ∃ k, x.length = k + 1 := ⟨x.length - 1, by omega⟩
  rw [he]
  ext ω
  simp only [vervaatAtAMark, Set.mem_ofPred_eq, Nat.add_sub_cancel]
  constructor
  · rintro ⟨k', ⟨h1, h2⟩, hs, hv⟩
    have heq : k' = k + 1 := by
      have := congrArg List.length hv
      rw [length_vervaat, length_walkWord, he] at this
      exact this
    subst k'
    refine ⟨hv, ?_⟩
    have := h2 k (by omega)
    rw [walkACount_succ] at h1
    split_ifs at h1 with hmark
    · exact hmark
    · omega
  · rintro ⟨hv, hm⟩
    have hc : walkACount A ω (k + 1) = n := by
      rw [← wordACount_walkWord, ← wordACount_vervaat, hv, hcount]
    have hsucc := walkACount_succ A ω k
    rw [ite_eq_left hm] at hsucc
    refine ⟨k + 1, ⟨hc, fun q hq => ?_⟩, ?_, hv⟩
    · have := walkACount_mono A ω (show q ≤ k by omega)
      omega
    · rw [← sum_walkWord, ← sum_vervaat, hv]
      exact hx.2.1

theorem wordACount_eq_card (A : Set ℕ) (x : List ℤ) :
    wordACount A x = ((Finset.range x.length).filter
      fun m => (x.getD m 0 + 1).toNat ∈ A).card := by
  induction x with
  | nil => simp [wordACount]
  | cons b t ih =>
    rw [Finset.card_filter] at ih ⊢
    rw [wordACount, List.countP_cons, ← wordACount, ih, List.length_cons,
      Finset.sum_range_succ']
    simp

/-- Among all rotations of a word, exactly its marked-letter count end at a mark. -/
theorem sum_rotate_last_mark (A : Set ℕ) (w : ℝ≥0∞) {x : List ℤ} {k : ℕ}
    (hl : x.length = k) (hk : 1 ≤ k) :
    ∑ i ∈ Finset.Icc 1 k,
      (if ((x.rotate (k - i)).getD (k - 1) 0 + 1).toNat ∈ A then w else 0) =
        (wordACount A x : ℝ≥0∞) * w := by
  have hσ : ∀ i ∈ Finset.Icc 1 k,
      (k - 1 + (k - i)) % k = if i = k then k - 1 else k - 1 - i := by
    intro i hi
    rw [Finset.mem_Icc] at hi
    split_ifs with h
    · subst h
      rw [Nat.sub_self, Nat.add_zero, Nat.mod_eq_of_lt (by omega)]
    · have : k - 1 + (k - i) = (k - 1 - i) + k := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
  have step1 : (∑ i ∈ Finset.Icc 1 k,
      (if ((x.rotate (k - i)).getD (k - 1) 0 + 1).toNat ∈ A then w else 0)) =
      ∑ m ∈ Finset.range k, (if (x.getD m 0 + 1).toNat ∈ A then w else 0) := by
    rw [Finset.sum_congr rfl (fun i hi => by rw [getD_rotate_last hl hk, hσ i hi])]
    refine Finset.sum_nbij' (fun i => if i = k then k - 1 else k - 1 - i)
      (fun m => if m = k - 1 then k else k - 1 - m) ?_ ?_ ?_ ?_ ?_
    · intro i hi
      rw [Finset.mem_Icc] at hi
      simp only [Finset.mem_range]
      split_ifs <;> omega
    · intro m hm
      simp only [Finset.mem_range] at hm
      simp only [Finset.mem_Icc]
      split_ifs <;> omega
    · intro i hi
      rw [Finset.mem_Icc] at hi
      split_ifs <;> omega
    · intro m hm
      simp only [Finset.mem_range] at hm
      split_ifs <;> omega
    · intro i hi; rfl
  rw [step1, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, wordACount_eq_card, hl]

theorem cyl_inter_mark (μ : Measure ℕ) [IsProbabilityMeasure μ] (A : Set ℕ)
    {k : ℕ} (hk : 1 ≤ k) (y : List ℤ) :
    𝐏w[μ] ({ω : ℕ → ℕ | walkWord ω k = y} ∩ {ω | ω (k - 1) ∈ A}) =
      if (y.getD (k - 1) 0 + 1).toNat ∈ A then
        𝐏w[μ] {ω | walkWord ω k = y} else 0 := by
  have hletter (ω : ℕ → ℕ) (hy : walkWord ω k = y) :
      (y.getD (k - 1) 0 + 1).toNat = ω (k - 1) := by
    rw [← hy, getD_walkWord hk]
    simp
  by_cases h : (y.getD (k - 1) 0 + 1).toNat ∈ A
  · rw [ite_eq_left h]
    congr 1
    ext ω
    constructor
    · exact fun h => h.1
    · intro hy
      refine ⟨hy, ?_⟩
      change ω (k - 1) ∈ A
      rwa [← hletter ω hy]
  · rw [ite_eq_right h]
    have hempty : {ω : ℕ → ℕ | walkWord ω k = y} ∩
        {ω | ω (k - 1) ∈ A} = ∅ := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨hy, hm⟩
      exact h ((hletter ω hy).symm ▸ hm)
    rw [hempty, measure_empty]

theorem marked_rotation_prob (μ : Measure ℕ) [IsProbabilityMeasure μ] (A : Set ℕ) {k l : ℕ}
    {x : List ℤ} (hx : x ∈ SBar k l) :
    𝐏w[μ] {ω | vervaat (walkWord ω k) = x ∧ ω (k - 1) ∈ A} =
      (wordACount A x : ℝ≥0∞) * 𝐏w[μ] {ω | walkWord ω k = x} := by
  have hk := one_le_of_SBar hx
  have hset : {ω : ℕ → ℕ | vervaat (walkWord ω k) = x ∧ ω (k - 1) ∈ A} =
      ⋃ i ∈ Finset.Icc 1 k, ({ω : ℕ → ℕ | walkWord ω k = x.rotate (k - i)} ∩
        {ω | ω (k - 1) ∈ A}) := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Finset.mem_Icc, exists_prop]
    constructor
    · rintro ⟨h1, h2⟩
      have hW : walkSum ω k = -1 := by
        rw [← sum_walkWord, ← sum_vervaat, h1]; exact hx.2.2.1
      have hi := idx_range hk ω
      refine ⟨vervaatIdx (walkWord ω k), hi, ?_, h2⟩
      have hm : ω ∈ {ω : ℕ → ℕ | vervaatIdx (walkWord ω k) = vervaatIdx (walkWord ω k) ∧
        vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} := ⟨rfl, h1, hW⟩
      exact (E_eq hx hi).subset hm
    · rintro ⟨i, hi, h1, h2⟩
      obtain ⟨-, b, -, -⟩ := good_of_rot hx (j := k - i) (by omega) h1
      exact ⟨b, h2⟩
  have hC : MeasurableSet {ω : ℕ → ℕ | ω (k - 1) ∈ A} :=
    (measurable_pi_apply (k - 1)) (MeasurableSet.of_discrete (s := A))
  rw [hset, measure_biUnion_finset]
  · have hlen : ∀ i ∈ Finset.Icc 1 k, (x.rotate (k - i)).length = k := fun i _ => by
      simp [hx.1]
    rw [Finset.sum_congr rfl (fun i hi => cyl_inter_mark μ A hk (x.rotate (k - i))),
      Finset.sum_congr rfl (fun i hi => by rw [prob_rot μ hx (k - i)]),
      sum_rotate_last_mark A _ hx.1 hk]

  · intro i hi j hj hij
    have hi' := Finset.mem_Icc.1 (Finset.mem_coe.1 hi)
    have hj' := Finset.mem_Icc.1 (Finset.mem_coe.1 hj)
    refine Set.disjoint_left.mpr (fun ω h1 h2 => hij ?_)
    obtain ⟨a, -, -, -⟩ := good_of_rot hx (j := k - i) (by omega) h1.1
    obtain ⟨b, -, -, -⟩ := good_of_rot hx (j := k - j) (by omega) h2.1
    omega
  · exact fun i _ => (measurableSet_walkWord_eq k _).inter hC

theorem treeWordAMarks_prob (μ : Measure ℕ) [IsProbabilityMeasure μ] (A : Set ℕ) (n : ℕ) (x : List ℤ) :
    bienaymeLaw μ (treeWordAMarks A n x) =
      if IsTreeExcursion x ∧ wordACount A x = n then 𝐏w[μ] {ω | walkWord ω x.length = x} else 0 := by
  by_cases hx : IsTreeExcursion x ∧ wordACount A x = n
  · rw [ite_eq_left hx]
    obtain ⟨hexc, hcount⟩ := hx
    obtain ⟨t, ht, -⟩ := (PlaneTree.isTreeExcursion_iff_existsUnique x).mp hexc
    have hdeg : treeACount A t = n := by
      rw [← wordACount_increments, ht]
      exact hcount
    have hset : treeWordAMarks A n x = {t.toLocallyFinite} := by
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
    have : treeWordAMarks A n x = ∅ := by
      ext T
      simp only [Set.mem_empty_iff_false, iff_false]
      rintro ⟨s, rfl, h1, h2⟩
      subst h1
      apply hx
      refine ⟨PlaneTree.isTreeExcursion_increments s, ?_⟩
      rw [wordACount_increments, h2]
    rw [this]
    simp

theorem vervaatAtAMark_eq_empty {A : Set ℕ} {n : ℕ} {x : List ℤ}
    (hx : ¬ (IsTreeExcursion x ∧ wordACount A x = n)) :
    vervaatAtAMark A n x = ∅ := by
  ext ω
  simp only [vervaatAtAMark, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  rintro ⟨k, hk, hs, hv⟩
  have hne : walkWord ω k ≠ [] := by
    intro he
    have hz : k = 0 := by simpa [length_walkWord] using congrArg List.length he
    subst k
    simp [walkSum] at hs
  have hc := vervaat_mem_SBar hne (walkWord_ge ω k) (by rwa [sum_walkWord])
  apply hx
  refine ⟨(mem_SBar_iff.mp hc).2.1 |> (hv ▸ ·), ?_⟩
  rw [← hv, wordACount_vervaat, wordACount_walkWord]
  exact hk.1

theorem measurable_walkACount (A : Set ℕ) (k : ℕ) :
    Measurable fun ω : ℕ → ℕ => walkACount A ω k := by
  unfold walkACount
  simp_rw [Finset.card_filter]
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_from_top (f := fun a : ℕ => if a ∈ A then 1 else 0)).comp
      (measurable_pi_apply i)

theorem measurableSet_bridgeAtAMark (A : Set ℕ) (n : ℕ) :
    MeasurableSet (bridgeAtAMark A n) := by
  have he : bridgeAtAMark A n = ⋃ k : ℕ,
      (({ω : ℕ → ℕ | walkACount A ω k = n} ∩
        (⋂ q ∈ Finset.range k, {ω : ℕ → ℕ | walkACount A ω q < n})) ∩
          {ω : ℕ → ℕ | walkSum ω k = -1}) := by
    ext ω
    simp only [bridgeAtAMark, IsAMarkTime, Set.mem_ofPred_eq, Set.mem_iUnion,
      Set.mem_inter_iff, Set.mem_iInter, Finset.mem_range]
  rw [he]
  refine MeasurableSet.iUnion fun k => (MeasurableSet.inter ?_ ?_).inter ?_
  · exact measurable_walkACount A k (measurableSet_singleton n)
  · exact Finset.measurableSet_biInter _ fun q _ =>
      measurable_walkACount A q (MeasurableSet.of_discrete (s := Set.Iio n))
  · exact measurable_walkSum k (measurableSet_singleton (-1))

theorem measurableSet_vervaatAtAMark (A : Set ℕ) (n : ℕ) (x : List ℤ) :
    MeasurableSet (vervaatAtAMark A n x) := by
  by_cases hx : IsTreeExcursion x ∧ wordACount A x = n
  · rw [vervaatAtAMark_eq hx.1 hx.2]
    have hk : 1 ≤ x.length := by
      have he : x ≠ [] := by intro he; simpa [he] using hx.1.2.1
      exact List.length_pos_iff.mpr he
    have he : {ω : ℕ → ℕ | vervaat (walkWord ω x.length) = x ∧
        ω (x.length - 1) ∈ A} =
        {ω : ℕ → ℕ | vervaat (walkWord ω x.length) = x ∧ walkSum ω x.length = -1} ∩
          {ω | ω (x.length - 1) ∈ A} := by
      ext ω
      constructor
      · rintro ⟨hv, hm⟩
        refine ⟨⟨hv, ?_⟩, hm⟩
        rw [← sum_walkWord, ← sum_vervaat, hv]
        exact hx.1.2.1
      · exact fun h => ⟨h.1.1, h.2⟩
    rw [he]
    exact (measurableSet_F hk x).inter
      ((measurable_pi_apply _ ) (MeasurableSet.of_discrete (s := A)))
  · rw [vervaatAtAMark_eq_empty hx]
    exact MeasurableSet.empty

/-- The unnormalized marked cyclic identity, at a full word atom. The word's
length is retained, including when its last vertex is unmarked. -/
theorem prop_vervaatdiscrete_joint (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (A : Set ℕ) (n : ℕ) (x : List ℤ) :
    𝐏w[μ] (vervaatAtAMark A n x) =
      (n : ℝ≥0∞) * bienaymeLaw μ (treeWordAMarks A n x) := by
  rw [treeWordAMarks_prob]
  by_cases hx : IsTreeExcursion x ∧ wordACount A x = n
  · rw [ite_eq_left hx, vervaatAtAMark_eq hx.1 hx.2,
      marked_rotation_prob μ A (mem_SBar_iff.mpr ⟨rfl, hx.1, rfl⟩), hx.2]
  · rw [ite_eq_right hx, vervaatAtAMark_eq_empty hx]
    simp


theorem bridgeAtAMark_eq_iUnion (A : Set ℕ) (n : ℕ) :
    bridgeAtAMark A n = ⋃ x : List ℤ, vervaatAtAMark A n x := by
  ext ω
  simp only [bridgeAtAMark, vervaatAtAMark, Set.mem_ofPred_eq, Set.mem_iUnion]
  constructor
  · rintro ⟨k, hk, hs⟩
    exact ⟨vervaat (walkWord ω k), k, hk, hs, rfl⟩
  · rintro ⟨x, k, hk, hs, -⟩
    exact ⟨k, hk, hs⟩

theorem zetaAEvent_eq_iUnion (A : Set ℕ) (n : ℕ) :
    {T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} =
      ⋃ x : List ℤ, treeWordAMarks A n x := by
  ext T
  constructor
  · rintro ⟨hT, hn⟩
    obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff T).mpr hT
    rw [zetaA_toLocallyFinite, ENat.natCast_inj] at hn
    exact Set.mem_iUnion.mpr ⟨t.increments, t, rfl, rfl, hn⟩
  · intro hT
    obtain ⟨x, t, rfl, hx, hn⟩ := Set.mem_iUnion.mp hT
    exact ⟨t.finiteVertices_toLocallyFinite, by rw [zetaA_toLocallyFinite, hn]⟩

theorem measurableSet_treeWordAMarks (A : Set ℕ) (n : ℕ) (x : List ℤ) :
    MeasurableSet (treeWordAMarks A n x) := by
  have he : treeWordAMarks A n x = PlaneTree.toLocallyFinite ''
      {t | t.increments = x ∧ treeACount A t = n} := by
    ext T
    simp [treeWordAMarks, finiteTreeEvent, and_comm]
  rw [he]
  exact ((Set.to_countable _).image _).measurableSet

theorem prop_vervaatdiscrete_total (μ : Measure ℕ) [IsProbabilityMeasure μ] (A : Set ℕ) (n : ℕ) :
    𝐏w[μ] (bridgeAtAMark A n) = (n : ℝ≥0∞) * bienaymeLaw μ ({T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}) := by
  have hdisj1 : Pairwise (Function.onFun Disjoint (fun x : List ℤ => vervaatAtAMark A n x)) := by
    intro x y hxy
    refine Set.disjoint_left.mpr (fun ω h1 h2 => hxy ?_)
    obtain ⟨k, hk, -, hx⟩ := h1
    obtain ⟨k', hk', -, hy⟩ := h2
    have := IsAMarkTime.unique hk hk'
    subst this
    exact hx.symm.trans hy
  have hdisj2 : Pairwise (Function.onFun Disjoint (fun x : List ℤ => treeWordAMarks A n x)) := by
    intro x y hxy
    refine Set.disjoint_left.mpr (fun T h1 h2 => hxy ?_)
    obtain ⟨s, rfl, hs1, -⟩ := h1
    obtain ⟨s', hs', hs1', -⟩ := h2
    have : s' = s := PlaneTree.toLocallyFinite_injective hs'
    subst this
    exact hs1.symm.trans hs1'
  rw [bridgeAtAMark_eq_iUnion, measure_iUnion hdisj1 (fun x => measurableSet_vervaatAtAMark A n x),
    zetaAEvent_eq_iUnion,
    measure_iUnion hdisj2 (fun x => measurableSet_treeWordAMarks A n _), ← ENNReal.tsum_mul_left]
  exact tsum_congr (fun x => prop_vervaatdiscrete_joint μ A n x)

theorem prop_vervaatdiscrete (μ : PMF ℕ) (A : Set ℕ) {n : ℕ} (hn : 1 ≤ n)
    (x : List ℤ) :
    ((𝐏w[μ.toMeasure])[|bridgeAtAMark A n]) (vervaatAtAMark A n x) =
      ((bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}]) (treeWordAMarks A n x) := by
  have hA : vervaatAtAMark A n x ⊆ bridgeAtAMark A n := fun ω ⟨k, hk, hs, _⟩ => ⟨k, hk, hs⟩
  have hB : treeWordAMarks A n x ⊆ {T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} := by
    rintro T ⟨t, rfl, hx, hn⟩
    exact ⟨t.finiteVertices_toLocallyFinite, by rw [zetaA_toLocallyFinite, hn]⟩
  rw [cond_apply (measurableSet_bridgeAtAMark A n), cond_apply (measurableSet_zetaAEvent A n),
    Set.inter_eq_right.2 hA, Set.inter_eq_right.2 hB, prop_vervaatdiscrete_joint μ.toMeasure A n x,
    prop_vervaatdiscrete_total μ.toMeasure A n]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnT : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hinv : (n : ℝ≥0∞)⁻¹ * n = 1 := ENNReal.inv_mul_cancel hn0 hnT
  rw [ENNReal.mul_inv (Or.inl hn0) (Or.inl hnT)]
  calc (n : ℝ≥0∞)⁻¹ * (bienaymeLaw μ.toMeasure ({T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}))⁻¹ * (n * bienaymeLaw μ.toMeasure (treeWordAMarks A n x))
      = ((n : ℝ≥0∞)⁻¹ * n) * ((bienaymeLaw μ.toMeasure ({T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)}))⁻¹ *
          bienaymeLaw μ.toMeasure (treeWordAMarks A n x)) := by ring
    _ = _ := by rw [hinv, one_mul]

end
end BGWLeaves.GeneralAFunctional.WalkCyclic
