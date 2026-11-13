module

public import BGWLeaves.Vervaat.Cyclic

/-!
# M5 provider `TimeReversal`

Provider for time reversal of the walk (6.8).  The theorems proved here were the registered holes of
`BGWLeaves.Vervaat`; they are exported in namespace `BGWLeaves.Vervaat.TimeReversal` with exactly the types of the
statements file.
-/

@[expose] public section

namespace BGWLeaves.Vervaat.TimeReversal

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGWLeaves.Vervaat.Cyclic
open scoped ENNReal Topology

local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

/-! ## Measurability -/

theorem measurable_walkPath (m : ℕ) : Measurable (walkPath m) :=
  measurable_pi_iff.mpr (fun i => by unfold walkPath; exact measurable_walkSum i)

theorem measurable_reversedPath (m : ℕ) : Measurable (reversedPath m) :=
  measurable_pi_iff.mpr (fun i => by
    unfold reversedPath
    exact (measurable_walkSum m).sub (measurable_walkSum (m - i)))

theorem measurable_walkLeafCount (m : ℕ) : Measurable fun ω : ℕ → ℕ => walkLeafCount ω m := by
  have : (fun ω : ℕ → ℕ => walkLeafCount ω m) =
      fun ω => ∑ i ∈ Finset.range m, if (ω i : ℤ) - 1 = -1 then 1 else 0 := by
    funext ω
    unfold walkLeafCount
    rw [Finset.card_filter]
  rw [this]
  refine Finset.measurable_sum _ (fun i _ => ?_)
  exact (measurable_from_top (f := fun a : ℕ => if (a : ℤ) - 1 = -1 then 1 else 0)).comp
    (measurable_pi_apply i)

theorem measurableSet_timeReversalEvent (m n : ℕ) : MeasurableSet (timeReversalEvent m n) := by
  have h1 : MeasurableSet {ω : ℕ → ℕ | walkSum ω m = 0} :=
    measurable_walkSum m (measurableSet_singleton 0)
  have h2 : MeasurableSet {ω : ℕ → ℕ | walkLeafCount ω m = n} :=
    measurable_walkLeafCount m (measurableSet_singleton n)
  exact h1.inter h2

/-! ## Word-level facts -/

theorem take_walkWord (ω : ℕ → ℕ) {i k : ℕ} (h : i ≤ k) :
    (walkWord ω k).take i = walkWord ω i := by
  unfold walkWord
  rw [← List.map_take, List.take_range, min_eq_left h]

theorem sum_take_walkWord (ω : ℕ → ℕ) {i k : ℕ} (h : i ≤ k) :
    ((walkWord ω k).take i).sum = walkSum ω i := by
  rw [take_walkWord ω h, sum_walkWord]

theorem count_walkWord (ω : ℕ → ℕ) (m : ℕ) : (walkWord ω m).count (-1) = walkLeafCount ω m := by
  induction m with
  | zero => simp [walkWord, walkLeafCount]
  | succ m ih =>
    have e : walkWord ω (m + 1) = walkWord ω m ++ [(ω m : ℤ) - 1] := by
      unfold walkWord; rw [List.range_succ, List.map_append]; rfl
    rw [e, List.count_append, ih]
    unfold walkLeafCount
    rw [Finset.card_filter, Finset.card_filter, Finset.sum_range_succ]
    by_cases h : (ω m : ℤ) - 1 = -1
    · simp [h]
    · simp [h]

theorem sum_reverse_take {y : List ℤ} {m i : ℕ} (hy : y.length = m) (_hi : i ≤ m) :
    (y.reverse.take i).sum = y.sum - (y.take (m - i)).sum := by
  rw [List.take_reverse, List.sum_reverse, hy]
  have := List.sum_take_add_sum_drop y (m - i)
  omega

theorem walkWord_event_len {m : ℕ} {y : List ℤ} (h : y.length ≠ m) :
    {ω : ℕ → ℕ | walkWord ω m = y} = ∅ := by
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  intro e
  apply h
  rw [← e, length_walkWord]

/-- Permuting the word does not change the probability (exchangeability). -/
theorem prob_perm (μ : Measure ℕ) [IsProbabilityMeasure μ] (m : ℕ) {y z : List ℤ}
    (h : y.Perm z) :
    𝐏w[μ] {ω | walkWord ω m = y} = 𝐏w[μ] {ω | walkWord ω m = z} := by
  by_cases hl : y.length = m
  · have hl' : z.length = m := h.length_eq ▸ hl
    have a1 := walkWord_atom μ y
    rw [hl] at a1
    have a2 := walkWord_atom μ z
    rw [hl'] at a2
    rw [a1, a2]
    have hiff : (∀ a ∈ y, -1 ≤ a) ↔ (∀ a ∈ z, -1 ≤ a) := by
      simp only [h.mem_iff]
    by_cases hg : ∀ a ∈ y, -1 ≤ a
    · rw [ite_eq_left hg, ite_eq_left (hiff.1 hg)]
      exact (h.map _).prod_eq
    · rw [ite_eq_right hg, ite_eq_right (mt hiff.2 hg)]
  · have hl' : z.length ≠ m := fun e => hl (h.length_eq.trans e)
    rw [walkWord_event_len hl, walkWord_event_len hl']

theorem prob_pred (μ : Measure ℕ) [IsProbabilityMeasure μ] (m : ℕ) (Q : List ℤ → Prop) :
    𝐏w[μ] {ω | Q (walkWord ω m)} = ∑' y : List ℤ, 𝐏w[μ] {ω | walkWord ω m = y ∧ Q y} := by
  have h : {ω : ℕ → ℕ | Q (walkWord ω m)} = ⋃ y : List ℤ, {ω | walkWord ω m = y ∧ Q y} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · intro hq; exact ⟨_, rfl, hq⟩
    · rintro ⟨y, rfl, hq⟩; exact hq
  have hmeas : ∀ y, MeasurableSet {ω : ℕ → ℕ | walkWord ω m = y ∧ Q y} := by
    intro y
    by_cases hq : Q y
    · simpa [hq] using measurableSet_walkWord_eq m y
    · simp [hq]
  rw [h]
  exact measure_iUnion (fun y z hyz => Set.disjoint_left.mpr
    (fun ω h1 h2 => hyz (h1.1.symm.trans h2.1))) hmeas

/-- Word-level description of `{W path = p} ∩ {W_m = 0, Λ(m) = n}`. -/
def QA (m n : ℕ) (p : Fin (m + 1) → ℤ) (y : List ℤ) : Prop :=
  y.length = m ∧ (∀ i : Fin (m + 1), (y.take i).sum = p i) ∧ y.sum = 0 ∧ y.count (-1) = n

/-- Word-level description of `{Ŵ path = p} ∩ {W_m = 0, Λ(m) = n}`. -/
def QB (m n : ℕ) (p : Fin (m + 1) → ℤ) (y : List ℤ) : Prop :=
  y.length = m ∧ (∀ i : Fin (m + 1), (y.reverse.take i).sum = p i) ∧ y.sum = 0 ∧
    y.count (-1) = n

theorem QB_iff (m n : ℕ) (p : Fin (m + 1) → ℤ) (y : List ℤ) : QB m n p y ↔ QA m n p y.reverse := by
  unfold QA QB
  simp [List.sum_reverse, List.length_reverse]

theorem eventA_eq (m n : ℕ) (p : Fin (m + 1) → ℤ) :
    {ω : ℕ → ℕ | walkPath m ω = p} ∩ timeReversalEvent m n = {ω | QA m n p (walkWord ω m)} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, timeReversalEvent, QA]
  rw [length_walkWord, sum_walkWord, count_walkWord, funext_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨rfl, fun i => ?_, h2, h3⟩
    rw [sum_take_walkWord ω (by omega)]
    exact h1 i
  · rintro ⟨-, h1, h2, h3⟩
    refine ⟨fun i => ?_, h2, h3⟩
    have := h1 i
    rw [sum_take_walkWord ω (by omega)] at this
    exact this

theorem eventB_eq (m n : ℕ) (p : Fin (m + 1) → ℤ) :
    {ω : ℕ → ℕ | reversedPath m ω = p} ∩ timeReversalEvent m n = {ω | QB m n p (walkWord ω m)} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, timeReversalEvent, QB]
  rw [length_walkWord, sum_walkWord, count_walkWord, funext_iff]
  have key : ∀ i : Fin (m + 1), ((walkWord ω m).reverse.take i).sum = reversedPath m ω i := by
    intro i
    rw [sum_reverse_take (length_walkWord ω m) (by omega), sum_walkWord,
      sum_take_walkWord ω (by omega)]
    rfl
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨rfl, fun i => by rw [key]; exact h1 i, h2, h3⟩
  · rintro ⟨-, h1, h2, h3⟩
    exact ⟨fun i => by rw [← key]; exact h1 i, h2, h3⟩

theorem timeReversal_atom (μ : Measure ℕ) [IsProbabilityMeasure μ] (m n : ℕ) (p : Fin (m + 1) → ℤ) :
    𝐏w[μ] ({ω | walkPath m ω = p} ∩ timeReversalEvent m n) =
      𝐏w[μ] ({ω | reversedPath m ω = p} ∩ timeReversalEvent m n) := by
  rw [eventA_eq, eventB_eq, prob_pred, prob_pred]
  let e : List ℤ ≃ List ℤ := ⟨List.reverse, List.reverse, List.reverse_reverse, List.reverse_reverse⟩
  rw [← e.tsum_eq]
  refine tsum_congr (fun y => ?_)
  change 𝐏w[μ] {ω | walkWord ω m = y.reverse ∧ QA m n p y.reverse} =
    𝐏w[μ] {ω | walkWord ω m = y ∧ QB m n p y}
  by_cases hq : QA m n p y.reverse
  · have hq' : QB m n p y := (QB_iff m n p y).2 hq
    simp only [hq, hq', and_true]
    exact prob_perm μ m (List.reverse_perm y)
  · have hq' : ¬ QB m n p y := fun h => hq ((QB_iff m n p y).1 h)
    simp [hq, hq']


theorem timeReversal_map (μ : Measure ℕ) [IsProbabilityMeasure μ] (m n : ℕ) :
    Measure.map (walkPath m) ((𝐏w[μ])[|timeReversalEvent m n]) =
      Measure.map (reversedPath m) ((𝐏w[μ])[|timeReversalEvent m n]) := by
  refine Measure.ext_of_singleton (fun p => ?_)
  rw [Measure.map_apply (measurable_walkPath m) (measurableSet_singleton p),
    Measure.map_apply (measurable_reversedPath m) (measurableSet_singleton p),
    cond_apply (measurableSet_timeReversalEvent m n), cond_apply (measurableSet_timeReversalEvent m n)]
  have h := timeReversal_atom μ m n p
  show _ * 𝐏w[μ] (timeReversalEvent m n ∩ {ω | walkPath m ω = p}) =
    _ * 𝐏w[μ] (timeReversalEvent m n ∩ {ω | reversedPath m ω = p})
  rw [Set.inter_comm (timeReversalEvent m n), Set.inter_comm (timeReversalEvent m n), h]

end BGWLeaves.Vervaat.TimeReversal
