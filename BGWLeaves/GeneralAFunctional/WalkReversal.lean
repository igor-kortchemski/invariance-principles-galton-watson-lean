module

public import BGWLeaves.GeneralAFunctional.WalkCyclic
public import BGWLeaves.Vervaat.TimeReversal

/-! Reversal of an arbitrary-mark prefix with prescribed count and endpoint. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.WalkReversal
open MeasureTheory ProbabilityTheory BGW BGW.StableTrees
open BGWLeaves.GeneralA.Marked BGWLeaves.GeneralAFunctional.WalkCyclic
open BGWLeaves.Vervaat.Cyclic BGWLeaves.Vervaat.TimeReversal
open scoped ENNReal
local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

/-- The preterminal word has a prescribed signed sum and mark count. -/
def aReversalEvent (A : Set ℕ) (s : ℤ) (m n : ℕ) : Set (ℕ → ℕ) :=
  {ω | walkSum ω m = s ∧ walkACount A ω m = n}

theorem measurableSet_aReversalEvent (A : Set ℕ) (s : ℤ) (m n : ℕ) :
    MeasurableSet (aReversalEvent A s m n) :=
  (measurable_walkSum m (measurableSet_singleton _)).inter
    (measurable_walkACount A m (measurableSet_singleton _))

/-- Word-level description of `{W path = p} ∩ {W_m = 0, Λ(m) = n}`. -/
def QA (A : Set ℕ) (s : ℤ) (m n : ℕ) (p : Fin (m + 1) → ℤ) (y : List ℤ) : Prop :=
  y.length = m ∧ (∀ i : Fin (m + 1), (y.take i).sum = p i) ∧ y.sum = s ∧ wordACount A y = n

/-- Word-level description of `{Ŵ path = p} ∩ {W_m = 0, Λ(m) = n}`. -/
def QB (A : Set ℕ) (s : ℤ) (m n : ℕ) (p : Fin (m + 1) → ℤ) (y : List ℤ) : Prop :=
  y.length = m ∧ (∀ i : Fin (m + 1), (y.reverse.take i).sum = p i) ∧ y.sum = s ∧
    wordACount A y = n

theorem QB_iff (A : Set ℕ) (s : ℤ) (m n : ℕ) (p : Fin (m + 1) → ℤ) (y : List ℤ) : QB A s m n p y ↔ QA A s m n p y.reverse := by
  unfold QA QB
  simp [List.sum_reverse, List.length_reverse, wordACount, List.countP_reverse]

theorem eventA_eq (A : Set ℕ) (s : ℤ) (m n : ℕ) (p : Fin (m + 1) → ℤ) :
    {ω : ℕ → ℕ | walkPath m ω = p} ∩ aReversalEvent A s m n = {ω | QA A s m n p (walkWord ω m)} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, aReversalEvent, QA]
  rw [length_walkWord, sum_walkWord, wordACount_walkWord, funext_iff]
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

theorem eventB_eq (A : Set ℕ) (s : ℤ) (m n : ℕ) (p : Fin (m + 1) → ℤ) :
    {ω : ℕ → ℕ | reversedPath m ω = p} ∩ aReversalEvent A s m n = {ω | QB A s m n p (walkWord ω m)} := by
  ext ω
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, aReversalEvent, QB]
  rw [length_walkWord, sum_walkWord, wordACount_walkWord, funext_iff]
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

theorem timeReversal_atom (μ : Measure ℕ) [IsProbabilityMeasure μ] (A : Set ℕ) (s : ℤ) (m n : ℕ) (p : Fin (m + 1) → ℤ) :
    𝐏w[μ] ({ω | walkPath m ω = p} ∩ aReversalEvent A s m n) =
      𝐏w[μ] ({ω | reversedPath m ω = p} ∩ aReversalEvent A s m n) := by
  rw [eventA_eq, eventB_eq, prob_pred, prob_pred]
  let e : List ℤ ≃ List ℤ := ⟨List.reverse, List.reverse, List.reverse_reverse, List.reverse_reverse⟩
  rw [← e.tsum_eq]
  refine tsum_congr (fun y => ?_)
  change 𝐏w[μ] {ω | walkWord ω m = y.reverse ∧ QA A s m n p y.reverse} =
    𝐏w[μ] {ω | walkWord ω m = y ∧ QB A s m n p y}
  by_cases hq : QA A s m n p y.reverse
  · have hq' : QB A s m n p y := (QB_iff A s m n p y).2 hq
    simp only [hq, hq', and_true]
    exact prob_perm μ m (List.reverse_perm y)
  · have hq' : ¬ QB A s m n p y := fun h => hq ((QB_iff A s m n p y).1 h)
    simp [hq, hq']


theorem timeReversal_map (μ : Measure ℕ) [IsProbabilityMeasure μ] (A : Set ℕ) (s : ℤ) (m n : ℕ) :
    Measure.map (walkPath m) ((𝐏w[μ])[|aReversalEvent A s m n]) =
      Measure.map (reversedPath m) ((𝐏w[μ])[|aReversalEvent A s m n]) := by
  refine Measure.ext_of_singleton (fun p => ?_)
  rw [Measure.map_apply (measurable_walkPath m) (measurableSet_singleton p),
    Measure.map_apply (measurable_reversedPath m) (measurableSet_singleton p),
    cond_apply (measurableSet_aReversalEvent A s m n), cond_apply (measurableSet_aReversalEvent A s m n)]
  have h := timeReversal_atom μ A s m n p
  show _ * 𝐏w[μ] (aReversalEvent A s m n ∩ {ω | walkPath m ω = p}) =
    _ * 𝐏w[μ] (aReversalEvent A s m n ∩ {ω | reversedPath m ω = p})
  rw [Set.inter_comm (aReversalEvent A s m n), Set.inter_comm (aReversalEvent A s m n), h]

end BGWLeaves.GeneralAFunctional.WalkReversal
