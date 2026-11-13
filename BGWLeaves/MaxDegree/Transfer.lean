module

public import BGWLeaves.MaxDegree.Defs
public import BGWLeaves.Vervaat
import BGWLeaves.Vervaat.Discrete

/-!
# Maximum degree: steps versus degrees and the transfer of the cyclic maximum

Proofs for steps versus degrees and the transfer of the cyclic maximum (Vervaat): `maxDegree_lt_iff`, `lt_maxDegree_iff`, `maximum_increments`, `maxDegree_eq_zero_iff`, `two_le_maxDegree_of_two_le_leaves`, `transfer_vervaat_invariant`, `exists_isMarkTime_of_le`, `walkWord_take`, `IsMarkTime.last_step`.  The theorems are those stated in
`BGWLeaves.MaxDegree`; they are exported in namespace `BGWLeaves.MaxDegree.Transfer` with exactly the types stated
there.
-/

@[expose] public section

namespace BGWLeaves.MaxDegree.Transfer

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

private theorem maximum_degree_increments (l : List ℕ) (h : l ≠ []) :
    (l.map fun d : ℕ => (d : ℤ) - 1).maximum =
      ((((l.foldr max 0 : ℕ) : ℤ) - 1 : ℤ) : WithBot ℤ) := by
  induction l with
  | nil => contradiction
  | cons a l ih =>
    simp only [List.map_cons, List.maximum_cons, List.foldr]
    by_cases hl : l = []
    · subst l
      simp
    · rw [ih hl, ← WithBot.coe_max]
      congr 1
      rw [Nat.cast_max, max_sub_sub_right]

/-- The exact identity: the largest increment of the Łukasiewicz word is `Δ(τ) - 1` (as an element of
`WithBot ℤ`, `List.maximum`; the word is never empty). -/
theorem maximum_increments (t : PlaneTree) :
    t.increments.maximum = (((maxDegree t : ℤ) - 1 : ℤ) : WithBot ℤ) := by
  apply maximum_degree_increments
  intro h
  have hl := t.length_degrees
  have hs := t.size_pos
  rw [h] at hl
  simp at hl
  omega

private theorem maximum_increments_mem (t : PlaneTree) :
    ((maxDegree t : ℤ) - 1) ∈ t.increments :=
  (List.maximum_eq_coe_iff.mp (maximum_increments t)).1

private theorem increment_le_maximum {t : PlaneTree} {a : ℤ} (ha : a ∈ t.increments) :
    a ≤ (maxDegree t : ℤ) - 1 := by
  have h := (List.maximum_eq_coe_iff.mp (maximum_increments t)).2 a ha
  exact h

/-- `Δ(τ) = M(W_1(τ) - W_0(τ), …, W_ζ(τ) - W_ζ-1(τ)) + 1` (line 2390), the printed identity, in the
form of the equivalences used in the proof: `Δ(τ) < p + 1 ⟺ M < p` ... -/
theorem maxDegree_lt_iff (t : PlaneTree) (p : ℝ) :
    (maxDegree t : ℝ) < p + 1 ↔ StepsLt p t.increments := by
  constructor
  · intro h a ha
    have hle := increment_le_maximum ha
    have hle' : (a : ℝ) ≤ (((maxDegree t : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hle
    push_cast at hle'
    linarith
  · intro h
    have hm := h _ (maximum_increments_mem t)
    push_cast at hm
    linarith

/-- ... and `Δ(τ) > q + 1 ⟺ M > q`. -/
theorem lt_maxDegree_iff (t : PlaneTree) (q : ℝ) :
    q + 1 < (maxDegree t : ℝ) ↔ StepsGt q t.increments := by
  constructor
  · intro h
    refine ⟨(maxDegree t : ℤ) - 1, maximum_increments_mem t, ?_⟩
    push_cast
    linarith
  · rintro ⟨a, ha, hq⟩
    have hle := increment_le_maximum ha
    have hle' : (a : ℝ) ≤ (((maxDegree t : ℤ) - 1 : ℤ) : ℝ) := by exact_mod_cast hle
    push_cast at hle'
    linarith

private theorem foldr_max_eq_zero_iff_sum_eq_zero (l : List ℕ) :
    l.foldr max 0 = 0 ↔ l.sum = 0 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr, List.sum_cons]
    constructor <;> intro h
    · have hf : l.foldr max 0 = 0 := by omega
      have ha : a = 0 := by omega
      have hs := ih.mp hf
      omega
    · have ha : a = 0 := by omega
      have hs : l.sum = 0 := by omega
      have hf := ih.mpr hs
      omega

/-- Exceptional one-vertex convention: `Δ(τ) = 0` iff `τ` is the one-vertex tree. -/
theorem maxDegree_eq_zero_iff (t : PlaneTree) : maxDegree t = 0 ↔ t.size = 1 := by
  change t.degrees.foldr max 0 = 0 ↔ t.size = 1
  rw [foldr_max_eq_zero_iff_sum_eq_zero]
  have h := t.sum_degrees_add_one
  omega

private theorem two_le_foldr_max_iff_exists (l : List ℕ) :
    2 ≤ l.foldr max 0 ↔ ∃ a ∈ l, 2 ≤ a := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr, List.mem_cons]
    constructor <;> intro h
    · by_cases ha : 2 ≤ a
      · exact ⟨a, Or.inl rfl, ha⟩
      · have hf : 2 ≤ l.foldr max 0 := by omega
        obtain ⟨b, hb, hb2⟩ := ih.mp hf
        exact ⟨b, Or.inr hb, hb2⟩
    · obtain ⟨b, hb, hb2⟩ := h
      rcases hb with rfl | hb
      · omega
      · have hf := ih.mpr ⟨b, hb, hb2⟩
        omega

private theorem sum_add_count_zero_eq_length (l : List ℕ) (h : ∀ a ∈ l, a ≤ 1) :
    l.sum + l.count 0 = l.length := by
  classical
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := h a (by simp)
    have hl := ih (fun b hb => h b (by simp [hb]))
    simp only [List.sum_cons, List.length_cons]
    by_cases ha0 : a = 0 <;> simp [ha0] <;> omega

/-- A tree with at least two leaves has a vertex with at least two children, so `Δ ≥ 2`. -/
theorem two_le_maxDegree_of_two_le_leaves (t : PlaneTree) (h : 2 ≤ t.degreeCount 0) : 2 ≤ maxDegree t := by
  change 2 ≤ t.degrees.foldr max 0
  rw [two_le_foldr_max_iff_exists]
  by_contra hn
  push Not at hn
  have hle : ∀ a ∈ t.degrees, a ≤ 1 := by
    intro a ha
    have := hn a ha
    omega
  have hc := sum_add_count_zero_eq_length t.degrees hle
  have hs := t.sum_degrees_add_one
  have hl := t.length_degrees
  change 2 ≤ t.degrees.count 0 at h
  omega

/-- **General transfer under a Vervaat-invariant set of words.** -/
theorem transfer_vervaat_invariant (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n)
    (S : Set (List ℤ)) (hS : ∀ x : List ℤ, vervaat x ∈ S ↔ x ∈ S) :
    ((bienaymeLaw μ)[|leafCountEvent n]) (treeStepsIn S) =
      ((𝐏w[μ])[|bridgeAtMark n]) (bridgeStepsIn n S) := by
  let ι := {x : List ℤ // x ∈ S}
  have hW : bridgeStepsIn n S = ⋃ x : ι, vervaatAtMark n x := by
    ext ω
    constructor
    · rintro ⟨k, hk, hs, hw⟩
      refine Set.mem_iUnion.2 ⟨⟨vervaat (walkWord ω k), (hS _).2 hw⟩, ?_⟩
      exact ⟨k, hk, hs, rfl⟩
    · intro hω
      obtain ⟨x, k, hk, hs, hx⟩ := Set.mem_iUnion.1 hω
      refine ⟨k, hk, hs, (hS _).1 ?_⟩
      rw [hx]
      exact x.property
  have hT : leafCountEvent n ∩ treeStepsIn S = ⋃ x : ι, treeWordLeaves n x := by
    ext T
    constructor
    · rintro ⟨⟨t, rfl, ht⟩, t', ht', hw⟩
      have hEq : t' = t := PlaneTree.toLocallyFinite_injective ht'
      subst t'
      exact Set.mem_iUnion.2 ⟨⟨t.increments, hw⟩, t, rfl, rfl, ht⟩
    · intro hT
      obtain ⟨x, t, rfl, hx, ht⟩ := Set.mem_iUnion.1 hT
      refine ⟨⟨t, rfl, ht⟩, t, rfl, ?_⟩
      change t.increments ∈ S
      rw [hx]
      exact x.property
  have hdisjW : Pairwise (Function.onFun Disjoint (fun x : ι => vervaatAtMark n x)) := by
    intro x y hxy
    refine Set.disjoint_left.mpr (fun ω h1 h2 => hxy ?_)
    obtain ⟨k, hk, -, hx⟩ := h1
    obtain ⟨k', hk', -, hy⟩ := h2
    have hkk' := hk.unique hk'
    subst k'
    exact Subtype.ext (hx.symm.trans hy)
  have hdisjT : Pairwise (Function.onFun Disjoint (fun x : ι => treeWordLeaves n x)) := by
    intro x y hxy
    refine Set.disjoint_left.mpr (fun T h1 h2 => hxy ?_)
    obtain ⟨s, rfl, hs, -⟩ := h1
    obtain ⟨s', hs', hs'', -⟩ := h2
    have hEq : s' = s := PlaneTree.toLocallyFinite_injective hs'
    subst s'
    exact Subtype.ext (hs.symm.trans hs'')
  have hjoint : 𝐏w[μ] (bridgeStepsIn n S) =
      (n : ℝ≥0∞) * bienaymeLaw μ (leafCountEvent n ∩ treeStepsIn S) := by
    rw [hW, measure_iUnion hdisjW
        (fun x => BGWLeaves.Vervaat.Discrete.measurableSet_vervaatAtMark hn x),
      hT, measure_iUnion hdisjT
        (fun _ => BGWLeaves.Vervaat.Discrete.measurableSet_finiteTreeEvent' _),
      ← ENNReal.tsum_mul_left]
    exact tsum_congr (fun x => prop_vervaatdiscrete_joint μ hn x)
  have hB : bridgeStepsIn n S ⊆ bridgeAtMark n := by
    rintro ω ⟨k, hk, hs, -⟩
    exact ⟨k, hk, hs⟩
  rw [cond_apply (measurableSet_leafCountEvent n), cond_apply (measurableSet_bridgeAtMark n),
    Set.inter_eq_right.2 hB, hjoint, prop_vervaatdiscrete_total μ hn]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnT : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hinv : (n : ℝ≥0∞)⁻¹ * n = 1 := ENNReal.inv_mul_cancel hn0 hnT
  rw [ENNReal.mul_inv (Or.inl hn0) (Or.inl hnT)]
  calc
    (bienaymeLaw μ (leafCountEvent n))⁻¹ * bienaymeLaw μ (leafCountEvent n ∩ treeStepsIn S) =
        ((n : ℝ≥0∞)⁻¹ * n) *
          ((bienaymeLaw μ (leafCountEvent n))⁻¹ * bienaymeLaw μ (leafCountEvent n ∩ treeStepsIn S)) := by
      rw [hinv, one_mul]
    _ = _ := by ring

/-- A smaller mark time exists before a larger one. -/
theorem exists_isMarkTime_of_le {n m : ℕ} {ω : ℕ → ℕ} {k : ℕ} (h : IsMarkTime n ω k) (hmn : m ≤ n) :
    ∃ k' : ℕ, k' ≤ k ∧ IsMarkTime m ω k' := by
  classical
  have hk : m ≤ walkLeafCount ω k := by rw [h.1]; exact hmn
  have hex : ∃ q, m ≤ walkLeafCount ω q := ⟨k, hk⟩
  refine ⟨Nat.find hex, Nat.find_min' hex hk, ?_⟩
  have hcount := Nat.find_spec hex
  rcases hfind : Nat.find hex with _ | j
  · rw [hfind] at hcount
    have hm0 : m = 0 := by simpa [walkLeafCount] using Nat.eq_zero_of_le_zero hcount
    exact ⟨by simp [walkLeafCount, hm0], fun q hq => absurd hq (Nat.not_lt_zero _)⟩
  · have hprev : walkLeafCount ω j < m := by
      have hmin := Nat.find_min hex (show j < Nat.find hex by omega)
      omega
    have hs := BGWLeaves.Vervaat.Discrete.walkLeafCount_succ' ω j
    have heq : walkLeafCount ω (j + 1) = m := by
      rw [hfind] at hcount
      split_ifs at hs <;> omega
    refine ⟨by simpa [hfind] using heq, fun q hq => ?_⟩
    have hmono : walkLeafCount ω q ≤ walkLeafCount ω j := by
      unfold walkLeafCount
      exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.range_mono (by omega)))
    omega

/-- The prefix of the word of the first `k` steps is the word of the first `k'` steps. -/
theorem walkWord_take (ω : ℕ → ℕ) {k' k : ℕ} (h : k' ≤ k) : (walkWord ω k).take k' = walkWord ω k' := by
  simp [walkWord, ← List.map_take, List.take_range, Nat.min_eq_left h]

/-- The mark steps: the `T_m`-th step of the walk is `-1` for `m ≥ 1`. -/
theorem IsMarkTime.last_step {m : ℕ} (hm : 1 ≤ m) {ω : ℕ → ℕ} {k : ℕ} (h : IsMarkTime m ω k) :
    1 ≤ k ∧ ω (k - 1) = 0 := by
  have hk : 1 ≤ k := by
    by_contra hk
    have hk0 : k = 0 := by omega
    subst k
    have hzero := h.1
    simp [walkLeafCount] at hzero
    omega
  refine ⟨hk, ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hprev := h.2 j (by omega)
  have hs := BGWLeaves.Vervaat.Discrete.walkLeafCount_succ' ω j
  rw [h.1] at hs
  by_cases hz : ω j = 0
  · exact hz
  · rw [ite_eq_right hz] at hs
    omega

end BGWLeaves.MaxDegree.Transfer
