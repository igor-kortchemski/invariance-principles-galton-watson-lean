module

public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.LeafMass
public import BGWLeaves.LeafConcentration
import BGW.StableTrees.CriticalSupport
import BGW.Tree.DFS
import BGW.Tree.Fringe
import BGW.Tree.Vertices
import BGW.ContinuumTrees.LeafMeasure

/-!
# Discrete glue and in-probability inputs for the leaf-conditioned limits

Proofs of the discrete glue and the in-probability inputs
`vervaatD_stepPath_vervaat`, `tendsto_treeSize_div_leaf` and `tendsto_leafIndex_discrepancy` of
`BGWLeaves.LeafLimits`, exported in namespace `BGWLeaves.LeafLimits.Helpers` with exactly the types
stated there.

* `vervaatD_stepPath_vervaat` (the Vervaat transform at the path level): BGW `vervaatD_stepPath` and the
  identity `vervaat x = x.rotate (vervaatIndex x)` (the project's `vervaat` is the cyclic shift at
  `vervaatIdx`, whose defining set is BGW's `vervaatIndex` set; this module proves its own copy of
  `vervaat_eq_rotate_vervaatIndex` and does not import `BGWLeaves.ClassicalLimits`).
* `tendsto_treeSize_div_leaf` (`eq:lg`): Corollary 3.3 (`cor_Lambda_isOe`) read at time `t = 1`, where
  `Λ_τ(ζ)/ζ = λ/ζ = n/ζ`; `oe` sequences tend to `0` (`IsOe.tail`).
* `tendsto_leafIndex_discrepancy`: the leaves of BGW's DFS enumeration `vertices` are the zeros
  of the DFS degree list `degrees` (BGW `map_fringe?_vertices_rootDegree`), so `numLeaves = λ` and
  `Λ_τ(ℓ_j) = j + 1` for the DFS index `ℓ_j` of the `j`-th leaf.  Corollary 3.3 at the times
  `t = ℓ_j/ζ ≥ η` gives `(j + 1)/ℓ_j ≈ μ₀`, at `t = 1` gives `n/ζ ≈ μ₀`, and at `t = η` (with the
  monotonicity of `Λ_τ`) bounds the leaves with `ℓ_j < ηζ`.
-/

@[expose] public section

namespace BGWLeaves.LeafLimits.Helpers

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-! ## The Vervaat transform at the path level -/

/-- The project's Vervaat transform is the rotation at BGW's discrete Vervaat index (private copy of
`vervaat_eq_rotate_vervaatIndex`: the two defining sets coincide). -/
private theorem vervaat_eq_rotate (x : List ℤ) :
    vervaat x = x.rotate (Skorokhod.vervaatIndex x) := by
  rw [vervaat, cyclicShift_eq_rotate]
  rfl

/-- **The Vervaat transform at the path level**: `V(stepPath x B) = stepPath (V x) B`. -/
theorem vervaatD_stepPath_vervaat {x : List ℤ}
    (hx : ∃ j, 1 ≤ j ∧ j ≤ x.length ∧ (x.take j).sum < 0) {B : ℝ} (hB : 0 < B) :
    Skorokhod.vervaatD (Skorokhod.stepPath x B) = Skorokhod.stepPath (vervaat x) B := by
  rw [Skorokhod.vervaatD_stepPath hx hB, vervaat_eq_rotate]

/-! ## Common tools -/

private theorem mu0_pos {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) : 0 < (μ 0).toReal :=
  ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (PMF.apply_ne_top μ 0)

/-- A nonnegative `oe_{1/2}` sequence tends to `0`. -/
private theorem tendsto_zero_of_isOe {x : ℕ → ℝ} (hx : IsOe (1 / 2) x) (hx0 : ∀ n, 0 ≤ x n) :
    Tendsto x atTop (𝓝 0) :=
  (IsOe.tail (by norm_num) hx0 hx).1.tendsto_atTop_zero

/-- Monotonicity of a conditional probability through the conditioning event. -/
private theorem cond_real_le_of_inter_subset {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {L E F : Set Ω} (hL : MeasurableSet L) (h : L ∩ E ⊆ F) :
    (P[|L]).real E ≤ (P[|L]).real F := by
  have hm : P (L ∩ E) ≤ P (L ∩ F) := measure_mono (Set.subset_inter Set.inter_subset_left h)
  have hle : P[|L] E ≤ P[|L] F := by
    rw [cond_apply hL, cond_apply hL]
    gcongr
  exact ENNReal.toReal_mono (measure_ne_top _ _) hle

/-- `δ / n^{1/4} ≤ δ` for every natural `n` (`0^{1/4} = 0` and `x / 0 = 0`). -/
private theorem div_rpow_quarter_le {δ : ℝ} (hδ : 0 ≤ δ) (n : ℕ) :
    δ / (n : ℝ) ^ (1 / 4 : ℝ) ≤ δ := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hδ]
  · exact div_le_self hδ (Real.one_le_rpow (by exact_mod_cast hn) (by norm_num))

/-- The deviation of Corollary 3.3 at time `1` is `λ/ζ - μ₀`. -/
private theorem treeLeafDev_one (p : ℝ) (t : PlaneTree) :
    treeLeafDev p t t.size 1 = (t.degreeCount 0 : ℝ) / t.size - p := by
  simp [treeLeafDev, Lambda]

/-! ## `ζ/n → 1/μ₀` -/

private theorem abs_one_div_sub_le {μ₀ δ ε a : ℝ} (hμ : 0 < μ₀) (hε : 0 ≤ ε) (hδ1 : δ ≤ μ₀ / 2)
    (hδ2 : δ ≤ ε * μ₀ ^ 2 / 2) (ha : |a - μ₀| < δ) : |1 / a - 1 / μ₀| ≤ ε := by
  obtain ⟨ha1, -⟩ := abs_lt.1 ha
  have hapos : μ₀ / 2 < a := by linarith
  have ha0 : 0 < a := by linarith
  rw [div_sub_div _ _ ha0.ne' hμ.ne', abs_div, abs_of_pos (mul_pos ha0 hμ),
    div_le_iff₀ (mul_pos ha0 hμ)]
  have h1 : |1 * μ₀ - a * 1| = |a - μ₀| := by rw [one_mul, mul_one, abs_sub_comm]
  rw [h1]
  have h2 : ε * (μ₀ / 2 * μ₀) ≤ ε * (a * μ₀) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hapos.le hμ.le) hε
  have h3 : ε * (μ₀ / 2 * μ₀) = ε * μ₀ ^ 2 / 2 := by ring
  linarith

/-- Under `P_μ[· | λ = n]`, `ζ(τ_n)/n → 1/μ₀` in probability (`eq:lg`). -/
theorem tendsto_treeSize_div_leaf {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ε < |(treeSize τ : ℝ) / q k - 1 / (μ 0).toReal|}) atTop (𝓝 0) := by
  have hμ0 : 0 < (μ 0).toReal := mu0_pos hc hne
  set δ : ℝ := min ((μ 0).toReal / 2) (ε * (μ 0).toReal ^ 2 / 2) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ (μ 0).toReal / 2 := min_le_left _ _
  have hδ2 : δ ≤ ε * (μ 0).toReal ^ 2 / 2 := min_le_right _ _
  have hOe := cor_Lambda_isOe hc hne hap hDA (η := 1 / 2) (by norm_num) (by norm_num) hδ0
  have hbad := (tendsto_zero_of_isOe hOe (fun n => measureReal_nonneg)).comp hqtop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hbad
    (fun k => measureReal_nonneg) (fun k => ?_)
  try simp only [Function.comp_apply]
  rw [coe_leafTreeLaw (hq k)]
  apply cond_real_le_of_inter_subset (measurableSet_leafCountEvent (q k))
  rintro τ ⟨⟨t, rfl, hdeg⟩, hE⟩
  refine ⟨t, rfl, ?_⟩
  rw [Set.mem_ofPred_eq, treeSize_toLocallyFinite, ← one_div_div (q k : ℝ) (t.size : ℝ)] at hE
  have hsup : ENNReal.ofReal |treeLeafDev (μ 0).toReal t t.size 1| ≤
      supDev (1 / 2) (treeLeafDev (μ 0).toReal t t.size) :=
    le_iSup₂ (f := fun s (_ : s ∈ Set.Icc (1 / 2 : ℝ) 1) =>
      ENNReal.ofReal |treeLeafDev (μ 0).toReal t t.size s|) 1 ⟨by norm_num, le_rfl⟩
  refine le_trans ?_ hsup
  apply ENNReal.ofReal_le_ofReal
  rw [treeLeafDev_one, hdeg]
  refine (div_rpow_quarter_le hδ0.le (q k)).trans ?_
  by_contra hlt
  rw [not_le] at hlt
  exact absurd hE (not_lt.2 (abs_one_div_sub_le hμ0 hε.le hδ1 hδ2 hlt))

/-! ## Leaves in DFS order -/

/-- A Boolean form of the leaf predicate of BGW's `leafAddrs`. -/
private theorem leafAddrs_eq (t : PlaneTree) :
    ∃ p : List ℕ → Bool, (∀ u, p u = true ↔ ContinuumTrees.LeafMeasure.IsLeafAddr t u) ∧
      ContinuumTrees.LeafMeasure.leafAddrs t = t.vertices.filter p := by
  classical
  exact ⟨fun u => decide (ContinuumTrees.LeafMeasure.IsLeafAddr t u), fun _ => decide_eq_true_iff,
    rfl⟩

private theorem length_filter_eq_count_map {α : Type*} (p : α → Bool) (L : List α) :
    (L.filter p).length = (L.map p).count true := by
  rw [← List.countP_eq_length_filter, List.count_eq_countP, List.countP_map]
  congr 1

private theorem count_map_eq_zero (L : List ℕ) :
    (L.map fun d => decide (d = 0)).count true = L.count 0 := by
  rw [List.count_eq_countP, List.count_eq_countP, List.countP_map]
  congr 1

/-- The number of `p`-elements up to and including the first occurrence of `a` (with `p a`) is the
rank of `a` among the `p`-elements, plus one. -/
private theorem length_filter_take_idxOf_succ {α : Type*} [BEq α] [LawfulBEq α] (p : α → Bool)
    {a : α} (hpa : p a = true) : ∀ {L : List α}, a ∈ L →
      ((L.take (L.idxOf a + 1)).filter p).length = (L.filter p).idxOf a + 1
  | [], h => by simp at h
  | b :: L, h => by
    by_cases hba : b = a
    · subst hba
      simp [List.idxOf_cons_self, hpa]
    · have haL : a ∈ L := (List.mem_cons.1 h).resolve_left (fun h' => hba h'.symm)
      have ih := length_filter_take_idxOf_succ p hpa haL
      rw [List.idxOf_cons_ne _ hba, Nat.succ_eq_add_one, List.take_succ_cons]
      by_cases hpb : p b = true
      · rw [List.filter_cons_of_pos hpb, List.filter_cons_of_pos hpb, List.length_cons,
          List.idxOf_cons_ne _ hba, Nat.succ_eq_add_one, ih]
      · rw [List.filter_cons_of_neg hpb, List.filter_cons_of_neg hpb, ih]

/-- The leaf predicate along the DFS enumeration is the zero predicate along the degree list. -/
private theorem map_vertices_eq (t : PlaneTree) (p : List ℕ → Bool)
    (hp : ∀ u, p u = true ↔ ContinuumTrees.LeafMeasure.IsLeafAddr t u) :
    t.vertices.map p = t.degrees.map (fun d => decide (d = 0)) := by
  have h := PlaneTree.map_fringe?_vertices_rootDegree t
  have h2 : t.vertices.map p =
      (t.vertices.map (fun u => (t.fringe? u).map PlaneTree.rootDegree)).map
        (fun o => decide (o = some 0)) := by
    rw [List.map_map]
    refine List.map_congr_left fun u hu => ?_
    obtain ⟨s, hs⟩ : ∃ s, t.fringe? u = some s := (PlaneTree.mem_vertices_iff t u).1 hu
    have hleaf : p u = true ↔ s.rootDegree = 0 := by
      rw [hp]
      unfold ContinuumTrees.LeafMeasure.IsLeafAddr
      rw [PlaneTree.isVertex_append_singleton_iff hs 0]
      constructor
      · intro h0
        omega
      · intro h0
        omega
    simp only [Function.comp_apply, hs, Option.map_some, Option.some.injEq]
    by_cases h0 : s.rootDegree = 0
    · rw [decide_eq_true h0]
      exact hleaf.2 h0
    · rw [decide_eq_false h0]
      simpa [h0] using hleaf
  rw [h2, h, List.map_map]
  refine List.map_congr_left fun d _ => ?_
  simp

private theorem count_take_degrees (t : PlaneTree) (p : List ℕ → Bool)
    (hp : ∀ u, p u = true ↔ ContinuumTrees.LeafMeasure.IsLeafAddr t u) (m : ℕ) :
    ((t.vertices.take m).filter p).length = (t.degrees.take m).count 0 := by
  rw [length_filter_eq_count_map, List.map_take, map_vertices_eq t p hp, ← List.map_take,
    count_map_eq_zero]

/-- BGW's number of leaves is the project's `λ(τ)`. -/
private theorem numLeaves_eq (t : PlaneTree) :
    ContinuumTrees.LeafMeasure.numLeaves t = t.degreeCount 0 := by
  obtain ⟨p, hp, hLA⟩ := leafAddrs_eq t
  unfold ContinuumTrees.LeafMeasure.numLeaves
  rw [hLA, length_filter_eq_count_map, map_vertices_eq t p hp, count_map_eq_zero]
  rfl

private theorem sum_childCountAt_eq_count (t : PlaneTree) {m : ℕ} (hm : m ≤ t.size) :
    (∑ i ∈ Finset.range m, if childCountAt t i = 0 then 1 else 0) =
      (t.degrees.take m).count 0 := by
  rw [count_zero_eq_sum, List.length_take, PlaneTree.length_degrees, min_eq_left hm]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < m := Finset.mem_range.1 hi
  unfold childCountAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take,
    ite_eq_left hi']

/-- `Λ_τ(ℓ_j) = j + 1` at the DFS index `ℓ_j` of the `j`-th leaf. -/
private theorem Lambda_leafIndex (t : PlaneTree) {j : ℕ}
    (hj : j < ContinuumTrees.LeafMeasure.numLeaves t) :
    Lambda t (ContinuumTrees.LeafMeasure.leafIndex t j : ℝ) = j + 1 := by
  have hlt := ContinuumTrees.LeafMeasure.leafIndex_lt_size t j
  have hlt' : ((ContinuumTrees.LeafMeasure.leafIndex t j : ℕ) : ℝ) < t.size := by
    exact_mod_cast hlt
  unfold Lambda
  rw [ite_eq_right (not_le.2 hlt'), Nat.floor_natCast, sum_childCountAt_eq_count t (by omega)]
  obtain ⟨p, hp, hLA⟩ := leafAddrs_eq t
  rw [← count_take_degrees t p hp]
  have hval := ContinuumTrees.LeafMeasure.leafVertex_val t hj
  have hnd : (ContinuumTrees.LeafMeasure.leafAddrs t).Nodup := by
    rw [hLA]
    exact (PlaneTree.nodup_vertices t).filter p
  have hidx : (ContinuumTrees.LeafMeasure.leafAddrs t).idxOf
      (ContinuumTrees.LeafMeasure.leafVertex t j).val = j := by
    rw [hval]
    exact hnd.idxOf_getElem j hj
  have hmem : (ContinuumTrees.LeafMeasure.leafVertex t j).val ∈
      ContinuumTrees.LeafMeasure.leafAddrs t := by
    rw [hval]
    exact List.getElem_mem hj
  rw [hLA] at hidx hmem
  obtain ⟨haV, hpa⟩ := List.mem_filter.1 hmem
  have key := length_filter_take_idxOf_succ p hpa haV
  rw [hidx] at key
  exact key

/-- `Λ_τ` is nondecreasing inside the tree. -/
private theorem Lambda_le_Lambda (t : PlaneTree) {a b : ℝ} (hab : a ≤ b)
    (hb : b < t.size) : Lambda t a ≤ Lambda t b := by
  have ha' : ¬ (t.size : ℝ) ≤ a := by linarith
  have hb' : ¬ (t.size : ℝ) ≤ b := not_le.2 hb
  unfold Lambda
  rw [ite_eq_right ha', ite_eq_right hb']
  apply Finset.sum_le_sum_of_subset
  exact Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hab) 1)

/-! ## The two arithmetic cases of the leaf-index discrepancy -/

/-- Leaves late in the DFS order (`ℓ ≥ ηζ`): `(j+1)/ℓ ≈ μ₀` and `n/ζ ≈ μ₀` give `ℓ/ζ ≈ j/n`. -/
private theorem leaf_arith_big {μ₀ δ ε z n l j : ℝ} (hδ1 : δ ≤ μ₀ / 2)
    (hδ2 : δ ≤ ε * μ₀ / 8) (hε : 0 < ε) (hn1 : 2 ≤ ε * n) (hz : 0 < z) (hl : 0 < l)
    (hlz : l ≤ z) (hN : |n / z - μ₀| < δ) (hJ : |(j + 1) / l - μ₀| < δ) :
    |l / z - j / n| ≤ ε := by
  have hδ0 : 0 < δ := lt_of_le_of_lt (abs_nonneg _) hN
  obtain ⟨hN1, hN2⟩ := abs_lt.1 hN
  obtain ⟨hJ1, hJ2⟩ := abs_lt.1 hJ
  have hn_lo : (μ₀ - δ) * z < n := (lt_div_iff₀ hz).1 (by linarith)
  have hn_hi : n < (μ₀ + δ) * z := (div_lt_iff₀ hz).1 (by linarith)
  have hj_lo : (μ₀ - δ) * l < j + 1 := (lt_div_iff₀ hl).1 (by linarith)
  have hj_hi : j + 1 < (μ₀ + δ) * l := (div_lt_iff₀ hl).1 (by linarith)
  have hμz : 0 < (μ₀ - δ) * z := mul_pos (by linarith) hz
  have hnpos : 0 < n := by linarith
  have hz2 : 0 < z * n := mul_pos hz hnpos
  rw [div_sub_div _ _ hz.ne' hnpos.ne', abs_div, abs_of_pos hz2, div_le_iff₀ hz2]
  have e1 : l * n < l * ((μ₀ + δ) * z) := mul_lt_mul_of_pos_left hn_hi hl
  have e2 : l * ((μ₀ - δ) * z) < l * n := mul_lt_mul_of_pos_left hn_lo hl
  have e3 : z * ((μ₀ - δ) * l) < z * (j + 1) := mul_lt_mul_of_pos_left hj_lo hz
  have e4 : z * (j + 1) < z * ((μ₀ + δ) * l) := mul_lt_mul_of_pos_left hj_hi hz
  have e5 : δ * z * l ≤ δ * z * z := mul_le_mul_of_nonneg_left hlz (by positivity)
  have f1 : ε * ((μ₀ - δ) * z) < ε * n := mul_lt_mul_of_pos_left hn_lo hε
  have f2 : ε * (μ₀ / 2 * z) ≤ ε * ((μ₀ - δ) * z) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hz.le) hε.le
  have f3 : 4 * δ * z ≤ ε * (μ₀ / 2 * z) := by
    have : 4 * δ ≤ ε * (μ₀ / 2) := by linarith
    nlinarith
  have f4 : 1 + 2 * δ * z ≤ ε * n := by linarith
  have e6 : z * (1 + 2 * δ * z) ≤ z * (ε * n) := mul_le_mul_of_nonneg_left f4 hz.le
  rw [abs_le]
  constructor <;> nlinarith

/-- Leaves early in the DFS order (`ℓ < ηζ`): both `ℓ/ζ` and `j/n` are `O(η)`. -/
private theorem leaf_arith_small {μ₀ δ ε η z n l j Λη : ℝ} (hμ : 0 < μ₀) (hδ1 : δ ≤ μ₀ / 2)
    (hη0 : 0 < η) (hη : η ≤ ε / 4) (hz : 0 < z) (hl0 : 0 ≤ l) (hl : l < η * z)
    (hj0 : 0 ≤ j) (hjΛ : j + 1 ≤ Λη) (hN : |n / z - μ₀| < δ) (hΛ : |Λη / (z * η) - μ₀| < δ) :
    |l / z - j / n| ≤ ε := by
  obtain ⟨hN1, -⟩ := abs_lt.1 hN
  obtain ⟨-, hΛ2⟩ := abs_lt.1 hΛ
  have hn_lo : (μ₀ - δ) * z < n := (lt_div_iff₀ hz).1 (by linarith)
  have hμz : 0 < (μ₀ - δ) * z := mul_pos (by linarith) hz
  have hnpos : 0 < n := by linarith
  have hzη : 0 < z * η := mul_pos hz hη0
  have hΛ_hi : Λη < (μ₀ + δ) * (z * η) := (div_lt_iff₀ hzη).1 (by linarith)
  have hlz : l / z < η := (div_lt_iff₀ hz).2 (by linarith)
  have hlz0 : 0 ≤ l / z := div_nonneg hl0 hz.le
  have hjn0 : 0 ≤ j / n := div_nonneg hj0 hnpos.le
  have g1 : (μ₀ + δ) * (z * η) ≤ (3 / 2 * μ₀) * (z * η) :=
    mul_le_mul_of_nonneg_right (by linarith) hzη.le
  have g2 : η * ((μ₀ - δ) * z) < η * n := mul_lt_mul_of_pos_left hn_lo hη0
  have g3 : η * (μ₀ / 2 * z) ≤ η * ((μ₀ - δ) * z) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (by linarith) hz.le) hη0.le
  have hjn : j / n ≤ 3 * η := by
    rw [div_le_iff₀ hnpos]
    nlinarith
  rw [abs_le]
  constructor <;> linarith

/-- **Leaf-index discrepancy**: under `P_μ[· | λ = n]`, `max_j |ℓ_j/ζ - j/λ| → 0` in probability. -/
theorem tendsto_leafIndex_discrepancy {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).toMeasure.real
      {τ | ∃ j < ContinuumTrees.LeafMeasure.numLeaves (toPlaneTree τ),
        ε < |(ContinuumTrees.LeafMeasure.leafIndex (toPlaneTree τ) j : ℝ) /
            ((toPlaneTree τ).size : ℝ) -
          (j : ℝ) / (ContinuumTrees.LeafMeasure.numLeaves (toPlaneTree τ) : ℝ)|}) atTop (𝓝 0) := by
  have hμ0 : 0 < (μ 0).toReal := mu0_pos hc hne
  set η : ℝ := min (ε / 4) (1 / 2) with hηdef
  have hη0 : 0 < η := lt_min (by positivity) (by norm_num)
  have hη1 : η < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hηε : η ≤ ε / 4 := min_le_left _ _
  set δ : ℝ := min ((μ 0).toReal / 2) (ε * (μ 0).toReal / 8) with hδdef
  have hδ0 : 0 < δ := lt_min (by positivity) (by positivity)
  have hδ1 : δ ≤ (μ 0).toReal / 2 := min_le_left _ _
  have hδ2 : δ ≤ ε * (μ 0).toReal / 8 := min_le_right _ _
  have hOe := cor_Lambda_isOe hc hne hap hDA hη0 hη1 hδ0
  have hbad := (tendsto_zero_of_isOe hOe (fun n => measureReal_nonneg)).comp hqtop
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, 2 / ε < N0 := exists_nat_gt (2 / ε)
  have hev : ∀ᶠ k in atTop, N0 ≤ q k := hqtop.eventually_ge_atTop N0
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbad
    (Eventually.of_forall fun k => measureReal_nonneg) ?_
  filter_upwards [hev] with k hk
  try simp only [Function.comp_apply]
  rw [coe_leafTreeLaw (hq k)]
  apply cond_real_le_of_inter_subset (measurableSet_leafCountEvent (q k))
  rintro τ ⟨⟨t, rfl, hdeg⟩, hE⟩
  refine ⟨t, rfl, ?_⟩
  by_contra hQ
  rw [not_le] at hQ
  have hG : ∀ s ∈ Set.Icc η 1, |treeLeafDev (μ 0).toReal t t.size s| < δ := by
    intro s hs
    have h1 : ENNReal.ofReal |treeLeafDev (μ 0).toReal t t.size s| ≤
        supDev η (treeLeafDev (μ 0).toReal t t.size) :=
      le_iSup₂ (f := fun s (_ : s ∈ Set.Icc η 1) =>
        ENNReal.ofReal |treeLeafDev (μ 0).toReal t t.size s|) s hs
    have h2 := lt_of_le_of_lt h1 hQ
    rw [ENNReal.ofReal_lt_ofReal_iff_of_nonneg (abs_nonneg _)] at h2
    exact lt_of_lt_of_le h2 (div_rpow_quarter_le hδ0.le _)
  obtain ⟨j, hj, hjε⟩ := hE
  rw [toPlaneTree_toLocallyFinite] at hj hjε
  have hNL : ContinuumTrees.LeafMeasure.numLeaves t = q k := (numLeaves_eq t).trans hdeg
  have hΛ := Lambda_leafIndex t hj
  rw [hNL] at hjε
  have hℓlt : (ContinuumTrees.LeafMeasure.leafIndex t j : ℝ) < t.size := by
    exact_mod_cast ContinuumTrees.LeafMeasure.leafIndex_lt_size t j
  have hz : (0 : ℝ) < t.size := lt_of_le_of_lt (Nat.cast_nonneg _) hℓlt
  have hqε : 2 ≤ ε * q k := by
    have h1 : 2 / ε < q k := lt_of_lt_of_le hN0 (by exact_mod_cast hk)
    have h2 := (div_lt_iff₀ hε).1 h1
    linarith
  have hN : |(q k : ℝ) / t.size - (μ 0).toReal| < δ := by
    have h1 := hG 1 ⟨hη1.le, le_rfl⟩
    rwa [treeLeafDev_one, hdeg] at h1
  refine absurd hjε (not_lt.2 ?_)
  rcases lt_or_ge (ContinuumTrees.LeafMeasure.leafIndex t j : ℝ) (η * t.size) with hsmall | hbig
  · have hΛη := hG η ⟨le_rfl, hη1.le⟩
    unfold treeLeafDev at hΛη
    have hmono : Lambda t (ContinuumTrees.LeafMeasure.leafIndex t j : ℝ) ≤
        Lambda t ((t.size : ℝ) * η) :=
      Lambda_le_Lambda t (by rw [mul_comm]; exact hsmall.le)
        (mul_lt_of_lt_one_right hz hη1)
    rw [hΛ] at hmono
    have hjΛ : (j : ℝ) + 1 ≤ (Lambda t ((t.size : ℝ) * η) : ℝ) := by exact_mod_cast hmono
    exact leaf_arith_small hμ0 hδ1 hη0 hηε hz (Nat.cast_nonneg _) hsmall (Nat.cast_nonneg j)
      hjΛ hN hΛη
  · have hℓpos : (0 : ℝ) < ContinuumTrees.LeafMeasure.leafIndex t j :=
      lt_of_lt_of_le (mul_pos hη0 hz) hbig
    have hs : (ContinuumTrees.LeafMeasure.leafIndex t j : ℝ) / t.size ∈ Set.Icc η 1 :=
      ⟨(le_div_iff₀ hz).2 hbig, (div_le_one hz).2 hℓlt.le⟩
    have hJ := hG _ hs
    have hval : treeLeafDev (μ 0).toReal t t.size
        ((ContinuumTrees.LeafMeasure.leafIndex t j : ℝ) / t.size) =
          ((j : ℝ) + 1) / (ContinuumTrees.LeafMeasure.leafIndex t j : ℝ) - (μ 0).toReal := by
      unfold treeLeafDev
      rw [mul_div_cancel₀ _ hz.ne', hΛ, Nat.cast_add, Nat.cast_one]
    rw [hval] at hJ
    exact leaf_arith_big hδ1 hδ2 hε hqε hz hℓpos hℓlt.le hN hJ

end BGWLeaves.LeafLimits.Helpers
