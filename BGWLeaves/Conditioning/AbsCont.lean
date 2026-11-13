module

public import BGWLeaves.Conditioning.Defs
import BGWLeaves.Conditioning.Basics
import BGW.Tree.Forest

/-!
# Proposition 5.2: absolute continuity at the `k`-th leaf

Proposition 5.2 (`prop:abscon`): `treeLeafTime_ne_top_iff`, `abscon_pending_nonneg`,
`tree_markov_leafCount`, `tree_markov_leafGe`, `abscon_core`, `prop_abscon`.  The theorems are those
stated in `BGWLeaves.Conditioning`; they are exported in namespace
`BGWLeaves.Conditioning.AbsCont` with exactly the types stated there.

Route (purely combinatorial, no strong Markov property of a walk).  A finite plane tree `t` with
`k ≤ λ(t)` is cut at its `k`-th leaf into the prefix word `P = pre k t` of the degree list (up to and
including the `k`-th leaf, `IsPre k P`) and the degree word of a forest of `j = jOf P` trees
(`decomp_tree`, `exists_tree`: parsing of the degree list from the right, and the Łukasiewicz excursion
criterion); the weight is multiplicative, `λ(t) = k + λ(forest)`, and `P ↦ t` is injective
(`pre_of_append`).  The total mass of the forests of `j` finite trees is `1` in the critical case with
`μ 1 ≠ 1` (`fwt_univ`, from `forestLaw_infinite_null`).  Hence `tsum_decomp` reindexes the sum over trees as
a sum over prefixes of `wP P` times a sum over forests, and `markov_general` follows for every set `E` of
admissible forest leaf counts; `tree_markov_leafCount` is `E = {m}`, `tree_markov_leafGe` is `E = [m, ∞)`.
-/

@[expose] public section

namespace BGWLeaves.Conditioning.AbsCont

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open BGWLeaves.Conditioning.Basics
open scoped ENNReal Topology Classical

theorem count_take_succ (ds : List ℕ) (i : ℕ) :
    (ds.take (i + 1)).count 0 = (ds.take i).count 0 + if ds[i]? = some 0 then 1 else 0 := by
  rw [List.take_add_one, List.count_append]
  rcases h : ds[i]? with _ | a
  · simp
  · by_cases ha : a = 0
    · subst ha; simp
    · simp [ha]

theorem count_take_mono (ds : List ℕ) {a b : ℕ} (h : a ≤ b) :
    (ds.take a).count 0 ≤ (ds.take b).count 0 := by
  induction b, h using Nat.le_induction with
  | base => exact le_rfl
  | succ b _ ih => rw [count_take_succ]; omega

theorem count_take_le (ds : List ℕ) (a : ℕ) : (ds.take a).count 0 ≤ ds.count 0 :=
  (List.take_sublist a ds).count_le 0

theorem treeLeafTime_eq_of {t : PlaneTree} {k i : ℕ} (_hk : 1 ≤ k) (h0 : t.degrees[i]? = some 0)
    (hc : (t.degrees.take i).count 0 + 1 = k) : treeLeafTime t k = i := by
  unfold treeLeafTime
  apply le_antisymm
  · refine iInf₂_le i ?_
    rw [count_take_succ]; simp [h0]; omega
  · refine le_iInf₂ fun i' hi' => ?_
    by_contra hlt
    have hlt' : i' < i := by
      have : (i' : ℕ∞) < i := not_le.1 hlt
      exact_mod_cast this
    have := count_take_mono t.degrees (show i' + 1 ≤ i by omega)
    omega

theorem exists_treeLeafTime {t : PlaneTree} {k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ t.degreeCount 0) :
    ∃ i : ℕ, treeLeafTime t k = (i : ℕ∞) ∧ t.degrees[i]? = some 0 ∧ (t.degrees.take i).count 0 + 1 = k := by
  have hex : ∃ i, k ≤ (t.degrees.take (i + 1)).count 0 := by
    refine ⟨t.degrees.length - 1, ?_⟩
    have hpos : 0 < t.degrees.length := by
      rcases Nat.eq_zero_or_pos t.degrees.length with h | h
      · have : t.degrees = [] := List.length_eq_zero_iff.1 h
        have h2 : t.degreeCount 0 = 0 := by simp [PlaneTree.degreeCount, this]
        omega
      · exact h
    rw [show t.degrees.length - 1 + 1 = t.degrees.length by omega, List.take_length]
    exact hkl
  classical
  set T := Nat.find hex with hT
  have hTk : k ≤ (t.degrees.take (T + 1)).count 0 := Nat.find_spec hex
  have hlt : (t.degrees.take T).count 0 < k := by
    rcases Nat.eq_zero_or_pos T with h0 | hpos
    · rw [h0]; simp; omega
    · have := Nat.find_min hex (show T - 1 < T by omega)
      rw [show T - 1 + 1 = T by omega] at this
      omega
  have hel : t.degrees[T]? = some 0 := by
    by_contra hne
    rw [count_take_succ] at hTk
    simp [hne] at hTk
    omega
  have hc : (t.degrees.take T).count 0 + 1 = k := by
    rw [count_take_succ] at hTk
    simp [hel] at hTk
    omega
  exact ⟨T, treeLeafTime_eq_of hk hel hc, hel, hc⟩

theorem treeLeafTime_ne_top_iff (t : PlaneTree) (k : ℕ) :
    treeLeafTime t k ≠ ⊤ ↔ k ≤ t.degreeCount 0 := by
  constructor
  · intro h
    by_contra hk
    apply h
    unfold treeLeafTime
    refine iInf_eq_top.2 fun i => iInf_eq_top.2 fun hi => ?_
    exact absurd (hi.trans (count_take_le _ _)) hk
  · intro hkl
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · have : treeLeafTime t 0 ≤ ((0 : ℕ) : ℕ∞) := by
        unfold treeLeafTime
        exact iInf₂_le (f := fun (i : ℕ) (_ : 0 ≤ (t.degrees.take (i + 1)).count 0) => (i : ℕ∞)) 0 (Nat.zero_le _)
      exact ne_top_of_le_ne_top (by simp) this
    · obtain ⟨i, hi, -⟩ := exists_treeLeafTime hk hkl
      rw [hi]; exact ENat.natCast_ne_top _

theorem lukasiewicz_succ (t : PlaneTree) {i d : ℕ} (h : t.degrees[i]? = some d) :
    t.lukasiewicz (i + 1) = t.lukasiewicz i + ((d : ℤ) - 1) := by
  unfold PlaneTree.lukasiewicz
  have h2 : t.increments[i]? = some ((d : ℤ) - 1) := by
    simp [PlaneTree.increments, h]
  rw [List.take_add_one, h2]
  simp

theorem lukasiewicz_nonneg (t : PlaneTree) {i : ℕ} (hi : i < t.size) :
    0 ≤ t.lukasiewicz i :=
  PlaneTree.sum_take_increments_nonneg t (by simpa using hi)

theorem lukasiewicz_size (t : PlaneTree) : t.lukasiewicz t.size = -1 := by
  unfold PlaneTree.lukasiewicz
  rw [← PlaneTree.length_increments, List.take_length]
  exact PlaneTree.sum_increments t

theorem getElem?_lt_size {t : PlaneTree} {i d : ℕ} (h : t.degrees[i]? = some d) : i < t.size := by
  have := (List.getElem?_eq_some_iff.1 h).1
  simpa using this

/-- The last vertex of a finite tree is a leaf, and the Łukasiewicz path is `0` just before it. -/
theorem last_leaf (t : PlaneTree) :
    t.degrees[t.size - 1]? = some 0 ∧ t.lukasiewicz (t.size - 1) = 0 := by
  have hpos := PlaneTree.size_pos t
  have hlt : t.size - 1 < t.size := by omega
  have hsome : ∃ d, t.degrees[t.size - 1]? = some d := by
    refine ⟨t.degrees[t.size - 1]'(by simpa using hlt), ?_⟩
    exact List.getElem?_eq_getElem _
  obtain ⟨d, hd⟩ := hsome
  have h1 := lukasiewicz_succ t hd
  rw [show t.size - 1 + 1 = t.size by omega, lukasiewicz_size] at h1
  have h2 := lukasiewicz_nonneg t hlt
  have : d = 0 := by omega
  subst this
  exact ⟨hd, by omega⟩

theorem abscon_pending_nonneg (t : PlaneTree) {k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ t.degreeCount 0) :
    0 ≤ treeStopPos t k ∧ (treeStopPos t k = 0 ↔ k = t.degreeCount 0) := by
  obtain ⟨i, hi, h0, hc⟩ := exists_treeLeafTime hk hkl
  have hilt := getElem?_lt_size h0
  have hsucc := lukasiewicz_succ t h0
  have hpos := lukasiewicz_nonneg t hilt
  have hstop : treeStopPos t k = t.lukasiewicz i := by
    unfold treeStopPos; rw [hi]; rfl
  rw [hstop]
  refine ⟨hpos, ⟨fun hz => ?_, fun hkl' => ?_⟩⟩
  · -- W_i = 0 : the tree ends at the leaf
    have hW : t.lukasiewicz (i + 1) = -1 := by rw [hsucc, hz]; simp
    have hi1 : i + 1 = t.size := by
      by_contra hne
      have := lukasiewicz_nonneg t (show i + 1 < t.size by omega)
      omega
    have : (t.degrees.take (i + 1)).count 0 = t.degreeCount 0 := by
      rw [hi1, ← PlaneTree.length_degrees, List.take_length]; rfl
    rw [count_take_succ] at this
    simp [h0] at this
    omega
  · by_contra hne
    have hW1 : 1 ≤ t.lukasiewicz i := by omega
    have hW : 0 ≤ t.lukasiewicz (i + 1) := by rw [hsucc]; omega
    have hi1 : i + 1 < t.size := by
      by_contra hge
      have hi1' : i + 1 = t.size := by omega
      rw [hi1', lukasiewicz_size] at hW; omega
    obtain ⟨hl0, -⟩ := last_leaf t
    have hmono := count_take_mono t.degrees (show i + 1 ≤ t.size - 1 by omega)
    have hlast := count_take_succ t.degrees (t.size - 1)
    rw [show t.size - 1 + 1 = t.size by omega, ← PlaneTree.length_degrees, List.take_length] at hlast
    rw [← PlaneTree.length_degrees] at hmono
    have hc1 := count_take_succ t.degrees i
    simp [h0] at hc1
    simp [hl0] at hlast
    have : t.degreeCount 0 = t.degrees.count 0 := rfl
    rw [PlaneTree.length_degrees] at hmono
    omega


/-- The weight of a finite tree, `∏` of the offspring masses of its outdegrees. -/
noncomputable def wt (μ : PMF ℕ) (t : PlaneTree) : ℝ≥0∞ := PlaneTree.weight (fun d => μ d) t

theorem weight_toMeasure (μ : PMF ℕ) :
    PlaneTree.weight (fun d => μ.toMeasure {d}) = wt μ := by
  funext t
  unfold wt
  congr 1
  funext d
  exact PMF.toMeasure_apply_singleton μ d (measurableSet_singleton _)

theorem measurableSet_finiteTreeEvent (Q : PlaneTree → Prop) :
    MeasurableSet (finiteTreeEvent Q) := by
  have : finiteTreeEvent Q = PlaneTree.toLocallyFinite '' {t | Q t} := by
    ext T
    simp only [finiteTreeEvent, Set.mem_ofPred_eq, Set.mem_image]
    constructor <;> rintro ⟨t, a, b⟩ <;> exact ⟨t, b, a⟩
  rw [this]
  exact ((Set.to_countable _).image _).measurableSet

theorem lintegral_finiteTreeEvent (μ : PMF ℕ) (Q : PlaneTree → Prop) (G : PlaneTree → ℝ≥0∞) :
    ∫⁻ τ in finiteTreeEvent Q, finiteTreeLift G τ ∂bienaymeLaw μ.toMeasure =
      ∑' t, if Q t then G t * wt μ t else 0 := by
  have hS := measurableSet_finiteTreeEvent Q
  have hmeas := measurable_finiteTreeLift G
  rw [← lintegral_indicator hS]
  have hpt : (finiteTreeEvent Q).indicator (finiteTreeLift G) =
      {T : LocallyFinite.Tree | FiniteVertices T}.indicator
        ((finiteTreeEvent Q).indicator (finiteTreeLift G)) := by
    funext T
    by_cases hT : T ∈ finiteTreeEvent Q
    · have : T ∈ {T : LocallyFinite.Tree | FiniteVertices T} := by
        obtain ⟨t, rfl, -⟩ := hT
        exact PlaneTree.finiteVertices_toLocallyFinite t
      simp [Set.indicator_of_mem this]
    · simp only [Set.indicator_apply]; simp [hT]
  rw [hpt, lintegral_indicator measurableSet_finiteVertices]
  have : IsProbabilityMeasure μ.toMeasure := inferInstance
  rw [bienaymeLaw_restrict_finiteVertices, lintegral_sum_measure]
  refine tsum_congr fun t => ?_
  rw [lintegral_smul_measure, lintegral_dirac' _ (hmeas.indicator hS), weight_toMeasure]
  by_cases hQ : Q t
  · have hm : t.toLocallyFinite ∈ finiteTreeEvent Q := ⟨t, rfl, hQ⟩
    simp [Set.indicator_of_mem hm, hQ, finiteTreeLift_toLocallyFinite, mul_comm]
  · have hm : t.toLocallyFinite ∉ finiteTreeEvent Q := by
      rintro ⟨t', ht', hq⟩
      exact hQ (PlaneTree.toLocallyFinite_injective ht' ▸ hq)
    simp [Set.indicator_of_notMem hm, hQ]

/-! ## Forest sums -/

/-- The total weight of the forests (lists of finite trees) with `j` trees and a total number of leaves
in `E`. -/
noncomputable def fwt (μ : PMF ℕ) (E : Set ℕ) (j : ℕ) : ℝ≥0∞ :=
  ∑' ts : PlaneForest, if ts.length = j ∧ forestLeafCount ts ∈ E then (ts.map (wt μ)).prod else 0

theorem tsum_forest_eq_tsum_fin (j : ℕ) (h : PlaneForest → ℝ≥0∞) :
    ∑' ts : PlaneForest, (if ts.length = j then h ts else 0) =
      ∑' f : Fin j → PlaneTree, h (List.ofFn f) := by
  rw [← List.equivSigmaTuple.symm.tsum_eq, ENNReal.tsum_sigma', tsum_eq_single j]
  · simp only [List.equivSigmaTuple_symm_apply, List.length_ofFn, ite_true]
  · intro k hk
    simp [List.equivSigmaTuple_symm_apply, hk]

theorem forestLaw_event (μ : PMF ℕ) (j : ℕ) (Q : (Fin j → PlaneTree) → Prop) :
    forestLaw μ j {F | ∃ ts : Fin j → PlaneTree, Q ts ∧ F = fun i => (ts i).toLocallyFinite} =
      ∑' ts : Fin j → PlaneTree, if Q ts then ∏ i, wt μ (ts i) else 0 := by
  let toLF : (Fin j → PlaneTree) → (Fin j → LocallyFinite.Tree) :=
    fun ts i => (ts i).toLocallyFinite
  have hinj : Function.Injective toLF := by
    intro ts us h
    funext i
    exact PlaneTree.toLocallyFinite_injective (congrFun h i)
  let good : Set (Fin j → PlaneTree) := {ts | Q ts}
  have hevent_eq : {F | ∃ ts : Fin j → PlaneTree, Q ts ∧ F = fun i => (ts i).toLocallyFinite} =
      ⋃ ts : good, ({toLF ts.1} : Set (Fin j → LocallyFinite.Tree)) := by
    ext F
    constructor
    · rintro ⟨ts, hq, rfl⟩
      exact Set.mem_iUnion.mpr ⟨⟨ts, hq⟩, rfl⟩
    · intro hF
      obtain ⟨⟨ts, hq⟩, rfl⟩ := Set.mem_iUnion.mp hF
      exact ⟨ts, hq, rfl⟩
  have hdisj : Pairwise (Function.onFun Disjoint fun ts : good =>
      ({toLF ts.1} : Set (Fin j → LocallyFinite.Tree))) := by
    intro ts us hne
    apply Set.disjoint_singleton.mpr
    intro hEq
    apply hne
    apply Subtype.ext
    exact hinj hEq
  unfold forestLaw
  rw [hevent_eq, measure_iUnion hdisj (fun _ => measurableSet_singleton _)]
  calc
    ∑' ts : good, Measure.pi (fun _ : Fin j => bienaymeLaw μ.toMeasure) {toLF ts.1} =
        ∑' ts : good, ∏ i, wt μ (ts.1 i) := by
      refine tsum_congr fun ts => ?_
      rw [Measure.pi_singleton]
      apply Finset.prod_congr rfl
      intro i _
      rw [bienaymeLaw_toLocallyFinite, weight_toMeasure]
    _ = ∑' ts : Fin j → PlaneTree, if Q ts then ∏ i, wt μ (ts i) else 0 := by
      rw [tsum_subtype good (fun ts => ∏ i, wt μ (ts i))]
      refine tsum_congr fun ts => ?_
      by_cases h : Q ts <;> simp [Set.indicator, good, h]

theorem fwt_eq_forestLaw (μ : PMF ℕ) (E : Set ℕ) (j : ℕ) :
    fwt μ E j = forestLaw μ j {F | ∃ ts : Fin j → PlaneTree, (∑ i, (ts i).degreeCount 0) ∈ E ∧
      F = fun i => (ts i).toLocallyFinite} := by
  rw [forestLaw_event, fwt]
  have : ∀ ts : PlaneForest, (if ts.length = j ∧ forestLeafCount ts ∈ E then
      (ts.map (wt μ)).prod else 0) =
      if ts.length = j then (if forestLeafCount ts ∈ E then (ts.map (wt μ)).prod else 0) else 0 := by
    intro ts; by_cases h1 : ts.length = j <;> by_cases h2 : forestLeafCount ts ∈ E <;> simp [h1, h2]
  simp_rw [this]
  rw [tsum_forest_eq_tsum_fin j (fun ts => if forestLeafCount ts ∈ E then (ts.map (wt μ)).prod else 0)]
  refine tsum_congr fun f => ?_
  simp only [forestLeafCount, List.map_ofFn, List.sum_ofFn, List.prod_ofFn]
  rfl

theorem psi_eq_fwt (μ : PMF ℕ) (m j : ℕ) : psi μ m j = fwt μ {m} j := by
  rw [fwt_eq_forestLaw]
  unfold psi
  congr 1
  ext F
  simp only [forestLeafCountEvent, forestEvent, Set.mem_iUnion, Set.mem_ofPred_eq,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨p, ts, -, h2, rfl⟩
    exact ⟨ts, h2, rfl⟩
  · rintro ⟨ts, h2, rfl⟩
    exact ⟨_, ts, rfl, h2, rfl⟩

theorem psiStar_eq_fwt (μ : PMF ℕ) (m j : ℕ) : psiStar μ m j = fwt μ (Set.Ici m) j := by
  rw [fwt_eq_forestLaw]
  unfold psiStar
  congr 1
  ext F
  simp only [forestLeafGeEvent, forestEvent, Set.mem_ofPred_eq,
    Set.mem_Ici]
  constructor
  · rintro ⟨p, m', hm, ts, -, h2, rfl⟩
    exact ⟨ts, h2 ▸ hm, rfl⟩
  · rintro ⟨ts, h2, rfl⟩
    exact ⟨_, _, h2, ts, rfl, rfl, rfl⟩

theorem fwt_univ {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (j : ℕ) :
    fwt μ Set.univ j = 1 := by
  rw [fwt_eq_forestLaw]
  have hP : IsProbabilityMeasure (forestLaw μ j) := by unfold forestLaw; infer_instance
  apply le_antisymm prob_le_one
  have hnull := forestLaw_infinite_null hc hne j
  calc (1 : ℝ≥0∞) = forestLaw μ j Set.univ := measure_univ.symm
    _ ≤ forestLaw μ j ({F | ∃ i, ¬ FiniteVertices (F i)} ∪
        {F | ∃ ts : Fin j → PlaneTree, (∑ i, (ts i).degreeCount 0) ∈ Set.univ ∧
          F = fun i => (ts i).toLocallyFinite}) := by
      refine measure_mono fun F _ => ?_
      by_cases h : ∃ i, ¬ FiniteVertices (F i)
      · exact Or.inl h
      · right
        push Not at h
        choose ts hts using fun i => (exists_toLocallyFinite_iff (F i)).2 (h i)
        exact ⟨ts, Set.mem_univ _, funext fun i => (hts i).symm⟩
    _ ≤ _ + _ := measure_union_le _ _
    _ = _ := by rw [hnull, zero_add]



/-- `W` of a word of offspring numbers: `∑ (d - 1)`. -/
def wsum (P : List ℕ) : ℤ := (P.map fun d : ℕ => (d : ℤ) - 1).sum

/-- `P` is a prefix of a Łukasiewicz word up to the `k`-th leaf. -/
def IsPre (k : ℕ) (P : List ℕ) : Prop :=
  P.count 0 = k ∧ P.getLast? = some 0 ∧ ∀ i < P.length, 0 ≤ wsum (P.take i)

def jOf (P : List ℕ) : ℕ := (wsum P + 1).toNat

noncomputable def pre (k : ℕ) (t : PlaneTree) : List ℕ :=
  t.degrees.take ((treeLeafTime t k).toNat + 1)

def pathOf (P : List ℕ) : List ℤ := (List.range P.length).map fun i => wsum (P.take i)

theorem wsum_append (P Q : List ℕ) : wsum (P ++ Q) = wsum P + wsum Q := by
  simp [wsum, List.map_append, List.sum_append]

theorem wsum_eq (P : List ℕ) : wsum P = (P.sum : ℤ) - P.length := by
  induction P with
  | nil => simp [wsum]
  | cons d P ih =>
    simp only [wsum, List.map_cons, List.sum_cons, List.length_cons] at ih ⊢
    rw [ih]; push_cast; ring

theorem wsum_take_add_one (P : List ℕ) {i d : ℕ} (h : P[i]? = some d) :
    wsum (P.take (i + 1)) = wsum (P.take i) + ((d : ℤ) - 1) := by
  rw [List.take_add_one, h]
  simp [wsum]

theorem lukasiewicz_eq_wsum (t : PlaneTree) (i : ℕ) :
    t.lukasiewicz i = wsum (t.degrees.take i) := by
  simp [PlaneTree.lukasiewicz, PlaneTree.increments, wsum, List.map_take]

theorem forest_increments_eq (ts : PlaneForest) :
    PlaneForest.increments ts = (PlaneForest.degrees ts).map (fun d : ℕ => (d : ℤ) - 1) := by
  simp [PlaneForest.increments, PlaneForest.degrees, List.map_flatten,
    List.map_map, Function.comp_def]
  rfl

theorem wsum_forest (ts : PlaneForest) : wsum (PlaneForest.degrees ts) = -(ts.length : ℤ) := by
  have := PlaneForest.sum_increments ts
  rw [forest_increments_eq] at this
  exact this

theorem pre_spec {t : PlaneTree} {k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ t.degreeCount 0) :
    IsPre k (pre k t) ∧ treeStopPath t k = pathOf (pre k t) ∧
      pendingTrees t k = jOf (pre k t) := by
  obtain ⟨i, hi, h0, hc⟩ := exists_treeLeafTime hk hkl
  have hT : (treeLeafTime t k).toNat = i := by rw [hi]; rfl
  have hilt := getElem?_lt_size h0
  have hlen : (t.degrees.take (i + 1)).length = i + 1 := by
    rw [List.length_take, PlaneTree.length_degrees]; omega
  have hpre : pre k t = t.degrees.take (i + 1) := by unfold pre; rw [hT]
  have hw : ∀ i' ≤ i, wsum ((t.degrees.take (i + 1)).take i') = t.lukasiewicz i' := by
    intro i' hi'
    rw [lukasiewicz_eq_wsum, List.take_take, min_eq_left (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · rw [hpre]
    refine ⟨?_, ?_, ?_⟩
    · rw [count_take_succ]; simp [h0]; omega
    · rw [List.getLast?_eq_getElem?, hlen, Nat.add_sub_cancel, List.getElem?_take_of_lt (by omega)]
      exact h0
    · intro i' hi'
      rw [hlen] at hi'
      rw [hw i' (by omega)]
      exact lukasiewicz_nonneg t (by omega)
  · rw [hpre]
    unfold treeStopPath pathOf
    rw [hT, hlen]
    refine List.map_congr_left fun i' hi' => ?_
    rw [hw i' (by have := List.mem_range.1 hi'; omega)]
  · rw [hpre]
    unfold pendingTrees treeStopPos jOf
    rw [hT, wsum_take_add_one _ h0, ← lukasiewicz_eq_wsum]
    simp


theorem pre_of_append {t : PlaneTree} {k : ℕ} {P S : List ℕ} (hk : 1 ≤ k) (hP : IsPre k P)
    (ht : t.degrees = P ++ S) :
    k ≤ t.degreeCount 0 ∧ treeLeafTime t k = ((P.length - 1 : ℕ) : ℕ∞) ∧ pre k t = P := by
  obtain ⟨hcount, hlast, -⟩ := hP
  have hPne : P ≠ [] := by
    rintro rfl
    simp at hcount; omega
  have hL : 1 ≤ P.length := List.length_pos_iff.2 hPne
  have hPl : P[P.length - 1]? = some 0 := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have hPfull : P.take (P.length - 1 + 1) = P := by
    rw [show P.length - 1 + 1 = P.length by omega, List.take_length]
  have hc1 := count_take_succ P (P.length - 1)
  rw [hPfull, hPl] at hc1
  simp at hc1
  have hdl : t.degrees[P.length - 1]? = some 0 := by
    rw [ht, List.getElem?_append_left (by omega)]; exact hPl
  have htake : t.degrees.take (P.length - 1) = P.take (P.length - 1) := by
    rw [ht, List.take_append_of_le_length (by omega)]
  have hT : treeLeafTime t k = ((P.length - 1 : ℕ) : ℕ∞) :=
    treeLeafTime_eq_of hk hdl (by rw [htake]; omega)
  refine ⟨?_, hT, ?_⟩
  · have : t.degreeCount 0 = P.count 0 + S.count 0 := by
      show t.degrees.count 0 = _
      rw [ht, List.count_append]
    omega
  · unfold pre
    rw [hT, ht]
    simp only [ENat.toNat_natCast]
    rw [show P.length - 1 + 1 = P.length by omega]
    exact List.take_left' rfl

theorem jOf_cast {k : ℕ} {P : List ℕ} (hP : IsPre k P) : (jOf P : ℤ) = wsum P + 1 := by
  obtain ⟨hcount, hlast, hnn⟩ := hP
  have hPne : P ≠ [] := by
    rintro rfl
    simp at hlast
  have hL : 1 ≤ P.length := List.length_pos_iff.2 hPne
  have hPl : P[P.length - 1]? = some 0 := by
    rw [← List.getLast?_eq_getElem?]; exact hlast
  have h1 := wsum_take_add_one P hPl
  rw [show P.length - 1 + 1 = P.length by omega, List.take_length] at h1
  have h2 := hnn (P.length - 1) (by omega)
  unfold jOf
  rw [Int.toNat_of_nonneg (by omega)]

theorem wsum_def (P : List ℕ) : wsum P = (P.map fun d : ℕ => (d : ℤ) - 1).sum := rfl

theorem exists_tree {k : ℕ} {P : List ℕ} (hP : IsPre k P) (ts : PlaneForest)
    (hl : ts.length = jOf P) : ∃ t : PlaneTree, t.degrees = P ++ PlaneForest.degrees ts := by
  have hj := jOf_cast hP
  obtain ⟨-, -, hnn⟩ := hP
  have hexc : IsTreeExcursion ((P ++ PlaneForest.degrees ts).map fun d : ℕ => (d : ℤ) - 1) := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx
      obtain ⟨d, -, rfl⟩ := List.mem_map.1 hx
      omega
    · have := wsum_append P (PlaneForest.degrees ts)
      rw [wsum_forest] at this
      rw [← wsum_def, this]
      omega
    · intro i hi
      rw [← List.map_take, ← wsum_def]
      by_cases hiP : i < P.length
      · rw [List.take_append_of_le_length hiP.le]
        exact hnn i hiP
      · rw [List.take_append, List.take_of_length_le (by omega), wsum_append]
        have hsz : (PlaneForest.degrees ts).length = PlaneForest.size ts := by
          have := congrArg List.length (forest_increments_eq ts)
          simpa using this.symm
        have hgt := PlaneForest.sum_take_increments_gt ts
          (i := i - P.length) (by
            rw [PlaneForest.length_increments]
            rw [List.length_map] at hi
            simp at hi
            omega)
        rw [forest_increments_eq, ← List.map_take, ← wsum_def] at hgt
        omega
  obtain ⟨t, ht⟩ := PlaneTree.exists_ofIncrements?_eq_some _ hexc
  have hinc := PlaneTree.increments_ofIncrements? ht
  refine ⟨t, ?_⟩
  unfold PlaneTree.increments at hinc
  exact (List.map_injective_iff.2 (fun a b h => by simp at h; omega)) hinc


theorem ofDegrees_append_isSome (P S : List ℕ) :
    (PlaneForest.ofDegrees? (P ++ S)).isSome → (PlaneForest.ofDegrees? S).isSome := by
  induction P with
  | nil => simp
  | cons d P ih =>
    intro h
    rw [List.cons_append, PlaneForest.ofDegrees?_cons] at h
    cases hh : PlaneForest.ofDegrees? (P ++ S) with
    | none => simp [hh] at h
    | some a => exact ih (by simp [hh])

theorem decomp_tree {t : PlaneTree} {k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ t.degreeCount 0) :
    ∃ ts : PlaneForest, ts.length = jOf (pre k t) ∧
      t.degrees = pre k t ++ PlaneForest.degrees ts := by
  obtain ⟨hP, -, -⟩ := pre_spec hk hkl
  have hj := jOf_cast hP
  set P := pre k t with hPdef
  set S := t.degrees.drop ((treeLeafTime t k).toNat + 1) with hS
  have ht : t.degrees = P ++ S := by
    rw [hPdef, hS]; unfold pre; exact (List.take_append_drop _ _).symm
  have h1 : PlaneForest.ofDegrees? t.degrees = some [t] := by
    simpa using PlaneForest.ofDegrees?_degrees [t]
  have h2 : (PlaneForest.ofDegrees? S).isSome :=
    ofDegrees_append_isSome P S (by rw [← ht, h1]; rfl)
  obtain ⟨ts, hts⟩ := Option.isSome_iff_exists.1 h2
  have h3 := PlaneForest.degrees_of_ofDegrees?_eq_some hts
  have h4 := PlaneForest.length_add_sum_of_ofDegrees?_eq_some hts
  refine ⟨ts, ?_, by rw [ht, h3]⟩
  have h5 := PlaneTree.sum_degrees_add_one t
  rw [← PlaneTree.length_degrees] at h5
  rw [ht] at h5
  simp only [List.sum_append, List.length_append] at h5
  have h6 := wsum_eq P
  have : (jOf P : ℤ) = ts.length := by
    rw [hj, h6]; omega
  exact_mod_cast this.symm


/-- The weight of a word of degrees. -/
noncomputable def wP (μ : PMF ℕ) (P : List ℕ) : ℝ≥0∞ := (P.map fun d => μ d).prod

theorem prod_forest_degrees (μ : PMF ℕ) (ts : PlaneForest) :
    ((PlaneForest.degrees ts).map fun d => μ d).prod = (ts.map (wt μ)).prod := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [PlaneForest.degrees_cons, List.map_append, List.prod_append, ih, List.map_cons,
      List.prod_cons]
    rfl

theorem count_forest_degrees (ts : PlaneForest) :
    (PlaneForest.degrees ts).count 0 = forestLeafCount ts := by
  induction ts with
  | nil => simp [forestLeafCount]
  | cons t ts ih =>
    rw [PlaneForest.degrees_cons, List.count_append, ih]
    simp [forestLeafCount, PlaneTree.degreeCount]

theorem tsum_decomp (μ : PMF ℕ) {k : ℕ} (hk : 1 ≤ k) (Ψ : List ℕ → ℕ → ℝ≥0∞) :
    ∑' t : PlaneTree, (if k ≤ t.degreeCount 0 then
        Ψ (pre k t) (t.degreeCount 0 - k) * wt μ t else 0) =
      ∑' P : List ℕ, if IsPre k P then wP μ P *
        ∑' ts : PlaneForest, (if ts.length = jOf P then
          Ψ P (forestLeafCount ts) * (ts.map (wt μ)).prod else 0) else 0 := by
  let s : Set (List ℕ × PlaneForest) := {p | IsPre k p.1 ∧ p.2.length = jOf p.1}
  let ι : s → PlaneTree := fun x => Classical.choose (exists_tree x.2.1 x.1.2 x.2.2)
  have hι : ∀ x, (ι x).degrees = x.1.1 ++ PlaneForest.degrees x.1.2 :=
    fun x => Classical.choose_spec (exists_tree x.2.1 x.1.2 x.2.2)
  have hpre : ∀ x, pre k (ι x) = x.1.1 := fun x => (pre_of_append hk x.2.1 (hι x)).2.2
  have hlam : ∀ x : s, (ι x).degreeCount 0 = k + forestLeafCount x.1.2 := by
    intro x
    show (ι x).degrees.count 0 = _
    rw [hι, List.count_append, count_forest_degrees, x.2.1.1]
  have hwt : ∀ x : s, wt μ (ι x) = wP μ x.1.1 * (x.1.2.map (wt μ)).prod := by
    intro x
    show ((ι x).degrees.map fun d => μ d).prod = _
    rw [hι, List.map_append, List.prod_append, prod_forest_degrees]
    rfl
  have hinj : Function.Injective ι := by
    intro x y h
    have h1 : x.1.1 = y.1.1 := by rw [← hpre x, ← hpre y, h]
    have h2 : PlaneForest.degrees x.1.2 = PlaneForest.degrees y.1.2 := by
      have := hι x
      rw [h, hι y, h1] at this
      exact (List.append_cancel_left this).symm
    exact Subtype.ext (Prod.ext h1 (PlaneForest.degrees_injective h2))
  set f : PlaneTree → ℝ≥0∞ := fun t => if k ≤ t.degreeCount 0 then
        Ψ (pre k t) (t.degreeCount 0 - k) * wt μ t else 0 with hf
  have hsupp : Function.support f ⊆ Set.range ι := by
    intro t ht
    have hkl : k ≤ t.degreeCount 0 := by
      by_contra h
      exact ht (by simp [hf, h])
    obtain ⟨ts, hl, hts⟩ := decomp_tree hk hkl
    obtain ⟨hP, -, -⟩ := pre_spec hk hkl
    refine ⟨⟨(pre k t, ts), hP, hl⟩, ?_⟩
    exact PlaneTree.degrees_injective (by rw [hι]; exact hts.symm)
  rw [← hinj.tsum_eq hsupp]
  have hfx : ∀ x : s, f (ι x) = Ψ x.1.1 (forestLeafCount x.1.2) *
      (wP μ x.1.1 * (x.1.2.map (wt μ)).prod) := by
    intro x
    have hk' : k ≤ (ι x).degreeCount 0 := by rw [hlam]; omega
    simp only [hf, ite_eq_left hk', hpre, hlam, hwt]
    congr 2
    omega
  simp_rw [hfx]
  rw [tsum_subtype s (fun p => Ψ p.1 (forestLeafCount p.2) * (wP μ p.1 * (p.2.map (wt μ)).prod)),
    ENNReal.tsum_prod']
  refine tsum_congr fun P => ?_
  by_cases hP : IsPre k P
  · rw [ite_eq_left hP, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun ts => ?_
    by_cases hl : ts.length = jOf P
    · have : (P, ts) ∈ s := ⟨hP, hl⟩
      simp only [Set.indicator_of_mem this, ite_eq_left hl]
      ring
    · have : (P, ts) ∉ s := fun h => hl h.2
      simp only [Set.indicator_of_notMem this, ite_eq_right hl, mul_zero]
  · rw [ite_eq_right hP]
    refine ENNReal.tsum_eq_zero.2 fun ts => ?_
    have : (P, ts) ∉ s := fun h => hP h.1
    exact Set.indicator_of_notMem this _


theorem markov_general {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {k : ℕ} (hk : 1 ≤ k)
    (E : Set ℕ) (Φ : List ℕ → ℝ≥0∞) :
    ∑' t : PlaneTree, (if k ≤ t.degreeCount 0 ∧ t.degreeCount 0 - k ∈ E then
        Φ (pre k t) * wt μ t else 0) =
      ∑' t : PlaneTree, (if k ≤ t.degreeCount 0 then
        Φ (pre k t) * fwt μ E (jOf (pre k t)) * wt μ t else 0) := by
  have h1 := tsum_decomp μ hk (fun P c => if c ∈ E then Φ P else 0)
  have h2 := tsum_decomp μ hk (fun P _ => Φ P * fwt μ E (jOf P))
  have e1 : ∀ t : PlaneTree, (if k ≤ t.degreeCount 0 ∧ t.degreeCount 0 - k ∈ E then
        Φ (pre k t) * wt μ t else 0) =
      (if k ≤ t.degreeCount 0 then
        (fun P c => if c ∈ E then Φ P else 0) (pre k t) (t.degreeCount 0 - k) * wt μ t else 0) := by
    intro t
    by_cases h1 : k ≤ t.degreeCount 0 <;> by_cases h2 : t.degreeCount 0 - k ∈ E <;> simp [h1, h2]
  have e2 : ∀ t : PlaneTree, (if k ≤ t.degreeCount 0 then
        Φ (pre k t) * fwt μ E (jOf (pre k t)) * wt μ t else 0) =
      (if k ≤ t.degreeCount 0 then
        (fun P (_ : ℕ) => Φ P * fwt μ E (jOf P)) (pre k t) (t.degreeCount 0 - k) * wt μ t
          else 0) := fun t => rfl
  rw [tsum_congr e1, tsum_congr e2, h1, h2]
  refine tsum_congr fun P => ?_
  by_cases hP : IsPre k P
  · simp only [ite_eq_left hP]
    congr 1
    have a1 : ∑' ts : PlaneForest, (if ts.length = jOf P then
        (if forestLeafCount ts ∈ E then Φ P else 0) * (ts.map (wt μ)).prod else 0) =
        Φ P * fwt μ E (jOf P) := by
      unfold fwt
      rw [← ENNReal.tsum_mul_left]
      refine tsum_congr fun ts => ?_
      by_cases h1 : ts.length = jOf P <;> by_cases h2 : forestLeafCount ts ∈ E <;> simp [h1, h2]
    have a2 : ∑' ts : PlaneForest, (if ts.length = jOf P then
        Φ P * fwt μ E (jOf P) * (ts.map (wt μ)).prod else 0) = Φ P * fwt μ E (jOf P) := by
      have := fwt_univ hc hne (jOf P)
      unfold fwt at this
      simp only [Set.mem_univ, and_true] at this
      have e : ∀ ts : PlaneForest, (if ts.length = jOf P then
          Φ P * fwt μ E (jOf P) * (ts.map (wt μ)).prod else 0) =
          Φ P * fwt μ E (jOf P) * (if ts.length = jOf P then (ts.map (wt μ)).prod else 0) := by
        intro ts; by_cases h : ts.length = jOf P <;> simp [h]
      rw [tsum_congr e, ENNReal.tsum_mul_left, this, mul_one]
    rw [a1, a2]
  · simp only [ite_eq_right hP]


theorem markov_core {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {k : ℕ} (hk : 1 ≤ k)
    (E : Set ℕ) (Q : PlaneTree → Prop)
    (hQ : ∀ t : PlaneTree, k ≤ t.degreeCount 0 → (Q t ↔ t.degreeCount 0 - k ∈ E))
    (hQk : ∀ t : PlaneTree, Q t → k ≤ t.degreeCount 0)
    (F : List ℤ → ℝ≥0∞) (g : ℕ → ℝ≥0∞) :
    ∫⁻ τ in finiteTreeEvent Q, finiteTreeLift
        (fun t => F (treeStopPath t k) * g (pendingTrees t k)) τ ∂bienaymeLaw μ.toMeasure =
      ∫⁻ τ in leafGeEvent k, finiteTreeLift
        (fun t => F (treeStopPath t k) * (g (pendingTrees t k) * fwt μ E (pendingTrees t k))) τ
          ∂bienaymeLaw μ.toMeasure := by
  have hlg : leafGeEvent k = finiteTreeEvent (fun t : PlaneTree => k ≤ t.degreeCount 0) := rfl
  rw [lintegral_finiteTreeEvent, hlg, lintegral_finiteTreeEvent]
  calc _ = ∑' t : PlaneTree, (if k ≤ t.degreeCount 0 ∧ t.degreeCount 0 - k ∈ E then
          (fun P => F (pathOf P) * g (jOf P)) (pre k t) * wt μ t else 0) := by
        refine tsum_congr fun t => ?_
        by_cases hkl : k ≤ t.degreeCount 0
        · obtain ⟨-, hpath, hpend⟩ := pre_spec hk hkl
          have hq : Q t ↔ t.degreeCount 0 - k ∈ E := hQ t hkl
          by_cases h : t.degreeCount 0 - k ∈ E
          · simp [hq.2 h, h, hkl, hpath, hpend]
          · simp [h, mt hq.1 h, hkl]
        · have : ¬ Q t := fun h => hkl (hQk t h)
          simp [hkl, this]
    _ = ∑' t : PlaneTree, (if k ≤ t.degreeCount 0 then
          (fun P => F (pathOf P) * g (jOf P)) (pre k t) * fwt μ E (jOf (pre k t)) * wt μ t
            else 0) := markov_general hc hne hk E (fun P => F (pathOf P) * g (jOf P))
    _ = _ := by
        refine tsum_congr fun t => ?_
        by_cases hkl : k ≤ t.degreeCount 0
        · obtain ⟨-, hpath, hpend⟩ := pre_spec hk hkl
          simp only [hkl, ite_true, hpath, hpend]
          ring
        · simp [hkl]


theorem tree_markov_leafCount {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {k : ℕ} (hk : 1 ≤ k)
    (m : ℕ) (F : List ℤ → ℝ≥0∞) (g : ℕ → ℝ≥0∞) :
    ∫⁻ τ in leafCountEvent (k + m), finiteTreeLift
        (fun t => F (treeStopPath t k) * g (pendingTrees t k)) τ ∂bienaymeLaw μ.toMeasure =
      ∫⁻ τ in leafGeEvent k, finiteTreeLift
        (fun t => F (treeStopPath t k) * (g (pendingTrees t k) * psi μ m (pendingTrees t k))) τ
          ∂bienaymeLaw μ.toMeasure := by
  have h := markov_core hc hne hk {m} (fun t : PlaneTree => t.degreeCount 0 = k + m)
    (fun t ht => by simp only [Set.mem_singleton_iff]; omega) (fun t ht => by omega) F g
  simp only [psi_eq_fwt]
  exact h

theorem tree_markov_leafGe {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {k : ℕ} (hk : 1 ≤ k)
    (m : ℕ) (F : List ℤ → ℝ≥0∞) (g : ℕ → ℝ≥0∞) :
    ∫⁻ τ in leafGeEvent (k + m), finiteTreeLift
        (fun t => F (treeStopPath t k) * g (pendingTrees t k)) τ ∂bienaymeLaw μ.toMeasure =
      ∫⁻ τ in leafGeEvent k, finiteTreeLift
        (fun t => F (treeStopPath t k) * (g (pendingTrees t k) * psiStar μ m (pendingTrees t k))) τ
          ∂bienaymeLaw μ.toMeasure := by
  have h := markov_core hc hne hk (Set.Ici m) (fun t : PlaneTree => k + m ≤ t.degreeCount 0)
    (fun t ht => by simp only [Set.mem_Ici]; omega) (fun t ht => by omega) F g
  simp only [psiStar_eq_fwt]
  exact h

theorem psi_div_mul (μ : PMF ℕ) (m j : ℕ) :
    psi μ m j / psiStar μ m j * psiStar μ m j = psi μ m j := by
  by_cases h : psiStar μ m j = 0
  · have : psi μ m j = 0 := le_antisymm ((psi_le_psiStar μ m j).trans h.le) zero_le
    simp [h, this]
  · exact ENNReal.div_mul_cancel h (psiStar_ne_top μ m j)

theorem abscon_core {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k < n) (f : List ℤ → ℝ≥0∞) :
    ∫⁻ τ in leafCountEvent n, finiteTreeLift (fun t => f (treeStopPath t k)) τ
        ∂bienaymeLaw μ.toMeasure =
      ∫⁻ τ in leafGeEvent n, finiteTreeLift
        (fun t => f (treeStopPath t k) *
          (psi μ (n - k) (pendingTrees t k) / psiStar μ (n - k) (pendingTrees t k))) τ
          ∂bienaymeLaw μ.toMeasure := by
  obtain ⟨m, rfl⟩ : ∃ m, n = k + m := ⟨n - k, by omega⟩
  rw [Nat.add_sub_cancel_left]
  have h1 := tree_markov_leafCount hc hne hk1 m f (fun _ => 1)
  have h2 := tree_markov_leafGe hc hne hk1 m f (fun j => psi μ m j / psiStar μ m j)
  simp only [mul_one] at h1
  rw [h1, h2]
  congr 2
  funext τ
  congr 1
  funext t
  rw [psi_div_mul, one_mul]

theorem ennreal_div_div (x y a b : ℝ≥0∞) (hyT : y ≠ ⊤)
    (hxy : y = 0 → x = 0) : (x / a) / (y / b) = (x / y) * (b / a) := by
  by_cases hy : y = 0
  · simp [hy, hxy hy]
  · rw [div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv,
      ENNReal.mul_inv (Or.inl hy) (Or.inl hyT), inv_inv]
    simp only [div_eq_mul_inv]
    ring

theorem finiteTreeLift_const_mul (c : ℝ≥0∞) (G : PlaneTree → ℝ≥0∞) (τ : LocallyFinite.Tree) :
    finiteTreeLift (fun t => c * G t) τ = c * finiteTreeLift G τ := by
  unfold finiteTreeLift
  split_ifs <;> simp

theorem prop_abscon {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n k : ℕ} (hk1 : 1 ≤ k)
    (hkn : k < n) (f : List ℤ → ℝ≥0∞) :
    ∫⁻ τ, finiteTreeLift (fun t => f (treeStopPath t k)) τ
        ∂((bienaymeLaw μ.toMeasure)[|leafCountEvent n]) =
      ∫⁻ τ, finiteTreeLift
        (fun t => f (treeStopPath t k) *
          ((psi μ (n - k) (pendingTrees t k) / psi μ n 1) /
            (psiStar μ (n - k) (pendingTrees t k) / psiStar μ n 1))) τ
        ∂((bienaymeLaw μ.toMeasure)[|leafGeEvent n]) := by
  have core := abscon_core hc hne hk1 hkn f
  have hν : IsProbabilityMeasure (bienaymeLaw μ.toMeasure) := inferInstance
  have hpsi : psi μ n 1 = bienaymeLaw μ.toMeasure (leafCountEvent n) := psi_one μ n
  have hpsis : psiStar μ n 1 = bienaymeLaw μ.toMeasure (leafGeEvent n) := psiStar_one μ n
  have hb0 : psiStar μ n 1 ≠ 0 := by rw [hpsis]; exact leafGeEvent_ne_zero hc hne n
  have hbT : psiStar μ n 1 ≠ ⊤ := psiStar_ne_top μ n 1
  have hcA : (bienaymeLaw μ.toMeasure)[|leafCountEvent n] =
      (psi μ n 1)⁻¹ • (bienaymeLaw μ.toMeasure).restrict (leafCountEvent n) := by
    rw [hpsi]; rfl
  have hcB : (bienaymeLaw μ.toMeasure)[|leafGeEvent n] =
      (psiStar μ n 1)⁻¹ • (bienaymeLaw μ.toMeasure).restrict (leafGeEvent n) := by
    rw [hpsis]; rfl
  rw [hcA, hcB, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul]
  have hxy : ∀ j : ℕ, psiStar μ (n - k) j = 0 → psi μ (n - k) j = 0 := fun j h =>
    le_antisymm ((psi_le_psiStar μ _ j).trans h.le) zero_le
  have hmeasL := measurable_finiteTreeLift
    (fun t : PlaneTree => f (treeStopPath t k) *
      (psi μ (n - k) (pendingTrees t k) / psiStar μ (n - k) (pendingTrees t k)))
  by_cases ha0 : psi μ n 1 = 0
  · have hA0 : bienaymeLaw μ.toMeasure (leafCountEvent n) = 0 := by rw [← hpsi]; exact ha0
    have hI0 : ∫⁻ τ in leafGeEvent n, finiteTreeLift
        (fun t => f (treeStopPath t k) *
          (psi μ (n - k) (pendingTrees t k) / psiStar μ (n - k) (pendingTrees t k))) τ
          ∂bienaymeLaw μ.toMeasure = 0 := by
      rw [← core]
      exact setLIntegral_measure_zero _ _ hA0
    have hae := (lintegral_eq_zero_iff hmeasL).1 hI0
    have hJ0 : ∫⁻ τ in leafGeEvent n, finiteTreeLift
        (fun t => f (treeStopPath t k) *
          ((psi μ (n - k) (pendingTrees t k) / psi μ n 1) /
            (psiStar μ (n - k) (pendingTrees t k) / psiStar μ n 1))) τ
          ∂bienaymeLaw μ.toMeasure = 0 := by
      refine (lintegral_eq_zero_iff (measurable_finiteTreeLift _)).2 ?_
      filter_upwards [hae] with τ hτ
      by_cases hT : ∃ t : PlaneTree, t.toLocallyFinite = τ
      · obtain ⟨t, rfl⟩ := hT
        simp only [finiteTreeLift_toLocallyFinite, Pi.zero_apply] at hτ ⊢
        rcases mul_eq_zero.1 hτ with h | h
        · rw [h, zero_mul]
        · have hψ : psi μ (n - k) (pendingTrees t k) = 0 := by
            rcases ENNReal.div_eq_zero_iff.1 h with h | h
            · exact h
            · exact absurd h (psiStar_ne_top _ _ _)
          rw [hψ]; simp
      · simp [finiteTreeLift, hT]
    rw [hJ0, mul_zero, setLIntegral_measure_zero _ _ hA0, mul_zero]
  · have haT : psi μ n 1 ≠ ⊤ := psi_ne_top μ n 1
    have hfun : (fun τ => finiteTreeLift
        (fun t => f (treeStopPath t k) *
          ((psi μ (n - k) (pendingTrees t k) / psi μ n 1) /
            (psiStar μ (n - k) (pendingTrees t k) / psiStar μ n 1))) τ) =
        fun τ => (psiStar μ n 1 / psi μ n 1) * finiteTreeLift
          (fun t => f (treeStopPath t k) *
            (psi μ (n - k) (pendingTrees t k) / psiStar μ (n - k) (pendingTrees t k))) τ := by
      funext τ
      rw [← finiteTreeLift_const_mul]
      congr 1
      funext t
      rw [ennreal_div_div _ _ _ _ (psiStar_ne_top _ _ _) (hxy _)]
      ring
    rw [hfun, lintegral_const_mul' _ _ (ENNReal.div_ne_top hbT ha0), ← core, ← mul_assoc]
    congr 1
    rw [div_eq_mul_inv, ← mul_assoc, ENNReal.inv_mul_cancel hb0 hbT, one_mul]


end BGWLeaves.Conditioning.AbsCont
