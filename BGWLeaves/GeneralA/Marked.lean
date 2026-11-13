module

public import BGWLeaves.GeneralA.Defs
public import BGWLeaves.MarkedForest.Defs

/-! Rotation-invariant arbitrary offspring marks in the weighted forest cycle lemma. -/

@[expose] public section

namespace BGWLeaves.GeneralA.Marked

open BGW
open scoped ENNReal BigOperators

noncomputable section

attribute [local instance] Classical.propDecidable

variable (A : Set ℕ)

/-- Number of vertices of the plane tree `t` whose number of children lies in `A`. -/
noncomputable def treeACount (t : PlaneTree) : ℕ := by
  exact t.degrees.countP (fun k => decide (k ∈ A))

/-- Number of letters `z` of the word `x` (Łukasiewicz increments) whose offspring count `z + 1` lies in `A`. -/
noncomputable def wordACount (x : List ℤ) : ℕ := by
  exact x.countP (fun z => decide ((z + 1).toNat ∈ A))

/-- Total number of `A`-marked vertices (number of children in `A`) of a plane forest. -/
noncomputable def forestACount (ts : PlaneForest) : ℕ := (ts.map (treeACount A)).sum

/-- Total weight (product of `w` over the vertices) of the plane forests with `j` trees, `p` vertices and `n` marked vertices. -/
noncomputable def forestAWeight (w : ℕ → ℝ≥0∞) (j p n : ℕ) : ℝ≥0∞ :=
  ∑' ts : PlaneForest,
    if ts.length = j ∧ PlaneForest.size ts = p ∧ forestACount A ts = n then
      (ts.map (PlaneTree.weight w)).prod else 0

/-- Offspring vectors of length `p` with `∑ ω i + j = p` and exactly `n` coordinates in `A`: the marked version of the forest bridge set. -/
noncomputable def markedForestBridges (j p n : ℕ) : Set (Fin p → ℕ) := by
  exact {ω | ∑ i, ω i + j = p ∧ (Finset.univ.filter fun i => ω i ∈ A).card = n}

/-- The number of marked letters is invariant under cyclic rotation. -/
theorem wordACount_rotate (x : List ℤ) (i : ℕ) :
    wordACount A (x.rotate i) = wordACount A x := by
  exact (List.rotate_perm x i).countP_eq _

theorem wordACount_increments (t : PlaneTree) :
    wordACount A t.increments = treeACount A t := by
  simp only [wordACount, treeACount, PlaneTree.increments, List.countP_map]
  congr 1
  funext k
  change decide ((((k : ℤ) - 1) + 1).toNat ∈ A) = decide (k ∈ A)
  simp

theorem wordACount_stepWord {p : ℕ} (ω : Fin p → ℕ) :
    wordACount A (stepWord ω) = (List.ofFn ω).countP (fun k => decide (k ∈ A)) := by
  change wordACount A (List.ofFn ((fun k : ℕ => (k : ℤ) - 1) ∘ ω)) = _
  rw [← List.map_ofFn]
  simp only [wordACount, List.countP_map]
  congr 1
  funext k
  change decide ((((k : ℤ) - 1) + 1).toNat ∈ A) = decide (k ∈ A)
  simp

private def markedForestBridgeWords (j p n : ℕ) : Set (List ℤ) :=
  {x | x ∈ forestBridgeWords j p ∧ wordACount A x = n}

private def markedForestCodes (j p n : ℕ) : Set (List ℤ) :=
  {x | (IsForestCode j x ∧ x.length = p) ∧ wordACount A x = n}

private theorem wordACount_append (x y : List ℤ) :
    wordACount A (x ++ y) = wordACount A x + wordACount A y := by
  simp [wordACount, List.countP_append]

private theorem forestACount_eq_wordACount (ts : PlaneForest) :
    forestACount A ts = wordACount A (PlaneForest.increments ts) := by
  induction ts with
  | nil => simp [forestACount, PlaneForest.increments, wordACount]
  | cons t ts ih =>
      change treeACount A t + forestACount A ts =
        wordACount A (t.increments ++ PlaneForest.increments ts)
      rw [wordACount_append, wordACount_increments, ih]

private theorem rotateRotateSelf {α : Type*} (l : List α) {a b : ℕ}
    (h : (a + b) % l.length = 0) : (l.rotate a).rotate b = l := by
  rw [List.rotate_rotate, ← List.rotate_mod, h, List.rotate_zero]

private theorem modComplementAdd {n i : ℕ} (hi : i < n) : ((n - i) % n + i) % n = 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hi0
  · simp
  · have h1 : (n - i) % n = n - i := Nat.mod_eq_of_lt (by omega)
    rw [h1, show n - i + i = n by omega, Nat.mod_self]

private theorem rotate_mem_forestBridgeWords_local {x : List ℤ} {j p : ℕ}
    (hx : x ∈ forestBridgeWords j p) (i : ℕ) : x.rotate i ∈ forestBridgeWords j p := by
  obtain ⟨hlen, hge, hsum⟩ := hx
  exact ⟨by simp [hlen], fun a ha => hge a (List.mem_rotate.mp ha),
    by rw [(List.rotate_perm x i).sum_eq]; exact hsum⟩

private theorem tsum_indicator_const_ncard_local {S : Set ℕ} (hS : S.Finite) (c : ℝ≥0∞) :
    ∑' i, S.indicator (fun _ => c) i = (S.ncard : ℝ≥0∞) * c := by
  rw [tsum_eq_sum (s := hS.toFinset) (fun i hi =>
      Set.indicator_of_notMem (fun h => hi (hS.mem_toFinset.mpr h)) _),
    Finset.sum_congr rfl (fun i hi => Set.indicator_of_mem (hS.mem_toFinset.mp hi) _),
    Finset.sum_const, nsmul_eq_mul, Set.ncard_eq_toFinset_card S hS]

private theorem forestAWeight_eq_tsum_codes (w : ℕ → ℝ≥0∞) {j : ℕ}
    (hj : 1 ≤ j) (p n : ℕ) :
    forestAWeight A w j p n =
      ∑' x : List ℤ, (markedForestCodes A j p n).indicator (walkWeight w) x := by
  have hrange : Function.support ((markedForestCodes A j p n).indicator (walkWeight w)) ⊆
      Set.range PlaneForest.increments := by
    intro x hx
    by_contra hr
    apply hx
    have hx' : x ∉ markedForestCodes A j p n := by
      intro h
      obtain ⟨ts, ⟨-, hinc⟩, -⟩ :=
        (PlaneForest.isForestCode_iff_existsUnique hj x).mp h.1.1
      exact hr ⟨ts, hinc⟩
    exact Set.indicator_of_notMem hx' _
  unfold forestAWeight
  rw [← PlaneForest.increments_injective.tsum_eq hrange]
  refine tsum_congr fun ts => ?_
  by_cases h : ts.length = j ∧ PlaneForest.size ts = p ∧ forestACount A ts = n
  · have hmem : PlaneForest.increments ts ∈ markedForestCodes A j p n := by
      refine ⟨?_, ?_⟩
      · refine ⟨(PlaneForest.isForestCode_iff_existsUnique hj _).mpr
            ⟨ts, ⟨h.1, rfl⟩, fun ts' hts' => PlaneForest.increments_injective hts'.2⟩,
          ?_⟩
        rw [PlaneForest.length_increments]
        exact h.2.1
      · rw [← forestACount_eq_wordACount]
        exact h.2.2
    rw [ite_eq_left h, Set.indicator_of_mem hmem, PlaneForest.walkWeight_increments]
  · have hmem : PlaneForest.increments ts ∉ markedForestCodes A j p n := by
      rintro ⟨⟨hc, hl⟩, hn⟩
      obtain ⟨ts', ⟨hl', hinc⟩, -⟩ := (PlaneForest.isForestCode_iff_existsUnique hj _).mp hc
      have heq := PlaneForest.increments_injective hinc
      subst ts'
      apply h
      refine ⟨hl', ?_, ?_⟩
      · rwa [PlaneForest.length_increments] at hl
      · exact (forestACount_eq_wordACount A ts).trans hn
    rw [ite_eq_right h, Set.indicator_of_notMem hmem]

private theorem tsum_markedForestBridgeWords_walkWeight (w : ℕ → ℝ≥0∞) (j p n : ℕ) :
    ∑' x : List ℤ, (markedForestBridgeWords A j p n).indicator (walkWeight w) x =
      ∑' ω : Fin p → ℕ,
        (markedForestBridges A j p n).indicator (fun ω => ∏ i, w (ω i)) ω := by
  have hcount (ω : Fin p → ℕ) :
      wordACount A (stepWord ω) = (Finset.univ.filter fun i : Fin p => ω i ∈ A).card := by
    rw [wordACount_stepWord]
    calc
      (List.ofFn ω).countP (fun k => decide (k ∈ A))
          = (List.finRange p).countP (fun i => decide (ω i ∈ A)) := by
              rw [List.ofFn_eq_map, List.countP_map]
              rfl
      _ = _ := by
        rw [List.countP_eq_length_filter]
        rw [← List.toFinset_card_of_nodup
          ((List.nodup_finRange p).filter (fun i => decide (ω i ∈ A)))]
        rw [← List.filter_toFinset]
        simp
  have hmem (ω : Fin p → ℕ) :
      stepWord ω ∈ markedForestBridgeWords A j p n ↔ ω ∈ markedForestBridges A j p n := by
    rw [markedForestBridgeWords, Set.mem_ofPred_eq, stepWord_mem_forestBridgeWords_iff,
      markedForestBridges]
    simp only [Set.mem_ofPred_eq]
    rw [hcount]
    rfl
  have hrange : Function.support ((markedForestBridgeWords A j p n).indicator (walkWeight w)) ⊆
      Set.range (stepWord (n := p)) := by
    intro x hx
    by_contra hrange
    apply hx
    have hx' : x ∉ markedForestBridgeWords A j p n := by
      intro h
      exact hrange (exists_stepWord_eq_of_entries h.1.1 h.1.2.1)
    exact Set.indicator_of_notMem hx' _
  rw [← stepWord_injective.tsum_eq hrange]
  refine tsum_congr fun ω => ?_
  by_cases h : ω ∈ markedForestBridges A j p n
  · rw [Set.indicator_of_mem ((hmem ω).mpr h), Set.indicator_of_mem h, walkWeight_stepWord]
  · rw [Set.indicator_of_notMem (mt (hmem ω).mp h), Set.indicator_of_notMem h]

private theorem natCast_mul_markedBridgeWeight (w : ℕ → ℝ≥0∞) {j : ℕ}
    (hj : 1 ≤ j) (p n : ℕ) :
    (p : ℝ≥0∞) * forestAWeight A w j p n =
      (j : ℝ≥0∞) * ∑' ω : Fin p → ℕ,
        (markedForestBridges A j p n).indicator (fun ω => ∏ i, w (ω i)) ω := by
  rw [forestAWeight_eq_tsum_codes A w hj p n]
  let B := markedForestBridgeWords A j p n
  let FC := markedForestCodes A j p n
  let Q : Set (List ℤ × ℕ) :=
    {q | q.1 ∈ B ∧ q.2 < p ∧ IsForestCode j (q.1.rotate q.2)}
  have ha : ∑' q, Q.indicator (fun q => walkWeight w q.1) q =
      (j : ℝ≥0∞) * ∑' x, B.indicator (walkWeight w) x := by
    rw [ENNReal.tsum_prod', ← ENNReal.tsum_mul_left]
    refine tsum_congr fun x => ?_
    by_cases hx : x ∈ B
    · have hS : ∀ i, Q.indicator (fun q => walkWeight w q.1) (x, i) =
          {i : ℕ | i < x.length ∧ IsForestCode j (x.rotate i)}.indicator
            (fun _ => walkWeight w x) i := by
        intro i
        by_cases hi : i < x.length ∧ IsForestCode j (x.rotate i)
        · rw [Set.indicator_of_mem (show (x, i) ∈ Q from
              ⟨hx, by rw [← hx.1.1]; exact hi.1, hi.2⟩),
            Set.indicator_of_mem (show i ∈ {i : ℕ | i < x.length ∧
              IsForestCode j (x.rotate i)} from hi)]
        · rw [Set.indicator_of_notMem (show (x, i) ∉ Q from fun h =>
              hi ⟨by rw [hx.1.1]; exact h.2.1, h.2.2⟩),
            Set.indicator_of_notMem (show i ∉ {i : ℕ | i < x.length ∧
              IsForestCode j (x.rotate i)} from hi)]
      simp_rw [hS]
      have hfin : {i : ℕ | i < x.length ∧ IsForestCode j (x.rotate i)}.Finite :=
        (Set.finite_Iio x.length).subset fun i hi => hi.1
      obtain ⟨⟨hlen, hge, hsum⟩, hmark⟩ := hx
      rw [tsum_indicator_const_ncard_local hfin,
        ncard_rotate_isForestCode hge hj hsum,
        Set.indicator_of_mem (show x ∈ B from ⟨⟨hlen, hge, hsum⟩, hmark⟩)]
    · have hzero : ∀ i : ℕ, Q.indicator (fun q => walkWeight w q.1) (x, i) = 0 :=
        fun i => Set.indicator_of_notMem (fun h => hx h.1) _
      simp [hzero, Set.indicator_of_notMem hx]
  have hb : ∑' q, Q.indicator (fun q => walkWeight w q.1) q =
      (p : ℝ≥0∞) * ∑' y, FC.indicator (walkWeight w) y := by
    rw [ENNReal.tsum_prod', ENNReal.tsum_comm]
    have hfib : ∀ i : ℕ, ∑' x, Q.indicator (fun q => walkWeight w q.1) (x, i) =
        if i < p then ∑' y, FC.indicator (walkWeight w) y else 0 := by
      intro i
      by_cases hi : i < p
      · rw [ite_eq_left hi]
        have hg : Function.Injective (fun y : List ℤ => y.rotate ((p - i) % p)) :=
          List.rotate_injective _
        have hrange : Function.support (fun x => Q.indicator (fun q => walkWeight w q.1)
            (x, i)) ⊆ Set.range (fun y : List ℤ => y.rotate ((p - i) % p)) := by
          intro x hx
          by_contra hr
          apply hx
          refine Set.indicator_of_notMem (fun hq => hr ⟨x.rotate i, ?_⟩) _
          have hlen : x.length = p := hq.1.1.1
          exact rotateRotateSelf x (by rw [hlen, add_comm]; exact modComplementAdd hi)
        rw [← hg.tsum_eq hrange]
        refine tsum_congr fun y => ?_
        by_cases hy : y ∈ FC
        · have hyFC : y ∈ FC := hy
          rcases hy with ⟨⟨hycode, hylen⟩, hymark⟩
          have hyB : y ∈ B := by
            exact ⟨⟨hylen, hycode.1, hycode.2.1⟩, hymark⟩
          have hmem : (y.rotate ((p - i) % p), i) ∈ Q := by
            refine ⟨?_, hi, ?_⟩
            · exact ⟨rotate_mem_forestBridgeWords_local hyB.1 _, by
                simpa only [wordACount_rotate] using hyB.2⟩
            · show IsForestCode j ((y.rotate ((p - i) % p)).rotate i)
              rw [rotateRotateSelf y (by rw [hylen]; exact modComplementAdd hi)]
              exact hycode
          simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hyFC]
          exact walkWeight_rotate w y _
        · have hmem : (y.rotate ((p - i) % p), i) ∉ Q := by
            rintro ⟨hB, -, hfc⟩
            have hlen : y.length = p := by simpa using hB.1.1
            apply hy
            refine ⟨⟨?_, hlen⟩, ?_⟩
            · have hrotate := rotateRotateSelf y (a := (p - i) % p) (b := i)
                (by rw [hlen]; exact modComplementAdd hi)
              rw [hrotate] at hfc
              exact hfc
            · simpa only [wordACount_rotate] using hB.2
          simp only [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hy]
      · rw [ite_eq_right hi]
        exact (tsum_congr fun x => Set.indicator_of_notMem (fun h => hi h.2.1) _).trans tsum_zero
    simp_rw [hfib]
    rw [tsum_eq_sum (s := Finset.range p) (fun i hi =>
        by rw [ite_eq_right (by simpa using hi)]),
      Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_range.mp hi)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← hb, ha, tsum_markedForestBridgeWords_walkWeight]

theorem natCast_mul_forestAWeight (w : ℕ → ℝ≥0∞) {j : ℕ} (hj : 1 ≤ j) (p n : ℕ) :
    (p : ℝ≥0∞) * forestAWeight A w j p n =
      (j : ℝ≥0∞) * ∑' ω : Fin p → ℕ,
        (markedForestBridges A j p n).indicator (fun ω => ∏ i, w (ω i)) ω :=
  natCast_mul_markedBridgeWeight A w hj p n


end

end BGWLeaves.GeneralA.Marked
