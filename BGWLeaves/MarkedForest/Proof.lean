module

public import BGWLeaves.MarkedForest.Defs

/-!
# Proof of the multiplied leaf-marked forest identity

The proof marks a forest code by its number of `-1` steps. This mark is invariant under cyclic
rotation, so the generalized cycle lemma counts marked bridge words by the same double counting as
for unmarked forests.
-/

@[expose] public section

namespace BGWLeaves.MarkedForest.Proof

open BGW
open scoped ENNReal BigOperators

private def markedForestBridgeWords (j p n : ℕ) : Set (List ℤ) :=
  {x | x ∈ forestBridgeWords j p ∧ wordDegreeCount x 0 = n}

private def markedForestCodes (j p n : ℕ) : Set (List ℤ) :=
  {x | (IsForestCode j x ∧ x.length = p) ∧ wordDegreeCount x 0 = n}

private theorem wordDegreeCount_append (x y : List ℤ) (k : ℕ) :
    wordDegreeCount (x ++ y) k = wordDegreeCount x k + wordDegreeCount y k := by
  simp [wordDegreeCount, List.count_append]

private theorem forestLeafCount_eq_wordDegreeCount (ts : PlaneForest) :
    BGWLeaves.forestLeafCount ts = wordDegreeCount (PlaneForest.increments ts) 0 := by
  induction ts with
  | nil => simp [BGWLeaves.forestLeafCount, PlaneForest.increments, wordDegreeCount]
  | cons t ts ih =>
      change t.degreeCount 0 + forestLeafCount ts =
        wordDegreeCount (t.increments ++ PlaneForest.increments ts) 0
      rw [wordDegreeCount_append, PlaneTree.wordDegreeCount_increments, ih]

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

private theorem forestLeafWeight_eq_tsum_codes (w : ℕ → ℝ≥0∞) {j : ℕ}
    (hj : 1 ≤ j) (p n : ℕ) :
    forestLeafWeight w j p n =
      ∑' x : List ℤ, (markedForestCodes j p n).indicator (walkWeight w) x := by
  have hrange : Function.support ((markedForestCodes j p n).indicator (walkWeight w)) ⊆
      Set.range PlaneForest.increments := by
    intro x hx
    by_contra hr
    apply hx
    have hx' : x ∉ markedForestCodes j p n := by
      intro h
      obtain ⟨ts, ⟨-, hinc⟩, -⟩ :=
        (PlaneForest.isForestCode_iff_existsUnique hj x).mp h.1.1
      exact hr ⟨ts, hinc⟩
    exact Set.indicator_of_notMem hx' _
  unfold forestLeafWeight
  rw [← PlaneForest.increments_injective.tsum_eq hrange]
  refine tsum_congr fun ts => ?_
  by_cases h : ts.length = j ∧ PlaneForest.size ts = p ∧ forestLeafCount ts = n
  · have hmem : PlaneForest.increments ts ∈ markedForestCodes j p n := by
      refine ⟨?_, ?_⟩
      · refine ⟨(PlaneForest.isForestCode_iff_existsUnique hj _).mpr
            ⟨ts, ⟨h.1, rfl⟩, fun ts' hts' => PlaneForest.increments_injective hts'.2⟩,
          ?_⟩
        rw [PlaneForest.length_increments]
        exact h.2.1
      · rw [← forestLeafCount_eq_wordDegreeCount]
        exact h.2.2
    rw [ite_eq_left h, Set.indicator_of_mem hmem, PlaneForest.walkWeight_increments]
  · have hmem : PlaneForest.increments ts ∉ markedForestCodes j p n := by
      rintro ⟨⟨hc, hl⟩, hn⟩
      obtain ⟨ts', ⟨hl', hinc⟩, -⟩ := (PlaneForest.isForestCode_iff_existsUnique hj _).mp hc
      have heq := PlaneForest.increments_injective hinc
      subst ts'
      apply h
      refine ⟨hl', ?_, ?_⟩
      · rwa [PlaneForest.length_increments] at hl
      · exact (forestLeafCount_eq_wordDegreeCount ts).trans hn
    rw [ite_eq_right h, Set.indicator_of_notMem hmem]

private theorem tsum_markedForestBridgeWords_walkWeight (w : ℕ → ℝ≥0∞) (j p n : ℕ) :
    ∑' x : List ℤ, (markedForestBridgeWords j p n).indicator (walkWeight w) x =
      ∑' ω : Fin p → ℕ,
        (leafMarkedForestBridges j p n).indicator (fun ω => ∏ i, w (ω i)) ω := by
  have hcount (ω : Fin p → ℕ) :
      wordDegreeCount (stepWord ω) 0 =
        (Finset.univ.filter fun i : Fin p => ω i = 0).card := by
    rw [wordDegreeCount_stepWord]
    calc
      (List.ofFn ω).count 0
          = (List.finRange p).countP (fun i => decide (ω i = 0)) := by
              rw [List.count_eq_countP, List.ofFn_eq_map, List.countP_map]
              rfl
      _ = (Finset.univ.filter fun i : Fin p => ω i = 0).card := by
            rw [List.countP_eq_length_filter]
            rw [← List.toFinset_card_of_nodup
              ((List.nodup_finRange p).filter (fun i => decide (ω i = 0)))]
            rw [← List.filter_toFinset]
            simp
  have hmem (ω : Fin p → ℕ) :
      stepWord ω ∈ markedForestBridgeWords j p n ↔ ω ∈ leafMarkedForestBridges j p n := by
    rw [markedForestBridgeWords, Set.mem_ofPred_eq, stepWord_mem_forestBridgeWords_iff,
      leafMarkedForestBridges]
    simp only [Set.mem_ofPred_eq]
    rw [hcount]
    rfl
  have hrange : Function.support ((markedForestBridgeWords j p n).indicator (walkWeight w)) ⊆
      Set.range (stepWord (n := p)) := by
    intro x hx
    by_contra hrange
    apply hx
    have hx' : x ∉ markedForestBridgeWords j p n := by
      intro h
      exact hrange (exists_stepWord_eq_of_entries h.1.1 h.1.2.1)
    exact Set.indicator_of_notMem hx' _
  rw [← stepWord_injective.tsum_eq hrange]
  refine tsum_congr fun ω => ?_
  by_cases h : ω ∈ leafMarkedForestBridges j p n
  · rw [Set.indicator_of_mem ((hmem ω).mpr h), Set.indicator_of_mem h, walkWeight_stepWord]
  · rw [Set.indicator_of_notMem (mt (hmem ω).mp h), Set.indicator_of_notMem h]

private theorem natCast_mul_markedBridgeWeight (w : ℕ → ℝ≥0∞) {j : ℕ}
    (hj : 1 ≤ j) (p n : ℕ) :
    (p : ℝ≥0∞) * forestLeafWeight w j p n =
      (j : ℝ≥0∞) * ∑' ω : Fin p → ℕ,
        (leafMarkedForestBridges j p n).indicator (fun ω => ∏ i, w (ω i)) ω := by
  rw [forestLeafWeight_eq_tsum_codes w hj p n]
  let B := markedForestBridgeWords j p n
  let FC := markedForestCodes j p n
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
                simpa only [wordDegreeCount_rotate] using hyB.2⟩
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
            · simpa only [wordDegreeCount_rotate] using hB.2
          simp only [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hy]
      · rw [ite_eq_right hi]
        exact (tsum_congr fun x => Set.indicator_of_notMem (fun h => hi h.2.1) _).trans tsum_zero
    simp_rw [hfib]
    rw [tsum_eq_sum (s := Finset.range p) (fun i hi =>
        by rw [ite_eq_right (by simpa using hi)]),
      Finset.sum_congr rfl (fun i hi => ite_eq_left (Finset.mem_range.mp hi)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  rw [← hb, ha, tsum_markedForestBridgeWords_walkWeight]

theorem result (w : ℕ → ℝ≥0∞) {j : ℕ} (hj : 1 ≤ j) (p n : ℕ) :
    (p : ℝ≥0∞) * forestLeafWeight w j p n =
      (j : ℝ≥0∞) * ∑' ω : Fin p → ℕ,
        (leafMarkedForestBridges j p n).indicator (fun ω => ∏ i, w (ω i)) ω :=
  natCast_mul_markedBridgeWeight w hj p n

end BGWLeaves.MarkedForest.Proof

end
