module

public import BGWLeaves.MarkedForest.Proof

/-!
# Examples for the leaf-marked forest identity
-/

@[expose] public section

namespace BGWLeaves.MarkedForest.Examples

open BGW
open scoped ENNReal BigOperators

private theorem ofFn_count_zero_eq_filter_card {p : ℕ} (ω : Fin p → ℕ) :
    (List.ofFn ω).count 0 = (Finset.univ.filter fun i : Fin p => ω i = 0).card := by
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

/-- A forest with one component is precisely one tree, with the same size and leaf mark. -/
theorem forestLeafWeight_one_tree (w : ℕ → ℝ≥0∞) (p n : ℕ) :
    forestLeafWeight w 1 p n =
      ∑' t : {t : PlaneTree // t.size = p},
        PlaneTree.weight w t.val * (if t.val.degreeCount 0 = n then 1 else 0) := by
  have hrange : Function.support (fun ts : PlaneForest =>
      if ts.length = 1 ∧ PlaneForest.size ts = p ∧ forestLeafCount ts = n then
        (ts.map (PlaneTree.weight w)).prod else 0) ⊆ Set.range (fun t : PlaneTree => [t]) := by
    intro ts hts
    by_contra hr
    apply hts
    have hnot : ¬ (ts.length = 1 ∧ PlaneForest.size ts = p ∧ forestLeafCount ts = n) := by
      intro h
      obtain ⟨t, rfl⟩ := List.length_eq_one_iff.mp h.1
      exact hr ⟨t, rfl⟩
    exact ite_eq_right hnot
  have hambient : forestLeafWeight w 1 p n =
      ∑' t : PlaneTree,
        (if t.size = p then PlaneTree.weight w t *
          (if t.degreeCount 0 = n then (1 : ℝ≥0∞) else 0) else 0) := by
    unfold forestLeafWeight
    rw [← List.singleton_injective.tsum_eq hrange]
    refine tsum_congr fun t => ?_
    by_cases hp : t.size = p <;> by_cases hn : t.degreeCount 0 = n <;>
      simp [PlaneForest.size, forestLeafCount, hp, hn]
  calc
    forestLeafWeight w 1 p n = _ := hambient
    _ = ∑' t : PlaneTree,
        Set.indicator {t : PlaneTree | t.size = p}
          (fun t => PlaneTree.weight w t *
            (if t.degreeCount 0 = n then (1 : ℝ≥0∞) else 0)) t := by
          apply tsum_congr
          intro t
          by_cases ht : t.size = p <;> simp [Set.indicator, ht]
    _ = _ := (tsum_subtype {t : PlaneTree | t.size = p}
      (fun t => PlaneTree.weight w t *
        (if t.degreeCount 0 = n then (1 : ℝ≥0∞) else 0))).symm

/-- The `j = 1` marked bridge condition is the degree-zero mark in the tree identity. -/
theorem one_root_bridge_set_eq (p n : ℕ) :
    leafMarkedForestBridges 1 p n =
      countBridges p ∩ {ω : Fin p → ℕ | (List.ofFn ω).count 0 = n} := by
  ext ω
  simp only [leafMarkedForestBridges, countBridges, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [← ofFn_count_zero_eq_filter_card]

/-- The one-root specialization of the result, written with tree weights. -/
theorem one_root_result (w : ℕ → ℝ≥0∞) (p n : ℕ) :
    (p : ℝ≥0∞) *
        (∑' t : {t : PlaneTree // t.size = p},
          PlaneTree.weight w t.val * (if t.val.degreeCount 0 = n then 1 else 0)) =
      ∑' ω : Fin p → ℕ,
        (countBridges p ∩ {ω : Fin p → ℕ | (List.ofFn ω).count 0 = n}).indicator
          (fun ω => ∏ i, w (ω i)) ω := by
  rw [← forestLeafWeight_one_tree]
  simpa [one_root_bridge_set_eq] using
    (BGWLeaves.MarkedForest.Proof.result w (j := 1) (by omega) p n)

/-- The `j = 1` instance is exactly BGW's degree-count Kemperman identity for `k = 0`. -/
theorem one_root_agrees_with_degreeCounts (w : ℕ → ℝ≥0∞) (p n : ℕ) :
    (p : ℝ≥0∞) *
        (∑' t : {t : PlaneTree // t.size = p},
          PlaneTree.weight w t.val * (if t.val.degreeCount 0 = n then 1 else 0)) =
      ∑' ω : Fin p → ℕ,
        (countBridges p ∩ {ω : Fin p → ℕ | (List.ofFn ω).count 0 = n}).indicator
          (fun ω => ∏ i, w (ω i)) ω := by
  simpa using
    (BGW.PlaneTree.natCast_mul_tsum_weight_degreeCounts w p 1
      (fun _ : Fin 1 => 0) (fun _ : Fin 1 => n))

/-- The periodic bridge word has two good rotation indices, although those rotations coincide. -/
theorem periodic_word_good_rotations :
    let x : List ℤ := [-1, 0, -1, 0]
    {i : ℕ | i < 4 ∧ BGW.IsForestCode 2 (x.rotate i)} = {1, 3} := by
  dsimp
  have hbad : ¬ BGW.IsForestCode 2 ([-1, 0, -1, 0] : List ℤ) := by
    intro h
    have hprefix := h.2.2 3 (by norm_num)
    norm_num [List.take] at hprefix
  have hgood : BGW.IsForestCode 2 ([0, -1, 0, -1] : List ℤ) := by
    unfold BGW.IsForestCode
    refine ⟨by norm_num, by norm_num, ?_⟩
    intro i hi
    have hi' : i < 4 := by simpa using hi
    have hibound : i ≤ 3 := by omega
    interval_cases i <;> norm_num [List.take]
  ext i
  by_cases hi : i < 4
  · have hibound : i ≤ 3 := by omega
    interval_cases i <;> norm_num [List.rotate, hbad, hgood]
  · simp [hi]
    omega

theorem periodic_word_good_rotation_ncard :
    (let x : List ℤ := [-1, 0, -1, 0]
     {i : ℕ | i < 4 ∧ BGW.IsForestCode 2 (x.rotate i)}).ncard = 2 := by
  rw [periodic_word_good_rotations]
  simp

theorem periodic_word_rotations_coincide :
    ([-1, 0, -1, 0] : List ℤ).rotate 1 =
      ([-1, 0, -1, 0] : List ℤ).rotate 3 := by
  decide

private def twoRootWordA : Fin 3 → ℕ := fun i => if i.val = 0 then 1 else 0
private def twoRootWordB : Fin 3 → ℕ := fun i => if i.val = 1 then 1 else 0
private def twoRootWordC : Fin 3 → ℕ := fun i => if i.val = 2 then 1 else 0

private def twoRootCandidate (k : Fin 3) : Fin 3 → ℕ :=
  if k.val = 0 then twoRootWordA else if k.val = 1 then twoRootWordB else twoRootWordC

private theorem twoRootBridge_set_eq :
    leafMarkedForestBridges 2 3 2 = Set.range twoRootCandidate := by
  classical
  ext ω
  constructor
  · intro h
    have hsum : ω 0 + ω 1 + ω 2 = 1 := by
      have h' := h.1
      simp only [Fin.sum_univ_three] at h'
      omega
    have h0bound : ω 0 ≤ 1 := by omega
    have h1bound : ω 1 ≤ 1 := by omega
    have h2bound : ω 2 ≤ 1 := by omega
    by_cases h0 : ω 0 = 1
    · have h1 : ω 1 = 0 := by omega
      have h2 : ω 2 = 0 := by omega
      refine ⟨0, ?_⟩
      funext i
      fin_cases i <;> simp [twoRootCandidate, twoRootWordA, h0, h1, h2]
    · have h0' : ω 0 = 0 := by omega
      by_cases h1 : ω 1 = 1
      · have h2 : ω 2 = 0 := by omega
        refine ⟨1, ?_⟩
        funext i
        fin_cases i <;> simp [twoRootCandidate, twoRootWordB, h0', h1, h2]
      · have h1' : ω 1 = 0 := by omega
        have h2 : ω 2 = 1 := by omega
        refine ⟨2, ?_⟩
        funext i
        fin_cases i <;> simp [twoRootCandidate, twoRootWordC, h0', h1', h2]
  · rintro ⟨k, rfl⟩
    fin_cases k <;>
      norm_num [leafMarkedForestBridges, twoRootCandidate, twoRootWordA,
        twoRootWordB, twoRootWordC, Fin.sum_univ_three,
        ← ofFn_count_zero_eq_filter_card]

/-- For two roots, three vertices and two leaves, the bridge sum has three equal terms. -/
theorem two_roots_bridge_sum (w : ℕ → ℝ≥0∞) :
    (∑' ω : Fin 3 → ℕ,
      (leafMarkedForestBridges 2 3 2).indicator (fun ω => ∏ i, w (ω i)) ω) =
        (3 : ℝ≥0∞) * w 0 ^ 2 * w 1 := by
  classical
  have hc : Function.Injective twoRootCandidate := by
    intro a b hab
    have h0 := congrFun hab (0 : Fin 3)
    have h1 := congrFun hab (1 : Fin 3)
    have h2 := congrFun hab (2 : Fin 3)
    fin_cases a <;> fin_cases b <;>
      simp_all [twoRootCandidate, twoRootWordA, twoRootWordB, twoRootWordC]
  have hrange : Function.support (fun ω : Fin 3 → ℕ =>
      (leafMarkedForestBridges 2 3 2).indicator (fun ω => ∏ i, w (ω i)) ω) ⊆
        Set.range twoRootCandidate := by
    intro ω hω
    by_contra hnot
    have hA : ω ∈ leafMarkedForestBridges 2 3 2 := by
      by_contra h
      exact hω (Set.indicator_of_notMem h _)
    rw [twoRootBridge_set_eq] at hA
    exact hnot hA
  rw [← hc.tsum_eq hrange]
  simp [twoRootBridge_set_eq, twoRootCandidate, twoRootWordA, twoRootWordB,
    twoRootWordC, Fin.prod_univ_three, Fin.sum_univ_three,
    mul_assoc, mul_left_comm, mul_comm]
  ring

/-- The forest weight for two roots, three vertices and two leaves. -/
theorem two_roots_forestLeafWeight (w : ℕ → ℝ≥0∞) :
    forestLeafWeight w 2 3 2 = (2 : ℝ≥0∞) * w 0 ^ 2 * w 1 := by
  have hm1 := BGWLeaves.MarkedForest.Proof.result w (j := 2) (by omega) 3 2
  rw [two_roots_bridge_sum] at hm1
  have hmul : (3 : ℝ≥0∞) * forestLeafWeight w 2 3 2 =
      (3 : ℝ≥0∞) * ((2 : ℝ≥0∞) * w 0 ^ 2 * w 1) := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using hm1
  exact (ENNReal.mul_right_inj (a := (3 : ℝ≥0∞))
    (by norm_num) (by norm_num)).mp hmul

/-- Both multiplied sides in this example simplify to six copies of the same monomial. -/
theorem two_roots_multiplied_sides (w : ℕ → ℝ≥0∞) :
    (3 : ℝ≥0∞) * forestLeafWeight w 2 3 2 =
        (6 : ℝ≥0∞) * w 0 ^ 2 * w 1 ∧
      (2 : ℝ≥0∞) *
        (∑' ω : Fin 3 → ℕ,
          (leafMarkedForestBridges 2 3 2).indicator (fun ω => ∏ i, w (ω i)) ω) =
        (6 : ℝ≥0∞) * w 0 ^ 2 * w 1 := by
  rw [two_roots_forestLeafWeight, two_roots_bridge_sum]
  constructor
  · calc
      (3 : ℝ≥0∞) * ((2 : ℝ≥0∞) * w 0 ^ 2 * w 1) =
          ((3 : ℝ≥0∞) * 2) * (w 0 ^ 2 * w 1) := by ring
      _ = (6 : ℝ≥0∞) * w 0 ^ 2 * w 1 := by norm_num [mul_assoc]
  · calc
      (2 : ℝ≥0∞) * ((3 : ℝ≥0∞) * w 0 ^ 2 * w 1) =
          ((2 : ℝ≥0∞) * 3) * (w 0 ^ 2 * w 1) := by ring
      _ = (6 : ℝ≥0∞) * w 0 ^ 2 * w 1 := by norm_num [mul_assoc]

end BGWLeaves.MarkedForest.Examples


end
