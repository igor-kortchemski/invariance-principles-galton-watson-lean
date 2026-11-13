/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Probability.RealWalkExits
public import BGW.Probability.RealWalkMaximal
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Expected exit counts and close-pair probabilities

The expected number of restart exits is controlled by splitting exits according to their gap
from the previous exit.  Far exits inject into time blocks.  Close successive exits are charged
to the preceding exit by finite-prefix determination and fresh-start independence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators

namespace BGW.Probability.RealWalk

private lemma index_le_exitTimes {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {j : ℕ}
    (hj : j ≤ M + 1) : j ≤ exitTimes M r ω j := by
  induction j with
  | zero => simp [exitTimes]
  | succ j ih =>
      by_cases hprev : exitTimes M r ω j ≤ M
      · have hlt := exitTimes_lt_succ hprev
        have hle := ih (by omega)
        omega
      · have hs : exitTimes M r ω (j + 1) = M + 1 := by
          simp [exitTimes, hprev]
        omega

private lemma exitTimes_lt_of_lt {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {i j : ℕ}
    (hij : i < j) (hj : exitTimes M r ω j ≤ M) :
    exitTimes M r ω i < exitTimes M r ω j := by
  induction j generalizing i with
  | zero => omega
  | succ j ih =>
      have hprev : exitTimes M r ω j ≤ M := by
        by_contra! hn
        simp [exitTimes, not_le_of_gt hn] at hj
      have hlast := exitTimes_lt_succ hprev
      by_cases hi : i = j
      · simpa [hi] using hlast
      · exact (ih (by omega) hprev).trans hlast

private lemma measurableSet_actualExit (M : ℕ) (r : ℝ) (j : ℕ) :
    MeasurableSet {ω : ℕ → ℝ | 1 ≤ j ∧ exitTimes M r ω j ≤ M} := by
  by_cases hj : 1 ≤ j
  · simpa [hj] using measurableSet_le (measurable_exitTimes M r j) measurable_const
  · simp [hj]

private lemma integral_card_filter (μ : Measure (ℕ → ℝ)) [IsProbabilityMeasure μ]
    (s : Finset ℕ) (P : ℕ → (ℕ → ℝ) → Prop)
    (d : ∀ ω, DecidablePred fun j => P j ω) (hP : ∀ j, MeasurableSet {ω | P j ω}) :
    ∫ ω, (((@Finset.filter ℕ (fun j => P j ω) (d ω) s).card : ℕ) : ℝ) ∂μ =
      ∑ j ∈ s, μ.real {ω | P j ω} := by
  classical
  have hpoint : (fun ω =>
      (((@Finset.filter ℕ (fun j => P j ω) (d ω) s).card : ℕ) : ℝ)) = fun ω =>
      ∑ j ∈ s, {ω' | P j ω'}.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp [Set.indicator]
  rw [hpoint, integral_finsetSum s fun j _ => (integrable_const 1).indicator (hP j)]
  apply Finset.sum_congr rfl
  intro j hj
  exact integral_indicator_one (hP j)

private lemma integrable_card_filter (μ : Measure (ℕ → ℝ)) [IsProbabilityMeasure μ]
    (s : Finset ℕ) (P : ℕ → (ℕ → ℝ) → Prop)
    (d : ∀ ω, DecidablePred fun j => P j ω) (hP : ∀ j, MeasurableSet {ω | P j ω}) :
    Integrable (fun ω =>
      (((@Finset.filter ℕ (fun j => P j ω) (d ω) s).card : ℕ) : ℝ)) μ := by
  classical
  have hpoint : (fun ω =>
      (((@Finset.filter ℕ (fun j => P j ω) (d ω) s).card : ℕ) : ℝ)) = fun ω =>
      ∑ j ∈ s, {ω' | P j ω'}.indicator (fun _ => (1 : ℝ)) ω := by
    funext ω
    simp [Set.indicator]
  rw [hpoint]
  exact integrable_finsetSum s fun j _ => (integrable_const 1).indicator (hP j)

private lemma integral_exitCount_eq_sum (ν : ProbabilityMeasure ℝ) (M : ℕ) (r : ℝ) :
    ∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ)) =
      ∑ j ∈ Finset.range (M + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real
          {ω | 1 ≤ j ∧ exitTimes M r ω j ≤ M} := by
  classical
  simpa only [exitCount, Finset.filter_congr_decidable] using
    (integral_card_filter (iidLaw ν : Measure (ℕ → ℝ)) (Finset.range (M + 1)) _
      (fun _ => inferInstance) (measurableSet_actualExit M r))

private noncomputable def closePairAt (M : ℕ) (r : ℝ) (l j : ℕ) :
    Set (ℕ → ℝ) := {ω | 1 ≤ j ∧ exitTimes M r ω (j + 1) ≤ M ∧
    exitTimes M r ω (j + 1) - exitTimes M r ω j ≤ l}

private lemma measurableSet_closePairAt (M : ℕ) (r : ℝ) (l j : ℕ) :
    MeasurableSet (closePairAt M r l j) := by
  by_cases hj : 1 ≤ j
  · have heq : closePairAt M r l j = {ω | exitTimes M r ω (j + 1) ≤ M} ∩
        {ω | exitTimes M r ω (j + 1) - exitTimes M r ω j ≤ l} := by
      ext ω
      simp [closePairAt, hj]
    rw [heq]
    exact (measurableSet_le (measurable_exitTimes M r (j + 1)) measurable_const).inter
      (measurableSet_le ((measurable_exitTimes M r (j + 1)).sub
        (measurable_exitTimes M r j)) measurable_const)
  · simp [closePairAt, hj, MeasurableSet.empty]

private noncomputable def shiftedPairAt (M : ℕ) (r : ℝ) (l j k : ℕ) :
    Set (ℕ → ℝ) := {ω | exitTimes M r ω j = k} ∩ shift k ⁻¹' maxExceed l r

private lemma measurableSet_shiftedPairAt (M : ℕ) (r : ℝ) (l j k : ℕ) (hk : k ≤ M) :
    MeasurableSet (shiftedPairAt M r l j k) := by
  obtain ⟨A, hA, heq⟩ := exists_prefixSet_exitTimes M r j k hk
  rw [shiftedPairAt, heq]
  exact (measurable_prefixVec k hA).inter
    (measurable_shift k (measurableSet_maxExceed l r))

private lemma measureReal_shiftedPairAt (ν : ProbabilityMeasure ℝ) (M : ℕ) (r : ℝ)
    (l j k : ℕ) (hk : k ≤ M) :
    (iidLaw ν : Measure (ℕ → ℝ)).real (shiftedPairAt M r l j k) =
      (iidLaw ν : Measure (ℕ → ℝ)).real {ω | exitTimes M r ω j = k} *
        maxTail ν l r := by
  obtain ⟨A, hA, heq⟩ := exists_prefixSet_exitTimes M r j k hk
  rw [shiftedPairAt, heq]
  simp only [measureReal_def, measure_prefix_inter_shift ν k hA
    (measurableSet_maxExceed l r), ENNReal.toReal_mul, maxTail]

private lemma nextExit_exceed {M : ℕ} {r : ℝ} {ω : ℕ → ℝ} {a : ℕ}
    (h : nextExit M r ω a ≤ M) :
    r < |partialSum ω (nextExit M r ω a) - partialSum ω a| := by
  classical
  unfold nextExit at h ⊢
  split_ifs at h ⊢ with hex
  · exact (Nat.find_spec hex).2.2
  · omega

private lemma closePairAt_subset_iUnion (M : ℕ) (r : ℝ) (l j : ℕ) :
    closePairAt M r l j ⊆ ⋃ k ∈ Finset.range (M + 1), shiftedPairAt M r l j k := by
  intro ω hω
  rcases hω with ⟨hj, hnext, hgap⟩
  have hk : exitTimes M r ω j ≤ M := by
    by_contra! hn
    simp [exitTimes, not_le_of_gt hn] at hnext
  have hshift := exitTimes_succ_eq_shift hk (rfl : exitTimes M r ω j = exitTimes M r ω j)
  let i := nextExit (M - exitTimes M r ω j) r (shift (exitTimes M r ω j) ω) 0
  have hiM : i ≤ M - exitTimes M r ω j := by
    dsimp [i]
    omega
  have hi : i ≤ l := by
    dsimp [i]
    omega
  have hex := nextExit_exceed hiM
  apply Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  refine ⟨rfl, ?_⟩
  refine ⟨i, hi, ?_⟩
  simpa [partialSum] using hex

private lemma measureReal_actualExit_eq_sum (ν : ProbabilityMeasure ℝ) (M : ℕ) (r : ℝ)
    (j : ℕ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | exitTimes M r ω j ≤ M} =
      ∑ k ∈ Finset.range (M + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real {ω | exitTimes M r ω j = k} := by
  have hset : {ω : ℕ → ℝ | exitTimes M r ω j ≤ M} =
      ⋃ k ∈ Finset.range (M + 1), {ω | exitTimes M r ω j = k} := by
    ext ω
    constructor
    · intro h
      exact Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le h)) rfl
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨k, h⟩
      rcases Set.mem_iUnion.mp h with ⟨hk, heq⟩
      exact heq.le.trans (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
  have hdisj : Set.PairwiseDisjoint (↑(Finset.range (M + 1)))
      (fun k => {ω : ℕ → ℝ | exitTimes M r ω j = k}) := by
    intro a ha b hb hab
    rw [Function.onFun, Set.disjoint_left]
    intro ω hωa hωb
    exact hab (hωa ▸ hωb)
  have hmeas : ∀ k ∈ Finset.range (M + 1),
      MeasurableSet {ω : ℕ → ℝ | exitTimes M r ω j = k} := by
    intro k hk
    exact measurable_exitTimes M r j (measurableSet_singleton k)
  rw [hset, measureReal_biUnion_finset hdisj hmeas]

private lemma measureReal_closePairAt_le (ν : ProbabilityMeasure ℝ) (M : ℕ) (r : ℝ)
    (l j : ℕ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real (closePairAt M r l j) ≤
      (iidLaw ν : Measure (ℕ → ℝ)).real {ω | 1 ≤ j ∧ exitTimes M r ω j ≤ M} *
        maxTail ν l r := by
  by_cases hj : 1 ≤ j
  swap
  · simp [closePairAt, hj]
  calc
    _ ≤ (iidLaw ν : Measure (ℕ → ℝ)).real
        (⋃ k ∈ Finset.range (M + 1), shiftedPairAt M r l j k) :=
      measureReal_mono (closePairAt_subset_iUnion M r l j) (measure_ne_top _ _)
    _ ≤ ∑ k ∈ Finset.range (M + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real (shiftedPairAt M r l j k) :=
      measureReal_biUnion_finset_le _ _
    _ = ∑ k ∈ Finset.range (M + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real {ω | exitTimes M r ω j = k} *
          maxTail ν l r := by
      apply Finset.sum_congr rfl
      intro k hk
      exact measureReal_shiftedPairAt ν M r l j k (Nat.le_of_lt_succ (Finset.mem_range.mp hk))
    _ = (∑ k ∈ Finset.range (M + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real {ω | exitTimes M r ω j = k}) *
          maxTail ν l r := by rw [Finset.sum_mul]
    _ = _ := by rw [← measureReal_actualExit_eq_sum]; simp [hj]

private lemma measureReal_closeExit_aux (ν : ProbabilityMeasure ℝ) (M : ℕ) (r : ℝ)
    (l : ℕ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | closeExit M r l ω} ≤
      (∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ))) *
        maxTail ν l r := by
  have hset : {ω : ℕ → ℝ | closeExit M r l ω} =
      ⋃ j ∈ Finset.range (M + 1), closePairAt M r l j := by
    ext ω
    constructor
    · rintro ⟨j, hj, hnext, hgap⟩
      have hjM : j ≤ M := by
        by_contra! hjM
        have hbase : M < exitTimes M r ω (M + 1) := by
          have h := index_le_exitTimes (M := M) (r := r) (ω := ω) (j := M + 1) le_rfl
          omega
        have hprev : M < exitTimes M r ω j := by
          obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le (show M + 1 ≤ j by omega)
          by_cases hi : i = 0
          · simpa [hi] using hbase
          · have heq := exitTimes_eq_sentinel hbase (i := i) (by omega)
            rw [heq]
            omega
        simp [exitTimes, not_le_of_gt hprev] at hnext
      exact Set.mem_biUnion (Finset.mem_range.mpr (Nat.lt_succ_of_le hjM))
        ⟨hj, hnext, hgap⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨j, h⟩
      rcases Set.mem_iUnion.mp h with ⟨hj, hclose⟩
      exact ⟨j, hclose⟩
  rw [hset, integral_exitCount_eq_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (M + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real (closePairAt M r l j) :=
      measureReal_biUnion_finset_le _ _
    _ ≤ ∑ j ∈ Finset.range (M + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real {ω | 1 ≤ j ∧ exitTimes M r ω j ≤ M} *
          maxTail ν l r := by
      apply Finset.sum_le_sum
      intro j hj
      exact measureReal_closePairAt_le ν M r l j
    _ = (∑ j ∈ Finset.range (M + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real {ω | 1 ≤ j ∧ exitTimes M r ω j ≤ M}) *
          maxTail ν l r := by rw [Finset.sum_mul]
    _ = _ := rfl

/-- Close pairs are bounded by the expected exit count times the fresh-start tail. -/
theorem measure_closeExit_le (ν : ProbabilityMeasure ℝ) {M : ℕ} {r : ℝ} (hr : 0 < r)
    (l : ℕ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | closeExit M r l ω} ≤
      (∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ))) *
        maxTail ν l r := by
  have _ : 0 < r := hr
  exact measureReal_closeExit_aux ν M r l

private noncomputable def farExitCount (M : ℕ) (r : ℝ) (L : ℕ) (ω : ℕ → ℝ) : ℕ :=
  ((Finset.range (M + 1)).filter fun j => 1 ≤ j ∧ exitTimes M r ω j ≤ M ∧
    (j = 1 ∨ L < exitTimes M r ω j - exitTimes M r ω (j - 1))).card

private noncomputable def closePairCount (M : ℕ) (r : ℝ) (L : ℕ) (ω : ℕ → ℝ) : ℕ :=
  ((Finset.range (M + 1)).filter fun j => 2 ≤ j ∧ exitTimes M r ω j ≤ M ∧
    exitTimes M r ω j - exitTimes M r ω (j - 1) ≤ L).card

private lemma measurableSet_farExit (M : ℕ) (r : ℝ) (L j : ℕ) :
    MeasurableSet {ω : ℕ → ℝ | 1 ≤ j ∧ exitTimes M r ω j ≤ M ∧
      (j = 1 ∨ L < exitTimes M r ω j - exitTimes M r ω (j - 1))} := by
  by_cases hj : 1 ≤ j
  · have hone : MeasurableSet {ω : ℕ → ℝ | j = 1} := by
      by_cases h : j = 1
      · simp [h]
      · simp [h]
    have hactual : MeasurableSet {ω : ℕ → ℝ | exitTimes M r ω j ≤ M} :=
      measurableSet_le (measurable_exitTimes M r j) measurable_const
    have hgap : MeasurableSet {ω : ℕ → ℝ |
        L < exitTimes M r ω j - exitTimes M r ω (j - 1)} :=
      measurableSet_lt measurable_const ((measurable_exitTimes M r j).sub
        (measurable_exitTimes M r (j - 1)))
    have hmeas := hactual.inter (hone.union hgap)
    have heq : {ω : ℕ → ℝ | 1 ≤ j ∧ exitTimes M r ω j ≤ M ∧
        (j = 1 ∨ L < exitTimes M r ω j - exitTimes M r ω (j - 1))} =
        {ω | exitTimes M r ω j ≤ M} ∩
          ({ω : ℕ → ℝ | j = 1} ∪
            {ω | L < exitTimes M r ω j - exitTimes M r ω (j - 1)}) := by
      ext ω
      simp [hj]
    rw [heq]
    exact hmeas
  · simp [hj]

private lemma measurableSet_closePairCount (M : ℕ) (r : ℝ) (L j : ℕ) :
    MeasurableSet {ω : ℕ → ℝ | 2 ≤ j ∧ exitTimes M r ω j ≤ M ∧
      exitTimes M r ω j - exitTimes M r ω (j - 1) ≤ L} := by
  by_cases hj : 2 ≤ j
  · have heq : {ω : ℕ → ℝ | 2 ≤ j ∧ exitTimes M r ω j ≤ M ∧
        exitTimes M r ω j - exitTimes M r ω (j - 1) ≤ L} =
        {ω | exitTimes M r ω j ≤ M} ∩
          {ω | exitTimes M r ω j - exitTimes M r ω (j - 1) ≤ L} := by
      ext ω
      simp [hj]
    rw [heq]
    exact (measurableSet_le (measurable_exitTimes M r j) measurable_const).inter
      (measurableSet_le ((measurable_exitTimes M r j).sub
        (measurable_exitTimes M r (j - 1))) measurable_const)
  · simp [hj]

private lemma nat_div_lt_of_add_lt {a b L : ℕ} (hL : 1 ≤ L) (h : a + L < b) :
    a / L < b / L := by
  apply (Nat.div_lt_iff_lt_mul (by omega : 0 < L)).2
  have hbdiv := Nat.div_add_mod b L
  have hbmod := Nat.mod_lt b (by omega : 0 < L)
  nlinarith

private lemma farExitCount_le (M : ℕ) (r : ℝ) (L : ℕ) (hL : 1 ≤ L) (ω : ℕ → ℝ) :
    farExitCount M r L ω ≤ M / L + 1 := by
  classical
  let s := (Finset.range (M + 1)).filter fun j => 1 ≤ j ∧ exitTimes M r ω j ≤ M ∧
    (j = 1 ∨ L < exitTimes M r ω j - exitTimes M r ω (j - 1))
  have hstrict : ∀ i ∈ s, ∀ j ∈ s, i < j →
      exitTimes M r ω i / L < exitTimes M r ω j / L := by
    intro i hi j hj hij
    simp only [s, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff] at hi hj
    have hj0 : j ≠ 0 := by omega
    have hj1 : j ≠ 1 := by
      intro heq
      subst j
      have := hi.2.1
      omega
    have hprevlt : j - 1 < j := by omega
    have hprev : exitTimes M r ω (j - 1) ≤ M :=
      (exitTimes_lt_of_lt hprevlt hj.2.2.1).le.trans hj.2.2.1
    have hile : exitTimes M r ω i ≤ exitTimes M r ω (j - 1) := by
      by_cases heq : i = j - 1
      · rw [heq]
      · exact (exitTimes_lt_of_lt (by omega) hprev).le
    have hgap := hj.2.2.2.resolve_left hj1
    apply nat_div_lt_of_add_lt hL
    omega
  change s.card ≤ M / L + 1
  have hcard : s.card ≤ (Finset.range (M / L + 1)).card := by
    apply Finset.card_le_card_of_injOn (fun j => exitTimes M r ω j / L)
    · intro j hj
      simp only [Finset.mem_coe, s, Finset.mem_filter, Finset.mem_range,
        Nat.lt_succ_iff] at hj ⊢
      exact Nat.div_le_div_right hj.2.2.1
    · intro i hi j hj heq
      rcases lt_trichotomy i j with hij | hij | hij
      · exact ((hstrict i hi j hj hij).ne heq).elim
      · exact hij
      · exact ((hstrict j hj i hi hij).ne heq.symm).elim
  simpa using hcard

private lemma exitCount_eq_far_add_close (M : ℕ) (r : ℝ) (L : ℕ) (ω : ℕ → ℝ) :
    exitCount M r ω = farExitCount M r L ω + closePairCount M r L ω := by
  classical
  simp only [exitCount, farExitCount, closePairCount]
  have hcard (P : ℕ → Prop) [DecidablePred P] :
      ((Finset.range (M + 1)).filter P).card =
        ∑ j ∈ Finset.range (M + 1), if P j then 1 else 0 := by simp
  rw [hcard, hcard, hcard, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hj0 : j = 0
  · simp [hj0]
  by_cases hj1 : j = 1
  · by_cases h : exitTimes M r ω j ≤ M <;> simp [hj1]
  have hj2 : 2 ≤ j := by omega
  by_cases ha : exitTimes M r ω j ≤ M
  · by_cases hg : L < exitTimes M r ω j - exitTimes M r ω (j - 1)
    · simp [hj1, hj2, ha, hg, not_le_of_gt hg]
    · have hg' : exitTimes M r ω j - exitTimes M r ω (j - 1) ≤ L := le_of_not_gt hg
      simp [hj0, hj1, hj2, ha, hg, hg']
  · simp [hj1, hj2, ha]

private lemma integral_closePairCount_le (ν : ProbabilityMeasure ℝ) (M : ℕ) (r : ℝ)
    (L : ℕ) :
    ∫ ω, (closePairCount M r L ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ)) ≤
      (∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ))) *
        maxTail ν L r := by
  classical
  have heq : ∫ ω, (closePairCount M r L ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ)) =
      ∑ j ∈ Finset.range (M + 1), (iidLaw ν : Measure (ℕ → ℝ)).real
        {ω | 2 ≤ j ∧ exitTimes M r ω j ≤ M ∧
          exitTimes M r ω j - exitTimes M r ω (j - 1) ≤ L} := by
    simpa only [closePairCount, Finset.filter_congr_decidable] using
      (integral_card_filter (iidLaw ν : Measure (ℕ → ℝ)) (Finset.range (M + 1)) _
        (fun _ => inferInstance) (measurableSet_closePairCount M r L))
  have hzero : (iidLaw ν : Measure (ℕ → ℝ)).real
      {ω | 2 ≤ (0 : ℕ) ∧ exitTimes M r ω 0 ≤ M ∧
        exitTimes M r ω 0 - exitTimes M r ω (0 - 1) ≤ L} = 0 := by
    convert measureReal_empty
    ext ω
    simp
  have hshift : (∑ j ∈ Finset.range (M + 1),
      (iidLaw ν : Measure (ℕ → ℝ)).real {ω | 2 ≤ j ∧ exitTimes M r ω j ≤ M ∧
        exitTimes M r ω j - exitTimes M r ω (j - 1) ≤ L}) =
      ∑ j ∈ Finset.range M, (iidLaw ν : Measure (ℕ → ℝ)).real (closePairAt M r L j) := by
    rw [Finset.sum_range_succ', hzero, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases h : 1 ≤ j
    · have heq : {ω : ℕ → ℝ | 2 ≤ j + 1 ∧ exitTimes M r ω (j + 1) ≤ M ∧
          exitTimes M r ω (j + 1) - exitTimes M r ω (j + 1 - 1) ≤ L} =
          closePairAt M r L j := by
        ext ω
        simp [closePairAt, h]
      rw [heq]
    · have heq : {ω : ℕ → ℝ | 2 ≤ j + 1 ∧ exitTimes M r ω (j + 1) ≤ M ∧
          exitTimes M r ω (j + 1) - exitTimes M r ω (j + 1 - 1) ≤ L} = ∅ := by
        ext ω
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        omega
      rw [heq]
      simp [closePairAt, h]
  have hlast : (iidLaw ν : Measure (ℕ → ℝ)).real (closePairAt M r L M) = 0 := by
    have hempty : closePairAt M r L M = ∅ := by
      ext ω
      constructor
      · rintro ⟨hj, hnext, hgap⟩
        have hle := index_le_exitTimes (M := M) (r := r) (ω := ω) (j := M + 1) le_rfl
        omega
      · simp
    rw [hempty, measureReal_empty]
  have hextend : (∑ j ∈ Finset.range M,
      (iidLaw ν : Measure (ℕ → ℝ)).real (closePairAt M r L j)) =
      ∑ j ∈ Finset.range (M + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real (closePairAt M r L j) := by
    rw [Finset.sum_range_succ, hlast, add_zero]
  rw [heq, hshift, hextend]
  calc
    _ ≤ ∑ j ∈ Finset.range (M + 1),
        (iidLaw ν : Measure (ℕ → ℝ)).real {ω | 1 ≤ j ∧ exitTimes M r ω j ≤ M} *
          maxTail ν L r := by
      apply Finset.sum_le_sum
      intro j hj
      exact measureReal_closePairAt_le ν M r L j
    _ = _ := by rw [integral_exitCount_eq_sum, Finset.sum_mul]

/-- Expected number of exits under the safe-block hypothesis. -/
theorem integral_exitCount_le (ν : ProbabilityMeasure ℝ) {M L : ℕ} {r : ℝ} (hr : 0 < r)
    (hL : 1 ≤ L) (hsafe : maxTail ν L r ≤ (1 / 2 : ℝ)) :
    ∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ)) ≤
      2 * ((M : ℝ) / L + 1) := by
  have _ : 0 < r := hr
  have hdecomp : (fun ω => (exitCount M r ω : ℝ)) = fun ω =>
      (farExitCount M r L ω : ℝ) + (closePairCount M r L ω : ℝ) := by
    funext ω
    exact_mod_cast exitCount_eq_far_add_close M r L ω
  have hFi : Integrable (fun ω => (farExitCount M r L ω : ℝ))
      (iidLaw ν : Measure (ℕ → ℝ)) := by
    simpa only [farExitCount, Finset.filter_congr_decidable] using
      (integrable_card_filter (iidLaw ν : Measure (ℕ → ℝ)) (Finset.range (M + 1)) _
        (fun _ => inferInstance) (measurableSet_farExit M r L))
  have hCi : Integrable (fun ω => (closePairCount M r L ω : ℝ))
      (iidLaw ν : Measure (ℕ → ℝ)) := by
    simpa only [closePairCount, Finset.filter_congr_decidable] using
      (integrable_card_filter (iidLaw ν : Measure (ℕ → ℝ)) (Finset.range (M + 1)) _
        (fun _ => inferInstance) (measurableSet_closePairCount M r L))
  have hEN : (∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ))) =
      (∫ ω, (farExitCount M r L ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ))) +
        ∫ ω, (closePairCount M r L ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ)) := by
    rw [hdecomp, integral_add hFi hCi]
  have hF : ∫ ω, (farExitCount M r L ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ)) ≤
      ((M / L + 1 : ℕ) : ℝ) := by
    have hle : (∫ ω, (farExitCount M r L ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ))) ≤
        ∫ _ : ℕ → ℝ, ((M / L + 1 : ℕ) : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ)) := by
      apply integral_mono hFi (integrable_const _)
      intro ω
      change (farExitCount M r L ω : ℝ) ≤ ((M / L + 1 : ℕ) : ℝ)
      exact_mod_cast farExitCount_le M r L hL ω
    simpa using hle
  have hC := integral_closePairCount_le ν M r L
  have hN0 : 0 ≤ ∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ)) :=
    integral_nonneg fun ω => Nat.cast_nonneg _
  have hmul : (∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ))) *
      maxTail ν L r ≤ (∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ))) *
        (1 / 2 : ℝ) := mul_le_mul_of_nonneg_left hsafe hN0
  have hcast : ((M / L + 1 : ℕ) : ℝ) ≤ (M : ℝ) / L + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
    exact add_le_add (Nat.cast_div_le (α := ℝ)) (le_refl 1)
  nlinarith [hEN]

/-- Close-pair bound with the safe-block expected-count estimate. -/
theorem measure_closeExit_le_of_safe (ν : ProbabilityMeasure ℝ) {M L : ℕ} {r : ℝ}
    (hr : 0 < r) (hL : 1 ≤ L) (hsafe : maxTail ν L r ≤ (1 / 2 : ℝ)) (l : ℕ) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | closeExit M r l ω} ≤
      2 * ((M : ℝ) / L + 1) * maxTail ν l r := by
  calc
    _ ≤ (∫ ω, (exitCount M r ω : ℝ) ∂(iidLaw ν : Measure (ℕ → ℝ))) *
        maxTail ν l r :=
      measure_closeExit_le ν hr l
    _ ≤ 2 * ((M : ℝ) / L + 1) * maxTail ν l r :=
      mul_le_mul_of_nonneg_right (integral_exitCount_le ν hr hL hsafe) (maxTail_nonneg ν l r)

end BGW.Probability.RealWalk
