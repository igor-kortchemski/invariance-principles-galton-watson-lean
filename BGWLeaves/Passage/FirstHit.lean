module

public import BGWLeaves.Passage.Atoms

/-!
# The first-hit law

The stopped walk and the finite forest are partitioned by their common forest code.  The same
partition, with the number of `-1` steps recorded, proves the joint law with the number of leaves.
-/

@[expose] public section

namespace BGWLeaves.Passage.FirstHit

open MeasureTheory ProbabilityTheory BGW
open scoped ENNReal

private abbrev CodeWords (j p : ℕ) :=
  {x : List ℤ // IsForestCode j x ∧ x.length = p}

private abbrev MarkedCodeWords (j p n : ℕ) :=
  {x : List ℤ // IsForestCode j x ∧ x.length = p ∧ wordDegreeCount x 0 = n}

private theorem walkPrefix_sum_eq_take_sum (ω : ℕ → ℕ) (x : List ℤ)
    (hstep : ∀ i (hi : i < x.length), (ω i : ℤ) - 1 = x[i]) (q : ℕ)
    (hq : q ≤ x.length) :
    (∑ i ∈ Finset.range q, ((ω i : ℤ) - 1)) = (x.take q).sum := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hq' : q < x.length := by omega
    rw [Finset.sum_range_succ, ih (by omega), List.sum_take_succ x q hq', hstep q hq']

private theorem firstHit_iff_forestCode_of_steps (j : ℕ) (ω : ℕ → ℕ) (x : List ℤ)
    (hstep : ∀ i (hi : i < x.length), (ω i : ℤ) - 1 = x[i]) :
    IsFirstHit j ω x.length ↔ IsForestCode j x := by
  constructor
  · intro hhit
    refine ⟨?_, ?_, ?_⟩
    · intro a ha
      obtain ⟨i, hi, hia⟩ := List.mem_iff_getElem.mp ha
      have := hstep i hi
      rw [hia] at this
      omega
    · have hsum : (∑ i ∈ Finset.range x.length, ((ω i : ℤ) - 1)) = x.sum := by
        simpa using walkPrefix_sum_eq_take_sum ω x hstep x.length le_rfl
      exact hsum.symm.trans hhit.1
    · intro i hi
      have hsum := walkPrefix_sum_eq_take_sum ω x hstep i (Nat.le_of_lt hi)
      simpa [hsum] using hhit.2 i hi
  · rintro ⟨hge, hsum, hpre⟩
    refine ⟨?_, ?_⟩
    · have htotal := walkPrefix_sum_eq_take_sum ω x hstep x.length le_rfl
      calc
        (∑ i ∈ Finset.range x.length, ((ω i : ℤ) - 1)) = (x.take x.length).sum := htotal
        _ = x.sum := by simp
        _ = -(j : ℤ) := hsum
    · intro q hq
      have hprefix := walkPrefix_sum_eq_take_sum ω x hstep q (Nat.le_of_lt hq)
      simpa [hprefix] using hpre q hq

private theorem wordDegreeCount_stepWord_eq_filter {p : ℕ} (ω : Fin p → ℕ) :
    wordDegreeCount (stepWord ω) 0 = (Finset.univ.filter fun i : Fin p => ω i = 0).card := by
  rw [wordDegreeCount_stepWord]
  calc
    (List.ofFn ω).count 0 = (List.finRange p).countP (fun i => decide (ω i = 0)) := by
      rw [List.count_eq_countP, List.ofFn_eq_map, List.countP_map]
      rfl
    _ = (Finset.univ.filter fun i : Fin p => ω i = 0).card := by
      rw [List.countP_eq_length_filter]
      rw [← List.toFinset_card_of_nodup
        ((List.nodup_finRange p).filter (fun i => decide (ω i = 0)))]
      rw [← List.filter_toFinset]
      simp

private theorem forestLeafCount_eq_wordDegreeCount (ts : PlaneForest) :
    forestLeafCount ts = wordDegreeCount (PlaneForest.increments ts) 0 := by
  induction ts with
  | nil => simp [forestLeafCount, PlaneForest.increments, wordDegreeCount]
  | cons t ts ih =>
    change t.degreeCount 0 + forestLeafCount ts =
      wordDegreeCount (t.increments ++ PlaneForest.increments ts) 0
    rw [show wordDegreeCount (t.increments ++ PlaneForest.increments ts) 0 =
        wordDegreeCount t.increments 0 + wordDegreeCount (PlaneForest.increments ts) 0 by
          simp [wordDegreeCount, List.count_append],
      PlaneTree.wordDegreeCount_increments, ih]

private theorem wordDegreeCount_forestIncrements {j : ℕ} (ts : Fin j → PlaneTree) :
    wordDegreeCount (PlaneForest.increments (List.ofFn ts)) 0 =
      ∑ i, (ts i).degreeCount 0 := by
  calc
    wordDegreeCount (PlaneForest.increments (List.ofFn ts)) 0 =
        forestLeafCount (List.ofFn ts) := (forestLeafCount_eq_wordDegreeCount _).symm
    _ = ∑ i, (ts i).degreeCount 0 := by
      simp [forestLeafCount, List.map_ofFn, List.sum_ofFn]

private theorem stoppedWordEvent_pairwiseDisjoint (j p : ℕ) :
    Pairwise (Function.onFun Disjoint fun x : CodeWords j p =>
      stoppedWordEvent j x.1) := by
  intro x y hxy
  apply Set.disjoint_left.mpr
  intro ω hx hy
  apply hxy
  apply Subtype.ext
  apply List.ext_getElem (x.2.2.trans y.2.2.symm)
  intro i hi hyi
  have hxi := hx.2 i hi
  have hyi := hy.2 i hyi
  omega

private theorem forestCodeEvent_pairwiseDisjoint {j p : ℕ} :
    Pairwise (Function.onFun Disjoint fun x : CodeWords j p =>
      forestCodeEvent j x.1) := by
  intro x y hxy
  apply Set.disjoint_left.mpr
  intro F hx hy
  obtain ⟨ts, hinc, hF⟩ := hx
  obtain ⟨us, hinc', hF'⟩ := hy
  have hmap : (fun i => (ts i).toLocallyFinite) = fun i => (us i).toLocallyFinite :=
    hF.symm.trans hF'
  have hts : ts = us := by
    funext i
    exact PlaneTree.toLocallyFinite_injective (congrFun hmap i)
  apply hxy
  apply Subtype.ext
  calc
    x.1 = PlaneForest.increments (List.ofFn ts) := hinc.symm
    _ = PlaneForest.increments (List.ofFn us) := by rw [hts]
    _ = y.1 := hinc'

private theorem stoppedWordEvent_measurable {j p : ℕ} (x : CodeWords j p) :
    MeasurableSet (stoppedWordEvent j x.1) := by
  rw [BGWLeaves.Passage.Atoms.stoppedWordEvent_eq_cylinder x.1 x.2.1]
  exact MeasurableSet.pi (Finset.countable_toSet _) (by
    intro i hi
    exact measurableSet_singleton _)

private theorem forestCodeEvent_measurable {j p : ℕ} (hj : 1 ≤ j)
    (x : CodeWords j p) : MeasurableSet (forestCodeEvent j x.1) := by
  obtain ⟨ts, _, hset⟩ :=
    BGWLeaves.Passage.Atoms.forestCodeEvent_eq_singleton hj x.1 x.2.1
  rw [hset]
  exact measurableSet_singleton _

private theorem walkHit_iUnion (j p : ℕ) :
    (⋃ x : CodeWords j p, stoppedWordEvent j x.1) = {ω | IsFirstHit j ω p} := by
  classical
  ext ω
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
    simpa [x.2.2] using hx.1
  · intro hhit
    let x : List ℤ := List.ofFn fun i : Fin p => (ω i : ℤ) - 1
    have hstep : ∀ i (hi : i < x.length), (ω i : ℤ) - 1 = x[i] := by
      intro i hi
      simp [x]
    have hcode : IsForestCode j x := (firstHit_iff_forestCode_of_steps j ω x hstep).mp
      (by simpa [x] using hhit)
    refine Set.mem_iUnion.mpr ⟨⟨x, hcode, by simp [x]⟩, ?_⟩
    exact ⟨by simpa [x] using hhit, hstep⟩

private theorem walkMarked_iUnion (j p n : ℕ) :
    (⋃ x : MarkedCodeWords j p n, stoppedWordEvent j x.1) =
      {ω | IsFirstHit j ω p ∧ (Finset.univ.filter fun i : Fin p => ω i = 0).card = n} := by
  classical
  ext ω
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
    refine ⟨by simpa [x.2.2.1] using hx.1, ?_⟩
    have hstepWord : x.1 = stepWord (fun i : Fin p => ω i) := by
      have hlenX : x.1.length = p := x.2.2.1
      have hlenS : (stepWord (fun i : Fin p => ω i)).length = p := by
        simp [BGW.stepWord]
      apply List.ext_getElem (hlenX.trans hlenS.symm)
      intro i hi _
      have hs := hx.2 i hi
      simpa [BGW.stepWord] using hs.symm
    rw [← wordDegreeCount_stepWord_eq_filter]
    rw [← hstepWord]
    exact x.2.2.2
  · rintro ⟨hhit, hcount⟩
    let x : List ℤ := List.ofFn fun i : Fin p => (ω i : ℤ) - 1
    have hstep : ∀ i (hi : i < x.length), (ω i : ℤ) - 1 = x[i] := by
      intro i hi
      simp [x]
    have hcode : IsForestCode j x := (firstHit_iff_forestCode_of_steps j ω x hstep).mp
      (by simpa [x] using hhit)
    have hcount' : wordDegreeCount x 0 = n := by
      rw [show x = stepWord (fun i : Fin p => ω i) by rfl,
        wordDegreeCount_stepWord_eq_filter]
      simpa using hcount
    refine Set.mem_iUnion.mpr ⟨⟨x, hcode, by simp [x], hcount'⟩, ?_⟩
    exact ⟨by simpa [x] using hhit, hstep⟩

private theorem forestSize_iUnion {j p : ℕ} (hj : 1 ≤ j) :
    (⋃ x : CodeWords j p, forestCodeEvent j x.1) = forestSizeEvent j p := by
  classical
  ext F
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
    obtain ⟨ts, hinc, hF⟩ := hx
    subst F
    refine ⟨ts, ?_, rfl⟩
    have hs : PlaneForest.size (List.ofFn ts) = p := by
      calc
        PlaneForest.size (List.ofFn ts) =
            (PlaneForest.increments (List.ofFn ts)).length :=
          (PlaneForest.length_increments _).symm
        _ = x.1.length := by rw [hinc]
        _ = p := x.2.2
    simpa [PlaneForest.size, List.map_ofFn, List.sum_ofFn] using hs
  · rintro ⟨ts, hp, rfl⟩
    let x : List ℤ := PlaneForest.increments (List.ofFn ts)
    have hcode : IsForestCode j x := by
      apply (PlaneForest.isForestCode_iff_existsUnique hj x).mpr
      refine ⟨List.ofFn ts, ⟨by simp, rfl⟩, ?_⟩
      intro us hus
      exact PlaneForest.increments_injective (hus.2.trans rfl)
    have hlen : x.length = p := by
      simp only [x, PlaneForest.length_increments]
      simpa [PlaneForest.size, List.map_ofFn, List.sum_ofFn] using hp
    exact Set.mem_iUnion.mpr ⟨⟨x, hcode, hlen⟩, ⟨ts, rfl, rfl⟩⟩

private theorem forestEvent_iUnion {j p n : ℕ} (hj : 1 ≤ j) :
    (⋃ x : MarkedCodeWords j p n, forestCodeEvent j x.1) = forestEvent j p n := by
  classical
  ext F
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
    obtain ⟨ts, hinc, hF⟩ := hx
    subst F
    refine ⟨ts, ?_, ?_, rfl⟩
    · have hs : PlaneForest.size (List.ofFn ts) = p := by
        calc
          PlaneForest.size (List.ofFn ts) =
              (PlaneForest.increments (List.ofFn ts)).length :=
            (PlaneForest.length_increments _).symm
          _ = x.1.length := by rw [hinc]
          _ = p := x.2.2.1
      simpa [PlaneForest.size, List.map_ofFn, List.sum_ofFn] using hs
    · have hc : wordDegreeCount (PlaneForest.increments (List.ofFn ts)) 0 = n := by
        rw [hinc]
        exact x.2.2.2
      rw [← wordDegreeCount_forestIncrements]
      simpa using hc
  · rintro ⟨ts, hp, hn, rfl⟩
    let x : List ℤ := PlaneForest.increments (List.ofFn ts)
    have hcode : IsForestCode j x := by
      apply (PlaneForest.isForestCode_iff_existsUnique hj x).mpr
      refine ⟨List.ofFn ts, ⟨by simp, rfl⟩, ?_⟩
      intro us hus
      exact PlaneForest.increments_injective (hus.2.trans rfl)
    have hlen : x.length = p := by
      simp only [x, PlaneForest.length_increments]
      simpa [PlaneForest.size, List.map_ofFn, List.sum_ofFn] using hp
    have hcount : wordDegreeCount x 0 = n := by
      change wordDegreeCount (PlaneForest.increments (List.ofFn ts)) 0 = n
      rw [wordDegreeCount_forestIncrements]
      simpa using hn
    exact Set.mem_iUnion.mpr ⟨⟨x, hcode, hlen, hcount⟩, ⟨ts, rfl, rfl⟩⟩

private theorem forestMarkedCodeEvent_pairwiseDisjoint {j p n : ℕ} :
    Pairwise (Function.onFun Disjoint fun x : MarkedCodeWords j p n =>
      forestCodeEvent j x.1) := by
  intro x y hxy
  apply Set.disjoint_left.mpr
  intro F hx hy
  obtain ⟨ts, hinc, hF⟩ := hx
  obtain ⟨us, hinc', hF'⟩ := hy
  have hmap : (fun i => (ts i).toLocallyFinite) = fun i => (us i).toLocallyFinite :=
    hF.symm.trans hF'
  have hts : ts = us := by
    funext i
    exact PlaneTree.toLocallyFinite_injective (congrFun hmap i)
  apply hxy
  apply Subtype.ext
  calc
    x.1 = PlaneForest.increments (List.ofFn ts) := hinc.symm
    _ = PlaneForest.increments (List.ofFn us) := by rw [hts]
    _ = y.1 := hinc'

private theorem stoppedWordMarkedEvent_pairwiseDisjoint {j p n : ℕ} :
    Pairwise (Function.onFun Disjoint fun x : MarkedCodeWords j p n =>
      stoppedWordEvent j x.1) := by
  intro x y hxy
  apply Set.disjoint_left.mpr
  intro ω hx hy
  apply hxy
  apply Subtype.ext
  apply List.ext_getElem (x.2.2.1.trans y.2.2.1.symm)
  intro i hi hyi
  have hxi := hx.2 i hi
  have hyi := hy.2 i hyi
  omega

private theorem stoppedWordMarkedEvent_measurable {j p n : ℕ}
    (x : MarkedCodeWords j p n) : MeasurableSet (stoppedWordEvent j x.1) := by
  exact stoppedWordEvent_measurable ⟨x.1, x.2.1, x.2.2.1⟩

private theorem forestMarkedCodeEvent_measurable {j p n : ℕ} (hj : 1 ≤ j)
    (x : MarkedCodeWords j p n) : MeasurableSet (forestCodeEvent j x.1) := by
  exact forestCodeEvent_measurable hj ⟨x.1, x.2.1, x.2.2.1⟩

/-- The hitting time of `-j` has the same law as the total size of a forest of `j` trees. -/
theorem firstHit_law (μ : Measure ℕ) [IsProbabilityMeasure μ] {j : ℕ} (hj : 1 ≤ j) (p : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ) {ω | IsFirstHit j ω p} =
      (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestSizeEvent j p) := by
  let walk : CodeWords j p → Set (ℕ → ℕ) := fun x => stoppedWordEvent j x.1
  let forest : CodeWords j p → Set (Fin j → LocallyFinite.Tree) := fun x => forestCodeEvent j x.1
  have hwalk := walkHit_iUnion j p
  have hforest := forestSize_iUnion (j := j) (p := p) hj
  rw [← hwalk, ← hforest]
  calc
    (Measure.infinitePi fun _ : ℕ => μ) (⋃ x : CodeWords j p, walk x) =
        ∑' x : CodeWords j p, (Measure.infinitePi fun _ : ℕ => μ) (walk x) := by
      rw [measure_iUnion (stoppedWordEvent_pairwiseDisjoint j p)
        (fun x => stoppedWordEvent_measurable x)]
    _ = ∑' x : CodeWords j p,
        (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forest x) := by
      exact tsum_congr fun x => BGWLeaves.Passage.Atoms.stoppedWord_atom μ hj x.1
    _ = (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ)
        (⋃ x : CodeWords j p, forest x) := by
      rw [measure_iUnion (forestCodeEvent_pairwiseDisjoint (j := j) (p := p))
        (fun x => forestCodeEvent_measurable hj x)]

/-- The joint law of the hitting time and the number of leaves counted along the walk. -/
theorem firstHit_leaves_law (μ : Measure ℕ) [IsProbabilityMeasure μ] {j : ℕ} (hj : 1 ≤ j)
    (p n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ)
        {ω | IsFirstHit j ω p ∧ (Finset.univ.filter fun i : Fin p => ω i = 0).card = n} =
      (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestEvent j p n) := by
  let walk : MarkedCodeWords j p n → Set (ℕ → ℕ) := fun x => stoppedWordEvent j x.1
  let forest : MarkedCodeWords j p n → Set (Fin j → LocallyFinite.Tree) :=
    fun x => forestCodeEvent j x.1
  have hwalk := walkMarked_iUnion j p n
  have hforest := forestEvent_iUnion (j := j) (p := p) (n := n) hj
  rw [← hwalk, ← hforest]
  calc
    (Measure.infinitePi fun _ : ℕ => μ) (⋃ x : MarkedCodeWords j p n, walk x) =
        ∑' x : MarkedCodeWords j p n, (Measure.infinitePi fun _ : ℕ => μ) (walk x) := by
      rw [measure_iUnion (stoppedWordMarkedEvent_pairwiseDisjoint (j := j) (p := p) (n := n))
        (fun x => stoppedWordMarkedEvent_measurable x)]
    _ = ∑' x : MarkedCodeWords j p n,
        (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forest x) := by
      exact tsum_congr fun x => BGWLeaves.Passage.Atoms.stoppedWord_atom μ hj x.1
    _ = (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ)
        (⋃ x : MarkedCodeWords j p n, forest x) := by
      rw [measure_iUnion (forestMarkedCodeEvent_pairwiseDisjoint (j := j) (p := p) (n := n))
        (fun x => forestMarkedCodeEvent_measurable hj x)]

end BGWLeaves.Passage.FirstHit

end
