module

public import BGWLeaves.Passage.Defs
public import BGW.Tree.ForestCycle
public import BGW.LocallyFinite.Atoms

/-!
# Proposition 1.4, atoms and the remaining mass

The stopped-word events are finite-coordinate cylinders indexed by forest codes.  Their atom
masses agree with the corresponding forest-code atoms.  The complement of their union is the
event that the walk never hits its target; on the forest side it is the event that some tree is
infinite.
-/

@[expose] public section

namespace BGWLeaves.Passage.Atoms

open MeasureTheory ProbabilityTheory BGW
open scoped ENNReal

private theorem int_step_eq_iff_nat (z : ℤ) (n : ℕ) (hz : -1 ≤ z) :
    ((n : ℤ) - 1 = z) ↔ n = (z + 1).toNat := by
  have hz' : 0 ≤ z + 1 := by omega
  have hcast : ((z + 1).toNat : ℤ) = z + 1 := Int.toNat_of_nonneg hz'
  constructor
  · intro h
    have h' : (n : ℤ) = ((z + 1).toNat : ℤ) := by rw [hcast]; omega
    exact_mod_cast h'
  · intro h
    have h' : (n : ℤ) = z + 1 := by rw [← hcast]; exact_mod_cast h
    omega

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

/-- A stopped word event is exactly the finite cylinder fixing its first `x.length` coordinates,
provided `x` is a forest code. -/
theorem stoppedWordEvent_eq_cylinder {j : ℕ} (x : List ℤ) (hx : IsForestCode j x) :
    stoppedWordEvent j x =
      Set.pi (Finset.range x.length) (fun i => {((x[i]?.getD 0 + 1).toNat)}) := by
  ext ω
  simp only [stoppedWordEvent, Set.mem_ofPred_eq, Set.mem_pi,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hhit, hstep⟩ i hi
    have hi' : i < x.length := Finset.mem_range.mp hi
    have hxi : x[i]?.getD 0 = x[i] := by simp [List.getElem?_eq_getElem hi']
    simpa [hxi] using
      (int_step_eq_iff_nat x[i] (ω i) (hx.1 _ (List.getElem_mem hi'))).mp (hstep i hi')
  · intro hcoords
    have hstep : ∀ i (hi : i < x.length), (ω i : ℤ) - 1 = x[i] := by
      intro i hi
      have hxi : x[i]?.getD 0 = x[i] := by simp [List.getElem?_eq_getElem hi]
      have hcoord : ω i = (x[i] + 1).toNat := by
        simpa [hxi] using hcoords i (Finset.mem_range.mpr hi)
      simpa [hxi] using
        (int_step_eq_iff_nat x[i] (ω i) (hx.1 _ (List.getElem_mem hi))).mpr hcoord
    exact ⟨(firstHit_iff_forestCode_of_steps j ω x hstep).2 hx, hstep⟩

/-- If a word is not a forest code, its stopped-word event is empty. -/
theorem stoppedWordEvent_eq_empty_of_not_code {j : ℕ} (x : List ℤ)
    (hx : ¬ IsForestCode j x) : stoppedWordEvent j x = ∅ := by
  ext ω
  constructor
  · intro h
    exfalso
    exact hx ((firstHit_iff_forestCode_of_steps j ω x h.2).mp h.1)
  · intro h
    exact h.elim

private theorem list_map_prod_eq_range {α : Type*} [Inhabited α] (x : List α)
    (f : α → ℝ≥0∞) :
    (x.map f).prod = ∏ i ∈ Finset.range x.length, f (x[i]?.getD default) := by
  induction x with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    rw [Finset.prod_range_succ']
    simp only [List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some]
    rw [ih]
    ac_rfl

/-- The walk atom has value `walkWeight` on forest codes and zero on all other words. -/
theorem stoppedWordEvent_measure_eq_walkWeight (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {j : ℕ} (x : List ℤ) :
    (Measure.infinitePi fun _ : ℕ => μ) (stoppedWordEvent j x) =
      Set.indicator {x | IsForestCode j x} (BGW.walkWeight (fun d => μ {d})) x := by
  classical
  by_cases hx : IsForestCode j x
  · rw [stoppedWordEvent_eq_cylinder x hx,
      Measure.infinitePi_pi (fun _ : ℕ => μ) (s := Finset.range x.length)
        (t := fun i => ({((x[i]?.getD 0 + 1).toNat)} : Set ℕ))]
    · have hxmem : x ∈ {y : List ℤ | IsForestCode j y} := hx
      rw [Set.indicator_of_mem hxmem]
      simpa [BGW.walkWeight] using
        (list_map_prod_eq_range x (fun a => μ {(a + 1).toNat})).symm
    · intro i hi
      exact measurableSet_singleton _
  · rw [stoppedWordEvent_eq_empty_of_not_code x hx]
    simp [Set.indicator_of_notMem, hx]

/-- On forest codes, the stopped-word atom is the corresponding walk weight. -/
theorem stoppedWordEvent_measure_eq_walkWeight_of_code (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {j : ℕ} (x : List ℤ) (hx : IsForestCode j x) :
    (Measure.infinitePi fun _ : ℕ => μ) (stoppedWordEvent j x) =
      BGW.walkWeight (fun d => μ {d}) x := by
  rw [stoppedWordEvent_measure_eq_walkWeight μ x]
  have hxmem : x ∈ {y : List ℤ | IsForestCode j y} := hx
  exact Set.indicator_of_mem hxmem _

/-- Outside forest codes, the stopped-word atom is zero. -/
theorem stoppedWordEvent_measure_eq_zero_of_not_code (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {j : ℕ} (x : List ℤ) (hx : ¬ IsForestCode j x) :
    (Measure.infinitePi fun _ : ℕ => μ) (stoppedWordEvent j x) = 0 := by
  rw [stoppedWordEvent_measure_eq_walkWeight μ x]
  exact Set.indicator_of_notMem (s := {y : List ℤ | IsForestCode j y}) (a := x)
    (f := BGW.walkWeight (fun d => μ {d})) (by simpa using hx)

private theorem forestCodeEvent_eq_empty_of_not_code {j : ℕ} (hj : 1 ≤ j)
    (x : List ℤ) (hx : ¬ IsForestCode j x) : forestCodeEvent j x = ∅ := by
  ext F
  constructor
  · intro h
    exfalso
    change ∃ ts : Fin j → PlaneTree,
      PlaneForest.increments (List.ofFn ts) = x ∧
        F = fun i => (ts i).toLocallyFinite at h
    rcases h with ⟨ts, hinc, hF⟩
    apply hx
    apply (PlaneForest.isForestCode_iff_existsUnique hj x).mpr
    refine ⟨List.ofFn ts, ⟨by simp, hinc⟩, ?_⟩
    intro us hus
    exact PlaneForest.increments_injective (hus.2.trans hinc.symm)
  · intro h
    exact h.elim

/-- A forest code determines the unique finite forest event as one point in the product space. -/
theorem forestCodeEvent_eq_singleton {j : ℕ} (hj : 1 ≤ j) (x : List ℤ)
    (hx : IsForestCode j x) :
    ∃ ts : Fin j → PlaneTree,
      PlaneForest.increments (List.ofFn ts) = x ∧
        forestCodeEvent j x = {fun i => (ts i).toLocallyFinite} := by
  classical
  obtain ⟨L, ⟨hLlen, hLinc⟩, hLuniq⟩ :=
    (PlaneForest.isForestCode_iff_existsUnique hj x).mp hx
  let ts : Fin j → PlaneTree := fun i =>
    L.get ⟨i.val, by simp [hLlen]⟩
  have hts : List.ofFn ts = L := by
    apply List.ext_getElem (by simp [hLlen])
    intro i hi hj'
    simp [ts]
  have hinc : PlaneForest.increments (List.ofFn ts) = x := by
    rw [hts]
    exact hLinc
  refine ⟨ts, hinc, ?_⟩
  ext F
  constructor
  · rintro ⟨us, hinc', rfl⟩
    have hlist : List.ofFn us = L := hLuniq _ ⟨by simp, hinc'⟩
    have hus : us = ts := (List.ofFn_inj).mp (hlist.trans hts.symm)
    simp [hus]
  · intro hF
    have hF' : F = fun i => (ts i).toLocallyFinite := by
      simpa using hF
    subst F
    exact ⟨ts, hinc, rfl⟩

/-- The forest atom has value `walkWeight` on forest codes and zero on all other words. -/
theorem forestCodeEvent_measure_eq_walkWeight (μ : Measure ℕ) [IsProbabilityMeasure μ]
    {j : ℕ} (hj : 1 ≤ j) (x : List ℤ) :
    (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestCodeEvent j x) =
      Set.indicator {x | IsForestCode j x} (BGW.walkWeight (fun d => μ {d})) x := by
  classical
  by_cases hx : IsForestCode j x
  · obtain ⟨ts, hinc, hset⟩ := forestCodeEvent_eq_singleton hj x hx
    rw [hset, Measure.pi_singleton]
    have hxmem : x ∈ {y : List ℤ | IsForestCode j y} := hx
    rw [Set.indicator_of_mem hxmem]
    calc
      (∏ i, LocallyFinite.bienaymeLaw μ {(ts i).toLocallyFinite}) =
          ∏ i, PlaneTree.weight (fun d => μ {d}) (ts i) := by
        apply Finset.prod_congr rfl
        intro i hi
        exact LocallyFinite.bienaymeLaw_toLocallyFinite μ (ts i)
      _ = ((List.ofFn ts).map (PlaneTree.weight (fun d => μ {d}))).prod := by
        rw [List.map_ofFn, List.prod_ofFn]
        rfl
      _ = BGW.walkWeight (fun d => μ {d}) x := by
        calc
          ((List.ofFn ts).map (PlaneTree.weight (fun d => μ {d}))).prod =
              BGW.walkWeight (fun d => μ {d})
                (PlaneForest.increments (List.ofFn ts)) :=
            (PlaneForest.walkWeight_increments (fun d => μ {d}) (List.ofFn ts)).symm
          _ = BGW.walkWeight (fun d => μ {d}) x := by rw [hinc]
  · rw [forestCodeEvent_eq_empty_of_not_code hj x hx]
    simp [Set.indicator_of_notMem, hx]

/-- On forest codes, the forest atom is the corresponding walk weight. -/
theorem forestCodeEvent_measure_eq_walkWeight_of_code (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {j : ℕ} (hj : 1 ≤ j) (x : List ℤ)
    (hx : IsForestCode j x) :
    (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestCodeEvent j x) =
      BGW.walkWeight (fun d => μ {d}) x := by
  rw [forestCodeEvent_measure_eq_walkWeight μ hj x]
  have hxmem : x ∈ {y : List ℤ | IsForestCode j y} := hx
  exact Set.indicator_of_mem hxmem _

/-- Outside forest codes, the forest-code atom is zero. -/
theorem forestCodeEvent_measure_eq_zero_of_not_code (μ : Measure ℕ)
    [IsProbabilityMeasure μ] {j : ℕ} (hj : 1 ≤ j) (x : List ℤ)
    (hx : ¬ IsForestCode j x) :
    (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestCodeEvent j x) = 0 := by
  rw [forestCodeEvent_measure_eq_walkWeight μ hj x]
  exact Set.indicator_of_notMem (s := {y : List ℤ | IsForestCode j y}) (a := x)
    (f := BGW.walkWeight (fun d => μ {d})) (by simpa using hx)

/-- The walk and forest atoms agree for every finite word. -/
theorem stoppedWord_atom (μ : Measure ℕ) [IsProbabilityMeasure μ] {j : ℕ} (hj : 1 ≤ j)
    (x : List ℤ) :
    (Measure.infinitePi fun _ : ℕ => μ) (stoppedWordEvent j x) =
      (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestCodeEvent j x) := by
  rw [stoppedWordEvent_measure_eq_walkWeight μ x,
    forestCodeEvent_measure_eq_walkWeight μ hj x]

private theorem isFirstHit_unique {j : ℕ} {ω : ℕ → ℕ} {p q : ℕ}
    (hp : IsFirstHit j ω p) (hq : IsFirstHit j ω q) : p = q := by
  by_contra hne
  by_cases hpq : p < q
  · have h := hq.2 p hpq
    rw [hp.1] at h
    omega
  · have hqp : q < p := by omega
    have h := hp.2 q hqp
    rw [hq.1] at h
    omega

private theorem stoppedWordEvent_pairwise_disjoint (j : ℕ) :
    Pairwise (Function.onFun Disjoint (stoppedWordEvent j)) := by
  intro x y hxy
  apply Set.disjoint_left.mpr
  intro ω hx hy
  have hlen := isFirstHit_unique hx.1 hy.1
  apply hxy
  apply List.ext_getElem hlen
  intro i hi hj
  have hxi := hx.2 i hi
  have hyi := hy.2 i (by simpa [hlen] using hi)
  omega

private theorem iUnion_stoppedWordEvent (j : ℕ) :
    (⋃ x : List ℤ, stoppedWordEvent j x) = {ω | ∃ p, IsFirstHit j ω p} := by
  ext ω
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
    exact ⟨x.length, hx.1⟩
  · rintro ⟨p, hp⟩
    let x : List ℤ := List.ofFn fun i : Fin p => ((ω i : ℕ) : ℤ) - 1
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    constructor
    · simpa [x] using hp
    · intro i hi
      simp [x]

private theorem stoppedWordEvent_measurable {j : ℕ} (x : List ℤ) :
    MeasurableSet (stoppedWordEvent j x) := by
  classical
  by_cases hx : IsForestCode j x
  · rw [stoppedWordEvent_eq_cylinder x hx]
    exact MeasurableSet.pi (Finset.countable_toSet _) (by
      intro i hi
      exact measurableSet_singleton _)
  · rw [stoppedWordEvent_eq_empty_of_not_code x hx]
    exact MeasurableSet.empty

private theorem walkNeverHit_eq_compl_iUnion (j : ℕ) :
    {ω | ∀ p, ¬ IsFirstHit j ω p} = (⋃ x : List ℤ, stoppedWordEvent j x)ᶜ := by
  rw [iUnion_stoppedWordEvent]
  ext ω
  simp

private theorem forestCodeEvent_pairwise_disjoint {j : ℕ} :
    Pairwise (Function.onFun Disjoint (forestCodeEvent j)) := by
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
  rw [← hinc, ← hinc', hts]

private theorem iUnion_forestCodeEvent_eq_finite (j : ℕ) :
    (⋃ x : List ℤ, forestCodeEvent j x) =
      {F | ∀ i, LocallyFinite.FiniteVertices (F i)} := by
  classical
  ext F
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Set.mem_iUnion.mp h
    obtain ⟨ts, hinc, rfl⟩ := hx
    intro i
    exact PlaneTree.finiteVertices_toLocallyFinite (ts i)
  · intro hfinite
    let ts : Fin j → PlaneTree := fun i =>
      Classical.choose ((LocallyFinite.exists_toLocallyFinite_iff (F i)).2 (hfinite i))
    have hts : ∀ i, (ts i).toLocallyFinite = F i := by
      intro i
      exact Classical.choose_spec
        ((LocallyFinite.exists_toLocallyFinite_iff (F i)).2 (hfinite i))
    let x := PlaneForest.increments (List.ofFn ts)
    refine Set.mem_iUnion.mpr ⟨x, ?_⟩
    exact ⟨ts, rfl, funext fun i => (hts i).symm⟩

private theorem forestCodeEvent_measurable {j : ℕ} (hj : 1 ≤ j) (x : List ℤ) :
    MeasurableSet (forestCodeEvent j x) := by
  classical
  by_cases hx : IsForestCode j x
  · obtain ⟨ts, hinc, hset⟩ := forestCodeEvent_eq_singleton hj x hx
    rw [hset]
    exact measurableSet_singleton _
  · rw [forestCodeEvent_eq_empty_of_not_code hj x hx]
    exact MeasurableSet.empty

private theorem forestInfinite_eq_compl_iUnion {j : ℕ} :
    {F : Fin j → LocallyFinite.Tree | ∃ i, ¬ LocallyFinite.FiniteVertices (F i)} =
      (⋃ x : List ℤ, forestCodeEvent j x)ᶜ := by
  rw [iUnion_forestCodeEvent_eq_finite]
  ext F
  simp

/-- Proposition 1.4, the remaining atom: the walk never hits `-j` iff some tree of the forest is
infinite. -/
theorem stoppedWord_none (μ : Measure ℕ) [IsProbabilityMeasure μ] {j : ℕ} (hj : 1 ≤ j) :
    (Measure.infinitePi fun _ : ℕ => μ) {ω | ∀ p, ¬ IsFirstHit j ω p} =
      (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ)
        {F | ∃ i, ¬ LocallyFinite.FiniteVertices (F i)} := by
  have hwalkUmeas : MeasurableSet (⋃ x : List ℤ, stoppedWordEvent j x) :=
    MeasurableSet.iUnion fun x => stoppedWordEvent_measurable x
  have hforestUmeas : MeasurableSet (⋃ x : List ℤ, forestCodeEvent j x) :=
    MeasurableSet.iUnion fun x => forestCodeEvent_measurable hj x
  have hwalk :
      (Measure.infinitePi fun _ : ℕ => μ) {ω | ∀ p, ¬ IsFirstHit j ω p} =
        1 - ∑' x : List ℤ,
          (Measure.infinitePi fun _ : ℕ => μ) (stoppedWordEvent j x) := by
    rw [walkNeverHit_eq_compl_iUnion, measure_compl hwalkUmeas (measure_ne_top _ _),
      IsProbabilityMeasure.measure_univ, measure_iUnion (stoppedWordEvent_pairwise_disjoint j)
        (fun x => stoppedWordEvent_measurable x)]
  have hforest :
      (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ)
          {F | ∃ i, ¬ LocallyFinite.FiniteVertices (F i)} =
        1 - ∑' x : List ℤ,
          (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestCodeEvent j x) := by
    rw [forestInfinite_eq_compl_iUnion, measure_compl hforestUmeas (measure_ne_top _ _),
      IsProbabilityMeasure.measure_univ, measure_iUnion forestCodeEvent_pairwise_disjoint
        (fun x => forestCodeEvent_measurable hj x)]
  have htsum :
      (∑' x : List ℤ, (Measure.infinitePi fun _ : ℕ => μ) (stoppedWordEvent j x)) =
        ∑' x : List ℤ,
          (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestCodeEvent j x) :=
    tsum_congr fun x => stoppedWord_atom μ hj x
  rw [hwalk, hforest, htsum]

end BGWLeaves.Passage.Atoms

end
