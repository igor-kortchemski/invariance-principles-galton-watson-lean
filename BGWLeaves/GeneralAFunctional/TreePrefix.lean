module

public import BGWLeaves.GeneralAFunctional.Defs
public import BGWLeaves.GeneralA.MarkedLaw
public import BGW.StableTrees.DiscreteForestPrefixMass

/-! Deterministic exploration prefixes with arbitrary offspring marks. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreePrefix

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.GeneralA.Marked BGWLeaves.GeneralA.MarkedLaw
open scoped ENNReal Classical

local instance : MeasurableSpace (List ℕ) := ⊤
local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

/-- Marks revealed by a finite degree word. -/
noncomputable def prefixMarks (A : Set ℕ) (a : List ℕ) : ℕ :=
  a.countP (fun d => decide (d ∈ A))

theorem prefixMarks_append (A : Set ℕ) (a b : List ℕ) :
    prefixMarks A (a ++ b) = prefixMarks A a + prefixMarks A b := by
  simp [prefixMarks, List.countP_append]

/-- Count marks up to completion of the first `j` ladder trees. -/
noncomputable def completionMarks (A : Set ℕ) (j : ℕ) (ω : ℕ → ℕ) : ℕ :=
  prefixMarks A (seqPrefix (ladderTime ω j) ω)

theorem measurable_completionMarks (A : Set ℕ) (j : ℕ) :
    Measurable (completionMarks A j) := by
  have hm (n : ℕ) : Measurable (fun ω => prefixMarks A (seqPrefix n ω)) := by
    exact (measurable_from_top : Measurable (prefixMarks A)).comp (measurable_seqPrefix n)
  have hprod : Measurable (fun p : (ℕ → ℕ) × ℕ => prefixMarks A (seqPrefix p.2 p.1)) :=
    measurable_from_prod_countable_left hm
  exact hprod.comp (measurable_id.prodMk (measurable_ladderTime j))

/-- The ladder completion count is the sum of the counts on its decoded trees. -/
theorem completionMarks_eq_sum {ω : ℕ → ℕ} (hω : LadderFinite ω)
    (A : Set ℕ) (j : ℕ) :
    completionMarks A j ω = ∑ i : Fin j, treeACount A (blockTree ω i) := by
  rw [completionMarks, ← degrees_blockPrefix hω]
  simp only [blockPrefix, PlaneForest.degrees, List.map_ofFn]
  simp only [prefixMarks, List.countP_flatten, List.map_ofFn, List.sum_ofFn, treeACount, Function.comp_def]

/-- A surviving prefix lies strictly before the end of the first tree. -/
theorem prefix_lt_ladderTime {ω : ℕ → ℕ} (hω : LadderFinite ω)
    {a : List ℕ} (ha : seqPrefix a.length ω = a) (hs : IsSurvivingPrefix a) :
    a.length < ladderTime ω 1 := by
  by_contra h
  have hle : ladderTime ω 1 ≤ a.length := by omega
  have hp := hs (ladderTime ω 1) hle
  change 0 ≤ prefixWalk (a.take (ladderTime ω 1)) at hp
  rw [← ha, take_seqPrefix _ _ _ hle, prefixWalk_seqPrefix, walk_ladderTime hω] at hp
  omega

/-- First passage of the remaining forest after a surviving deterministic prefix. -/
theorem ladderTime_shift_prefix {ω : ℕ → ℕ} (hω : LadderFinite ω)
    {a : List ℕ} (ha : seqPrefix a.length ω = a) (hs : IsSurvivingPrefix a) :
    ladderTime (DiscreteForest.shiftSeq a.length ω) (prefixStack a) = ladderTime ω 1 - a.length := by
  have hlt := prefix_lt_ladderTime hω ha hs
  have hh := (prefix_ladder_iff_forestHit hω rfl hlt hs).mp ⟨ha, rfl⟩
  change sInf {k | walk (DiscreteForest.shiftSeq a.length ω) k = -(prefixStack a : ℤ)} = _
  apply le_antisymm (Nat.sInf_le hh.2.1)
  by_contra hn
  change ¬ ladderTime ω 1 - a.length ≤ ladderTime (DiscreteForest.shiftSeq a.length ω) (prefixStack a) at hn
  have hle : ladderTime (DiscreteForest.shiftSeq a.length ω) (prefixStack a) ≤
      ladderTime ω 1 - a.length := Nat.sInf_le hh.2.1
  have he := Nat.sInf_mem (s := {k | walk (DiscreteForest.shiftSeq a.length ω) k = -(prefixStack a : ℤ)})
    ⟨_, hh.2.1⟩
  change walk (DiscreteForest.shiftSeq a.length ω) (ladderTime (DiscreteForest.shiftSeq a.length ω) (prefixStack a)) = _ at he
  have hp := hh.2.2 (ladderTime (DiscreteForest.shiftSeq a.length ω) (prefixStack a)) (by omega)
  rw [he] at hp
  omega

/-- Marks split additively at a surviving deterministic prefix. -/
theorem completionMarks_split {ω : ℕ → ℕ} (hω : LadderFinite ω)
    (A : Set ℕ) {a : List ℕ} (ha : seqPrefix a.length ω = a)
    (hs : IsSurvivingPrefix a) :
    completionMarks A 1 ω = prefixMarks A a +
      completionMarks A (prefixStack a) (DiscreteForest.shiftSeq a.length ω) := by
  have hlt := prefix_lt_ladderTime hω ha hs
  unfold completionMarks
  rw [ladderTime_shift_prefix hω ha hs]
  conv_lhs => rw [show ladderTime ω 1 = a.length + (ladderTime ω 1 - a.length) by omega,
    seqPrefix_add, prefixMarks_append, ha]

/-- A-marked completion kernel in the iid exploration representation. -/
noncomputable def completionMass (μ : PMF ℕ) (A : Set ℕ) (j n : ℕ) : ℝ≥0∞ :=
  (offspringSeqLaw μ).toMeasure {ω | completionMarks A j ω = n}

/-- Deterministic-prefix factorization, with the impossible-count convention explicit. -/
theorem completion_prefix_mass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (a : List ℕ) (n : ℕ) (hs : IsSurvivingPrefix a) :
    (offspringSeqLaw μ).toMeasure
        {ω | seqPrefix a.length ω = a ∧ completionMarks A 1 ω = n} =
      (a.map μ).prod * if prefixMarks A a ≤ n then
        completionMass μ A (prefixStack a) (n - prefixMarks A a) else 0 := by
  by_cases hkn : prefixMarks A a ≤ n
  · have heq : {ω | seqPrefix a.length ω = a ∧ completionMarks A 1 ω = n} =ᵐ[
        (offspringSeqLaw μ).toMeasure]
        {ω | seqPrefix a.length ω = a} ∩ DiscreteForest.shiftSeq a.length ⁻¹'
          {ω | completionMarks A (prefixStack a) ω = n - prefixMarks A a} := by
      filter_upwards [ae_ladderFinite μ hc hne] with ω hω
      apply propext
      simp only [mem_inter_iff, mem_preimage, mem_ofPred_eq]
      constructor
      · rintro ⟨ha, hn⟩
        have he := completionMarks_split hω A (a := a) ha hs
        exact ⟨ha, by omega⟩
      · rintro ⟨ha, hn⟩
        have he := completionMarks_split hω A (a := a) ha hs
        exact ⟨ha, by omega⟩
    rw [ite_eq_left hkn, measure_congr heq, seqPrefix_inter_shift_mass μ a
      (measurableSet_eq_fun (measurable_completionMarks A _) measurable_const)]
    rfl
  · rw [ite_eq_right hkn, mul_zero]
    have heq : {ω | seqPrefix a.length ω = a ∧ completionMarks A 1 ω = n} =ᵐ[
        (offspringSeqLaw μ).toMeasure] ∅ := by
      filter_upwards [ae_ladderFinite μ hc hne] with ω hω
      apply propext
      constructor
      · rintro ⟨ha, hn⟩
        have he := completionMarks_split hω A (a := a) ha hs
        simp only [mem_empty_iff_false]
        omega
      · simp
    rw [measure_congr heq, measure_empty]

/-- Finite forests with a specified total mark count. -/
def markedForestEvent (A : Set ℕ) (j n : ℕ) : Set (Fin j → LocallyFinite.Tree) :=
  {F | (∀ i, FiniteVertices (F i)) ∧ ∑ i, zetaA A (F i) = (n : ℕ∞)}

theorem markedForestEvent_eq_image (A : Set ℕ) (j n : ℕ) :
    markedForestEvent A j n =
      (fun ts : Fin j → PlaneTree => fun i => (ts i).toLocallyFinite) ''
        {ts | ∑ i, treeACount A (ts i) = n} := by
  ext F
  constructor
  · rintro ⟨hF, hn⟩
    choose ts hts using fun i => (exists_toLocallyFinite_iff (F i)).mpr (hF i)
    refine ⟨ts, ?_, funext hts⟩
    have he : ∑ i, zetaA A (F i) = ((∑ i, treeACount A (ts i) : ℕ) : ℕ∞) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [← hts i, zetaA_toLocallyFinite]
    rw [he] at hn
    exact ENat.natCast_inj.mp hn
  · rintro ⟨ts, hn, rfl⟩
    refine ⟨fun i => (ts i).finiteVertices_toLocallyFinite, ?_⟩
    simp_rw [zetaA_toLocallyFinite]
    rw [← Nat.cast_sum, hn]

theorem measurableSet_markedForestEvent (A : Set ℕ) (j n : ℕ) :
    MeasurableSet (markedForestEvent A j n) := by
  rw [markedForestEvent_eq_image]
  exact ((Set.to_countable _).image _).measurableSet

/-- Finite initial ladder blocks have the product BGW law. -/
theorem initial_blocks_law (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (j : ℕ) :
    (offspringSeqLaw μ).toMeasure.map (fun ω (i : Fin j) => blockLF ω i) =
      Measure.pi (fun _ : Fin j => bienaymeLaw μ.toMeasure) := by
  have h := congrArg (fun M : Measure (ℕ → LocallyFinite.Tree) =>
    M.map (fun F (i : Fin j) => F i)) (blockTrees_law μ hc hne)
  rw [Measure.map_map (by fun_prop) measurable_blockLF,
    Measure.map_infinitePi_infinitePi_of_inj Fin.val_injective, Measure.infinitePi_eq_pi] at h
  exact h

/-- The exploration completion kernel is the marked-count law of a BGW forest. -/
theorem completionMass_eq_forest (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (j n : ℕ) :
    completionMass μ A j n =
      (Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure) (markedForestEvent A j n) := by
  rw [← initial_blocks_law μ hc hne j,
    Measure.map_apply (Measurable.of_eval fun i => measurable_blockLF.eval)
      (measurableSet_markedForestEvent A j n)]
  apply measure_congr
  filter_upwards [ae_ladderFinite μ hc hne] with ω hω
  apply propext
  change completionMarks A j ω = n ↔
    (∀ i : Fin j, FiniteVertices (blockLF ω i)) ∧
      ∑ i : Fin j, zetaA A (blockLF ω i) = (n : ℕ∞)
  have hf : ∀ i : Fin j, FiniteVertices (blockLF ω i) :=
    fun i => (blockTree ω i).finiteVertices_toLocallyFinite
  rw [and_iff_right hf]
  simp only [blockLF, zetaA_toLocallyFinite, ← Nat.cast_sum,
    ENat.natCast_inj, completionMarks_eq_sum hω]

/-- Tree realization of the completion mark count of the first block. -/
theorem zetaA_first_block {ω : ℕ → ℕ} (hω : LadderFinite ω) (A : Set ℕ) :
    zetaA A (blockLF ω 0) = (completionMarks A 1 ω : ℕ∞) := by
  rw [completionMarks_eq_sum hω]
  simp [blockLF, zetaA_toLocallyFinite]

/-- **A-marked deterministic-prefix completion identity (C).**
The guard is necessary even when the remaining mark count is zero: truncated
natural subtraction alone does not express an impossible count. -/
theorem zetaAEvent_prefixCylinder_mass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (a : List ℕ) (n : ℕ) (hs : IsSurvivingPrefix a) :
    bienaymeLaw μ.toMeasure
        ({T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} ∩ prefixCylinder a.length a) =
      (a.map μ).prod * if prefixMarks A a ≤ n then
        (Measure.pi fun _ : Fin (prefixStack a) => bienaymeLaw μ.toMeasure)
          (markedForestEvent A (prefixStack a) (n - prefixMarks A a)) else 0 := by
  rw [← completionMass_eq_forest μ hc hne,
    ← completion_prefix_mass μ hc hne A a n hs,
    ← first_block_law μ hc hne,
    Measure.map_apply measurable_blockLF.eval
      ((measurableSet_zetaAEvent A n).inter (measurableSet_prefixCylinder _ _))]
  apply measure_congr
  filter_upwards [ae_ladderFinite μ hc hne] with ω hω
  apply propext
  change ((FiniteVertices (blockLF ω 0) ∧ zetaA A (blockLF ω 0) = (n : ℕ∞)) ∧
    FiniteVertices (blockLF ω 0) ∧ treePrefix a.length (blockLF ω 0) = a) ↔ _
  have hf := (blockTree ω 0).finiteVertices_toLocallyFinite
  rw [zetaA_first_block hω, ENat.natCast_inj]
  constructor
  · rintro ⟨⟨_, hn⟩, _, hp⟩
    have hlen : a.length ≤ ladderTime ω 1 := by
      have hl := congrArg List.length hp
      rw [blockLF, treePrefix_toLocallyFinite, List.length_take,
        PlaneTree.length_degrees, first_block_size hω] at hl
      omega
    rw [treePrefix_first_block hω _ hlen] at hp
    exact ⟨hp, hn⟩
  · rintro ⟨ha, hn⟩
    refine ⟨⟨hf, hn⟩, hf, ?_⟩
    rw [treePrefix_first_block hω _ (prefix_lt_ladderTime hω ha hs).le]
    exact ha

/-- Real-valued version of (C), for use in prefix densities. -/
theorem zetaAEvent_prefixCylinder_real (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (a : List ℕ) (n : ℕ) (hs : IsSurvivingPrefix a) :
    (bienaymeLaw μ.toMeasure).real
        ({T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} ∩ prefixCylinder a.length a) =
      degreeWeight μ a * if prefixMarks A a ≤ n then
        ((Measure.pi fun _ : Fin (prefixStack a) => bienaymeLaw μ.toMeasure)
          (markedForestEvent A (prefixStack a) (n - prefixMarks A a))).toReal else 0 := by
  rw [measureReal_def, zetaAEvent_prefixCylinder_mass μ hc hne A a n hs, ENNReal.toReal_mul]
  split_ifs <;> rfl

end BGWLeaves.GeneralAFunctional.TreePrefix
