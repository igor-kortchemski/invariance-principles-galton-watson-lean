module

public import BGWLeaves.GeneralAFunctional.TreeDensity

/-! Positive total-size forest-tail denominators for every pending stack. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeTailPositive

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.GeneralAFunctional.TreeDensity
open scoped ENNReal Classical

theorem forestHit_iff_ladderTime {ω : ℕ → ℕ} (hω : LadderFinite ω) (j r : ℕ) :
    ω ∈ forestHit j r ↔ DiscreteForest.ladderTime ω j = r := by
  constructor
  · rintro ⟨hhit, hpre⟩
    have hle : DiscreteForest.ladderTime ω j ≤ r := Nat.sInf_le hhit
    by_contra hne
    have ht := hpre (DiscreteForest.ladderTime ω j) (by omega)
    rw [walk_ladderTime hω] at ht
    omega
  · intro he
    refine ⟨?_, fun i hi => ?_⟩
    · rw [← he, walk_ladderTime hω]
    · exact walk_gt_of_lt_ladderTime hω (by omega)

/-- Forest-tail mass is the tail of the corresponding ladder time. -/
theorem forestTail_eq_ladderTime_tail (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {j : ℕ} (hj : 1 ≤ j) (r : ℕ) :
    forestTail μ j r = (offspringSeqLaw μ).toMeasure.real {ω | r ≤ DiscreteForest.ladderTime ω j} := by
  have heq : {ω | r ≤ DiscreteForest.ladderTime ω j} =ᵐ[(offspringSeqLaw μ).toMeasure]
      ⋃ k : ℕ, (if r ≤ k then forestHit j k else ∅) := by
    filter_upwards [ae_ladderFinite μ hc hne] with ω hω
    apply propext
    constructor
    · intro hr
      exact mem_iUnion.mpr ⟨DiscreteForest.ladderTime ω j, by
        rw [ite_eq_left hr]
        exact (forestHit_iff_ladderTime hω j _).mpr rfl⟩
    · intro h
      obtain ⟨k, hk⟩ := mem_iUnion.mp h
      split_ifs at hk with hr
      · rw [(forestHit_iff_ladderTime hω j k).mp hk]
        exact hr
      · exact False.elim hk
  have hdisj : Pairwise (fun k l : ℕ => Disjoint
      (if r ≤ k then forestHit j k else ∅) (if r ≤ l then forestHit j l else ∅)) := by
    intro k l hkl
    split_ifs with hk hl <;> try simp
    apply Set.disjoint_left.mpr
    intro ω hωk hωl
    rcases lt_or_gt_of_ne hkl with h | h
    · have ht := hωl.2 k h
      rw [hωk.1] at ht
      omega
    · have ht := hωk.2 l h
      rw [hωl.1] at ht
      omega
  have hm (k : ℕ) : MeasurableSet (if r ≤ k then forestHit j k else ∅) := by
    split_ifs
    · exact measurableSet_forestHit j k
    · exact MeasurableSet.empty
  rw [measureReal_def, measure_congr heq, measure_iUnion hdisj hm,
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]
  unfold forestTail forestMass
  apply tsum_congr
  intro k
  by_cases hk : r ≤ k
  · rw [ite_eq_left hk, forestHit_mass μ hj]
    exact Set.indicator_of_mem hk _
  · rw [ite_eq_right hk, measure_empty, ENNReal.toReal_zero]
    exact Set.indicator_of_notMem hk _

/-- Adding pending trees can only increase a total-size tail. -/
theorem forestTail_one_le (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {j : ℕ} (hj : 1 ≤ j) (r : ℕ) : forestTail μ 1 r ≤ forestTail μ j r := by
  rw [forestTail_eq_ladderTime_tail μ hc hne le_rfl,
    forestTail_eq_ladderTime_tail μ hc hne hj]
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_ladderFinite μ hc hne] with ω hω
  intro hr
  have hmono : Monotone (DiscreteForest.ladderTime ω) :=
    (strictMono_nat_of_lt_succ (ladderTime_lt_succ hω)).monotone
  exact hr.trans (hmono hj)

theorem forestTail_stack_pos (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {j : ℕ} (hj : 1 ≤ j) (r : ℕ) : 0 < forestTail μ j r :=
  (forestTail_pos μ hc hne r).trans_le (forestTail_one_le μ hc hne hj r)

/-- The marked prefix RN identity has positive tail denominators automatically. -/
theorem markedPrefixMass_eq_density_mul (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (a : List ℕ) (n r : ℕ) (hn : ZetaAAdmissible μ A n)
    (har : a.length < r) (hs : IsSurvivingPrefix a) :
    (zetaATreeLaw μ A n).toMeasure.real (prefixCylinder a.length a) =
      TreeDensity.prefixDensity μ A n r a *
        (tailTreeLaw μ r).toMeasure.real (prefixCylinder a.length a) :=
  TreeDensity.markedPrefixMass_eq_density_mul μ hc hne A a n r hn har hs
    (forestTail_stack_pos μ hc hne (prefixStack_pos hs) _)

end BGWLeaves.GeneralAFunctional.TreeTailPositive
