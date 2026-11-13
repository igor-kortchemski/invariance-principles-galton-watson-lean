module

public import BGWLeaves.GeneralAFunctional.TreeAugmented
public import BGWLeaves.GeneralAFunctional.TreePrefixSupport
public import BGWLeaves.GeneralAFunctional.TreeResidue
public import BGW.StableTrees.ExactPairLocality

/-! Recovering the marked prefix density from the augmented path state. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreePathDensity

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGW.StableTrees.TailPair BGW.StableTrees.PathTail BGW.Skorokhod
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralAFunctional.TreePrefixMeasure BGWLeaves.GeneralAFunctional.TreePrefixSupport
open BGWLeaves.GeneralAFunctional.TreeAugmented BGWLeaves.GeneralAFunctional.TreeClocks
open BGWLeaves.GeneralAFunctional.TreeKernel BGWLeaves.GeneralAFunctional.TreeResidue
open scoped ENNReal NNReal Topology Classical

noncomputable def recoveredMarks (n : ℕ) {b : ℝ≥0} (z : PairSpace b × ℝ) : ℕ := ⌊z.2 * n⌋₊

noncomputable def rawStack (B : ℕ → ℝ) (r : ℕ) (b : ℝ≥0) (z : PairSpace b × ℝ) : ℕ :=
  ⌊DiscreteBridge.endValue b z.1.1 * B r⌋₊ + 1

noncomputable def recoveredStack (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ)
    (n r : ℕ) (b : ℝ≥0) (z : PairSpace b × ℝ) : ℕ :=
  pendingProject (arithFactor μ A) n (recoveredMarks n z) (rawStack B r b z)

noncomputable def pathWeight (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ)
    (n r : ℕ) (b : ℝ≥0) (z : PairSpace b × ℝ) : ℝ :=
  if recoveredMarks n z ≤ n then
    max (kernelDensity μ A n r (prefixLength b r) (recoveredMarks n z)
      (recoveredStack μ A B n r b z)) 0 else 0

theorem measurable_recoveredMarks (n : ℕ) (b : ℝ≥0) :
    Measurable (recoveredMarks n (b := b)) := by
  have hm : Measurable (fun z : PairSpace b × ℝ => z.2 * (n : ℝ)) := measurable_snd.mul_const _
  exact hm.nat_floor

theorem measurable_rawStack (B : ℕ → ℝ) (r : ℕ) (b : ℝ≥0) :
    Measurable (rawStack B r b) :=
  ((((measurable_evalEnd b).comp (measurable_fst.comp measurable_fst)).mul_const (B r)).nat_floor).add_const 1

theorem measurable_recoveredStack (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ)
    (n r : ℕ) (b : ℝ≥0) : Measurable (recoveredStack μ A B n r b) :=
  (measurable_of_countable (fun p : ℕ × ℕ => pendingProject (arithFactor μ A) n p.1 p.2)).comp
    ((measurable_recoveredMarks n b).prodMk (measurable_rawStack B r b))

theorem measurable_pathWeight (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ)
    (n r : ℕ) (b : ℝ≥0) : Measurable (pathWeight μ A B n r b) := by
  have hk := measurable_recoveredMarks n b
  have hj := measurable_recoveredStack μ A B n r b
  exact Measurable.ite (measurableSet_le hk measurable_const)
    (((measurable_of_countable (fun p : ℕ × ℕ =>
      kernelDensity μ A n r (prefixLength b r) p.1 p.2)).comp (hk.prodMk hj)).max measurable_const)
    measurable_const

theorem pathWeight_nonneg (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ)
    (n r : ℕ) (b : ℝ≥0) (z : PairSpace b × ℝ) : 0 ≤ pathWeight μ A B n r b z := by
  unfold pathWeight
  split_ifs
  · exact le_max_right _ _
  · rfl

theorem recoveredMarks_augmented (A : Set ℕ) (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (r : ℕ) (b : ℝ≥0) (T : LocallyFinite.Tree) :
    recoveredMarks n (augmentedMap A B n r b T) = prefixMarks A (treePrefix (prefixLength b r) T) := by
  unfold recoveredMarks augmentedMap
  dsimp only
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [div_mul_cancel₀ _ hnR, Nat.floor_natCast]

theorem endValue_treePair (B : ℕ → ℝ) (r : ℕ) (b : ℝ≥0) (t : PlaneTree) :
    DiscreteBridge.endValue b (treePairPath B r b t.toLocallyFinite).1 =
      (prefixWalk (treePrefix (prefixLength b r) t.toLocallyFinite) : ℝ) / B r := by
  change BGW.Probability.RealWalk.partialSum (treeIncrementSeq t.toLocallyFinite)
    ⌊(r : ℝ) * (b : ℝ)⌋₊ / B r = _
  simp only [BGW.Probability.RealWalk.partialSum, treeIncrementSeq,
    ExactPrefix.treeIncrements_toLocallyFinite, ExactPrefix.sum_range_getD, treePrefix_toLocallyFinite,
    prefixWalk_eq_sum_steps, PlaneTree.increments, ← List.map_take, mul_comm (r : ℝ), prefixLength]

theorem rawStack_augmented (A : Set ℕ) (B : ℕ → ℝ) (n r : ℕ) (b : ℝ≥0)
    (hB : B r ≠ 0) (t : PlaneTree)
    (hs : IsSurvivingPrefix (treePrefix (prefixLength b r) t.toLocallyFinite)) :
    rawStack B r b (augmentedMap A B n r b t.toLocallyFinite) =
      prefixStack (treePrefix (prefixLength b r) t.toLocallyFinite) := by
  let a := treePrefix (prefixLength b r) t.toLocallyFinite
  have hc : (prefixStack a : ℤ) = prefixWalk a + 1 := prefixStack_cast hs
  have hp : 1 ≤ prefixStack a := prefixStack_pos hs
  have hv : prefixWalk a = ((prefixStack a - 1 : ℕ) : ℤ) := by omega
  unfold rawStack augmentedMap
  dsimp only
  rw [endValue_treePair, div_mul_cancel₀ _ hB]
  change ⌊(prefixWalk a : ℝ)⌋₊ + 1 = prefixStack a
  rw [hv, Int.cast_natCast, Nat.floor_natCast]
  omega

/-- On supported surviving prefixes the projected path density equals the
exact finite-word density. Impossible revealed mark counts give zero on both sides. -/
theorem pathWeight_augmented (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (B : ℕ → ℝ) {n r : ℕ} (hn : ZetaAAdmissible μ A n)
    (hn0 : 0 < n) (hB : B r ≠ 0) (b : ℝ≥0) (t : PlaneTree)
    (hg : treePrefix (prefixLength b r) t.toLocallyFinite ∈ goodWords (prefixLength b r))
    (hμ : ∀ d ∈ treePrefix (prefixLength b r) t.toLocallyFinite, μ d ≠ 0) :
    pathWeight μ A B n r b (augmentedMap A B n r b t.toLocallyFinite) =
      TreeDensity.prefixDensity μ A n r (treePrefix (prefixLength b r) t.toLocallyFinite) := by
  let a := treePrefix (prefixLength b r) t.toLocallyFinite
  have hlen : a.length = prefixLength b r := hg.1
  have hs : IsSurvivingPrefix a := hg.2
  unfold pathWeight recoveredStack
  rw [recoveredMarks_augmented A B hn0, rawStack_augmented A B n r b hB t hs]
  change (if prefixMarks A a ≤ n then
    max (kernelDensity μ A n r (prefixLength b r) (prefixMarks A a)
      (pendingProject (arithFactor μ A) n (prefixMarks A a) (prefixStack a))) 0 else 0) =
      TreeDensity.prefixDensity μ A n r a
  by_cases hkn : prefixMarks A a ≤ n
  · rw [ite_eq_left hkn, pendingProject_prefix hc hne hn hs hμ hkn,
      show kernelDensity μ A n r (prefixLength b r) (prefixMarks A a) (prefixStack a) =
          TreeDensity.prefixDensity μ A n r a from by
        rw [← hlen]; exact (prefixDensity_eq_kernelDensity μ A n r a hkn).symm]
    apply max_eq_left
    unfold TreeDensity.prefixDensity remainingMass
    rw [ite_eq_left hkn]
    apply mul_nonneg
    · exact div_nonneg (forestTail_pos μ hc hne r).le (markedMass_pos hn).le
    · exact div_nonneg ENNReal.toReal_nonneg
        (TreeTailPositive.forestTail_stack_pos μ hc hne (prefixStack_pos hs) _).le
  · rw [ite_eq_right hkn]
    simp only [TreeDensity.prefixDensity, remainingMass, ite_eq_right hkn, zero_div, mul_zero]

end BGWLeaves.GeneralAFunctional.TreePathDensity
