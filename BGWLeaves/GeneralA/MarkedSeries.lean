module

public import BGWLeaves.GeneralA.MarkedLaw
public import BGWLeaves.GeneralA.Regroup

/-! The marked tree probability series in unnormalized walk form. -/

@[expose] public section

namespace BGWLeaves.GeneralA.MarkedSeries

open MeasureTheory BGW BGW.StableTrees BGWLeaves.StableAnalysis Marked MarkedLaw MarkedWalk
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Total weight of the plane trees with `p` vertices and exactly `n` vertices whose number of children lies in `A`. -/
noncomputable def treeAWeight (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p n : ℕ) : ℝ≥0∞ :=
  ∑' t : PlaneTree, if t.size = p ∧ treeACount A t = n then PlaneTree.weight w t else 0

private theorem forestAWeight_one (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p n : ℕ) :
    forestAWeight A w 1 p n = treeAWeight w A p n := by
  rw [forestAWeight_eq_tsum_fin]
  let g : PlaneTree → (Fin 1 → PlaneTree) := fun t _ => t
  have hinj : Function.Injective g := fun _ _ h => congrFun h 0
  have hrange : Function.support (fun f : Fin 1 → PlaneTree =>
      if (∑ i, (f i).size = p) ∧ (∑ i, treeACount A (f i) = n) then
        ∏ i, PlaneTree.weight w (f i) else 0) ⊆ Set.range g := by
    intro f _
    refine ⟨f 0, ?_⟩
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  rw [← hinj.tsum_eq hrange]
  apply tsum_congr
  intro t
  simp [g]

/-- Arbitrary-mark Kemperman identity for one finite tree, before division by size. -/
theorem natCast_mul_treeAWeight (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p n : ℕ) :
    (p : ℝ≥0∞) * treeAWeight w A p n = markedWalk w A p n {(-1 : ℤ)} := by
  rw [← forestAWeight_one, Marked.natCast_mul_forestAWeight A w (by norm_num : 1 ≤ 1) p n]
  simpa only [Nat.cast_one, one_mul] using (markedWalk_apply_bridge w A p n).symm

private theorem treeAWeight_zero (w : ℕ → ℝ≥0∞) (A : Set ℕ) (n : ℕ) :
    treeAWeight w A 0 n = 0 := by
  simp [treeAWeight, (PlaneTree.size_pos _).ne']

private theorem treeAWeight_eq_walk (w : ℕ → ℝ≥0∞) (A : Set ℕ) {p : ℕ} (hp : 0 < p) (n : ℕ) :
    treeAWeight w A p n = (p : ℝ≥0∞)⁻¹ * markedWalk w A p n {(-1 : ℤ)} := by
  rw [← natCast_mul_treeAWeight, ← mul_assoc,
    ENNReal.inv_mul_cancel (by exact_mod_cast hp.ne') (by simp), one_mul]

/-- The total marked-count law is the sum over all total sizes of the marked
Kemperman terms. This also covers `0 ∉ A`; only the count index is positive. -/
theorem zetaA_series {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) {n : ℕ} (hn : 0 < n) :
    LocallyFinite.bienaymeLaw μ.toMeasure {T | zetaA A T = (n : ℕ∞)} =
      ∑' p : ℕ, (p : ℝ≥0∞)⁻¹ * markedWalk (fun k => μ k) A p n {(-1 : ℤ)} := by
  rw [bienaymeLaw_zetaA_eq_tsum A hc hne]
  have hs : (∑' t : PlaneTree, if treeACount A t = n then PlaneTree.weight (fun k => μ k) t else 0) =
      ∑' p, treeAWeight (fun k => μ k) A p n := by
    simp only [treeAWeight]
    rw [ENNReal.tsum_comm]
    apply tsum_congr
    intro t
    rw [tsum_eq_single t.size]
    · simp
    · intro p hp
      simp [Ne.symm hp]
  rw [hs]
  apply tsum_congr
  intro p
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · rw [treeAWeight_zero, markedWalk_zero]
    simp [hn.ne']
  · exact treeAWeight_eq_walk _ _ hp n

private theorem choose_weight (n k : ℕ) :
    ((k + n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ((k + n + 1).choose (n + 1) : ℝ≥0∞) =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * ((k + n).choose n : ℝ≥0∞) := by
  have hp : ((k + n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  have hn : ((n + 1 : ℕ) : ℝ≥0∞) ≠ 0 := by positivity
  apply (ENNReal.toReal_eq_toReal_iff' (by finiteness) (by finiteness)).1
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have h := Nat.add_one_mul_choose_eq (k + n) n
  have hr : ((k + n + 1 : ℕ) : ℝ) * ((k + n).choose n : ℝ) =
      ((k + n + 1).choose (n + 1) : ℝ) * ((n + 1 : ℕ) : ℝ) := by exact_mod_cast h
  have hpR : ((k + n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hnR : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  nlinarith [hr]

/-- Exact marked-time identity for every positive count. The block increment
consists of an A-step and any number of unmarked steps. -/
theorem zetaA_blockLaw {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (n : ℕ) :
    LocallyFinite.bienaymeLaw μ.toMeasure {T | zetaA A T = ((n + 1 : ℕ) : ℕ∞)} =
      ((n + 1 : ℕ) : ℝ≥0∞)⁻¹ *
        intWalk (Regroup.blockLaw (markedStep (fun k => μ k) A)
          (unmarkedStep (fun k => μ k) A)) (n + 1) {(-1 : ℤ)} := by
  have : SFinite (markedStep (fun k => μ k) A) := by
    unfold markedStep weightedStep
    infer_instance
  have : SFinite (unmarkedStep (fun k => μ k) A) := by
    unfold unmarkedStep markedStep weightedStep
    infer_instance
  rw [zetaA_series hc hne A (by omega : 0 < n + 1)]
  let f : ℕ → ℝ≥0∞ := fun p => (p : ℝ≥0∞)⁻¹ *
    markedWalk (fun k => μ k) A p (n + 1) {(-1 : ℤ)}
  have hs : Function.support f ⊆ Set.range (fun k : ℕ => k + (n + 1)) := by
    intro p hp
    have hle : n + 1 ≤ p := by
      by_contra h
      apply hp
      simp [f, markedWalk_eq_zero_of_lt (fun k => μ k) A (by omega : p < n + 1)]
    exact ⟨p - (n + 1), Nat.sub_add_cancel hle⟩
  have he := (show Function.Injective (fun k : ℕ => k + (n + 1)) from
    fun _ _ h => Nat.add_right_cancel h).tsum_eq hs
  change (∑' p, f p) = _
  rw [← he, Regroup.blockLaw_walk, Measure.sum_apply _ (measurableSet_singleton _),
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro k
  dsimp [f]
  rw [markedWalk_binomial]
  simp only [Nat.add_sub_cancel, Measure.smul_apply, smul_eq_mul]
  rw [← mul_assoc, ← mul_assoc]
  rw [show k + (n + 1) = k + n + 1 by omega, choose_weight]

end
end BGWLeaves.GeneralA.MarkedSeries
