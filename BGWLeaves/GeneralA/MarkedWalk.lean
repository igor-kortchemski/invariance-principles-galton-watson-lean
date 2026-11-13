module

public import BGWLeaves.GeneralA.Marked

/-! Measure-valued marked-word sums and their two-color convolution recurrence. -/

@[expose] public section

namespace BGWLeaves.GeneralA.MarkedWalk

open MeasureTheory BGW BGWLeaves.StableAnalysis
open scoped ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The weighted step measure `∑ₖ w k • δ_{k-1}` on `ℤ`. -/
noncomputable def weightedStep (w : ℕ → ℝ≥0∞) : Measure ℤ :=
  Measure.sum fun k => w k • Measure.dirac ((k : ℤ) - 1)

/-- The part of `weightedStep w` carried by the jumps `k - 1` with `k ∈ A`. -/
noncomputable def markedStep (w : ℕ → ℝ≥0∞) (A : Set ℕ) : Measure ℤ :=
  weightedStep fun k => if k ∈ A then w k else 0

/-- The part of `weightedStep w` carried by the jumps `k - 1` with `k ∉ A`. -/
noncomputable def unmarkedStep (w : ℕ → ℝ≥0∞) (A : Set ℕ) : Measure ℤ :=
  markedStep w Aᶜ

/-- Number of coordinates of the offspring vector `ω` that lie in `A`. -/
noncomputable def markCount (A : Set ℕ) {p : ℕ} (ω : Fin p → ℕ) : ℕ :=
  (Finset.univ.filter fun i => ω i ∈ A).card

/-- The sum `∑ᵢ (ω i - 1)` of the Łukasiewicz increments of an offspring vector. -/
def wordSum {p : ℕ} (ω : Fin p → ℕ) : ℤ := ∑ i, ((ω i : ℤ) - 1)

/-- The measure on `ℤ` that puts mass `∏ᵢ w (ω i)` at `wordSum ω` for each offspring vector `ω` of length `p` with exactly `n` coordinates in `A`. -/
noncomputable def markedWalk (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p n : ℕ) : Measure ℤ :=
  Measure.sum fun ω : Fin p → ℕ =>
    (if markCount A ω = n then ∏ i, w (ω i) else 0) • Measure.dirac (wordSum ω)

private instance weightedStep_sfinite (w : ℕ → ℝ≥0∞) : SFinite (weightedStep w) := by
  unfold weightedStep
  infer_instance

private instance markedWalk_sfinite (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p n : ℕ) :
    SFinite (markedWalk w A p n) := by
  unfold markedWalk
  infer_instance

private theorem conv_sums_dirac {ι κ : Type*} [Countable κ]
    (u : ι → ℝ≥0∞) (v : κ → ℝ≥0∞) (a : ι → ℤ) (b : κ → ℤ) :
    (Measure.sum fun i => u i • Measure.dirac (a i)).conv
        (Measure.sum fun j => v j • Measure.dirac (b j)) =
      Measure.sum fun p : ι × κ => (u p.1 * v p.2) • Measure.dirac (a p.1 + b p.2) := by
  rw [Measure.conv, Measure.prod_sum, Measure.map_sum (by fun_prop)]
  congr 1
  funext p
  change (u p.1 • Measure.dirac (a p.1)).conv (v p.2 • Measure.dirac (b p.2)) = _
  rw [Measure.conv_smul_left, Measure.conv_smul_right, smul_smul, Measure.dirac_conv_dirac]

private def finConsEquiv (p : ℕ) : (ℕ × (Fin p → ℕ)) ≃ (Fin (p + 1) → ℕ) where
  toFun x := Fin.cons x.1 x.2
  invFun ω := (ω 0, fun i => ω i.succ)
  left_inv x := by rcases x with ⟨a, ω⟩; rfl
  right_inv ω := by ext i; refine Fin.cases ?_ ?_ i <;> simp

private theorem markCount_cons (A : Set ℕ) {p : ℕ} (a : ℕ) (ω : Fin p → ℕ) :
    markCount A (Fin.cons a ω) = (if a ∈ A then 1 else 0) + markCount A ω := by
  unfold markCount
  rw [Finset.card_filter]
  change (∑ i : Fin (p + 1), if (@Fin.cons p (fun _ => ℕ) a ω) i ∈ A then 1 else 0) = _
  rw [Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

private theorem wordSum_cons {p : ℕ} (a : ℕ) (ω : Fin p → ℕ) :
    wordSum (Fin.cons a ω) = ((a : ℤ) - 1) + wordSum ω := by
  simp [wordSum, Fin.sum_univ_succ]
  ring

theorem markedWalk_succ_zero (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p : ℕ) :
    markedWalk w A (p + 1) 0 = (unmarkedStep w A).conv (markedWalk w A p 0) := by
  unfold markedWalk unmarkedStep markedStep weightedStep
  rw [conv_sums_dirac, ← Measure.sum_comp_equiv (finConsEquiv p)]
  congr 1
  funext x
  rcases x with ⟨a, ω⟩
  by_cases ha : a ∈ A
  · simp [finConsEquiv, markCount_cons, ha, Fin.prod_univ_succ]
  · simp [finConsEquiv, markCount_cons, ha, Fin.prod_univ_succ, wordSum_cons]

theorem markedWalk_succ_succ (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p n : ℕ) :
    markedWalk w A (p + 1) (n + 1) =
      (markedStep w A).conv (markedWalk w A p n) +
        (unmarkedStep w A).conv (markedWalk w A p (n + 1)) := by
  unfold markedWalk unmarkedStep markedStep weightedStep
  rw [conv_sums_dirac, conv_sums_dirac, Measure.sum_add_sum,
    ← Measure.sum_comp_equiv (finConsEquiv p)]
  congr 1
  funext x
  rcases x with ⟨a, ω⟩
  by_cases ha : a ∈ A
  · have hcnt : 1 + markCount A ω = n + 1 ↔ markCount A ω = n := by omega
    simp [finConsEquiv, markCount_cons, ha, Fin.prod_univ_succ, wordSum_cons, hcnt]
  · simp [finConsEquiv, markCount_cons, ha, Fin.prod_univ_succ, wordSum_cons]

private instance intWalk_sfinite (ν : Measure ℤ) [SFinite ν] (p : ℕ) : SFinite (intWalk ν p) := by
  induction p with
  | zero => simp only [intWalk]; infer_instance
  | succ p ih => simpa only [intWalk] using (inferInstance : SFinite ((intWalk ν p).conv ν))

private instance markedStep_sfinite (w : ℕ → ℝ≥0∞) (A : Set ℕ) : SFinite (markedStep w A) := by
  unfold markedStep
  infer_instance

private instance unmarkedStep_sfinite (w : ℕ → ℝ≥0∞) (A : Set ℕ) : SFinite (unmarkedStep w A) := by
  unfold unmarkedStep
  infer_instance

theorem markedWalk_zero (w : ℕ → ℝ≥0∞) (A : Set ℕ) (n : ℕ) :
    markedWalk w A 0 n = if n = 0 then Measure.dirac 0 else 0 := by
  ext s hs
  simp [markedWalk, markCount, wordSum, eq_comm]

theorem markedWalk_eq_zero_of_lt (w : ℕ → ℝ≥0∞) (A : Set ℕ) {p n : ℕ} (hpn : p < n) :
    markedWalk w A p n = 0 := by
  have hz : ∀ ω : Fin p → ℕ, markCount A ω ≠ n := by
    intro ω he
    have hle : markCount A ω ≤ p := by
      exact (Finset.card_filter_le _ _).trans_eq (Finset.card_univ.trans (Fintype.card_fin p))
    omega
  simp [markedWalk, hz]

private theorem markedWalk_zero_marks (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p : ℕ) :
    markedWalk w A p 0 = intWalk (unmarkedStep w A) p := by
  induction p with
  | zero => simp [markedWalk_zero, intWalk]
  | succ p ih =>
    rw [markedWalk_succ_zero, ih, Measure.conv_comm]
    rfl

private theorem markedWalk_all_marks (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p : ℕ) :
    markedWalk w A p p = intWalk (markedStep w A) p := by
  induction p with
  | zero => simp [markedWalk_zero, intWalk]
  | succ p ih =>
    rw [markedWalk_succ_succ, ih, markedWalk_eq_zero_of_lt w A (Nat.lt_succ_self p)]
    simp only [Measure.conv_zero, add_zero]
    rw [Measure.conv_comm]
    rfl

private theorem conv_walk_marked (α β : Measure ℤ) [SFinite α] [SFinite β] (n k : ℕ) :
    α.conv ((intWalk α n).conv (intWalk β k)) = (intWalk α (n + 1)).conv (intWalk β k) := by
  rw [← Measure.conv_assoc, Measure.conv_comm α (intWalk α n)]
  rfl

private theorem conv_walk_unmarked (α β : Measure ℤ) [SFinite α] [SFinite β] (n k : ℕ) :
    β.conv ((intWalk α n).conv (intWalk β k)) = (intWalk α n).conv (intWalk β (k + 1)) := by
  rw [Measure.conv_comm β, Measure.conv_assoc]
  rfl

/-- Binomial factorization before normalization by the two class masses. It
continues to hold when either class has mass zero. -/
theorem markedWalk_binomial (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p n : ℕ) :
    markedWalk w A p n = (p.choose n : ℝ≥0∞) •
      ((intWalk (markedStep w A) n).conv (intWalk (unmarkedStep w A) (p - n))) := by
  induction p generalizing n with
  | zero =>
    by_cases hn : n = 0
    · subst n
      simp [markedWalk_zero, intWalk]
    · rw [markedWalk_eq_zero_of_lt w A (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      simp
  | succ p ih =>
    by_cases hnp : n ≤ p + 1
    · rcases n with _ | n
      · simp [markedWalk_zero_marks, intWalk]
      · by_cases hn : n = p
        · subst n
          simp [markedWalk_all_marks, intWalk]
        · have hnle : n + 1 ≤ p := by omega
          rw [markedWalk_succ_succ, ih n, ih (n + 1), Measure.conv_smul_right,
            Measure.conv_smul_right, conv_walk_marked, conv_walk_unmarked]
          rw [show p - (n + 1) + 1 = p - n by omega, Nat.succ_sub_succ]
          rw [← add_smul, ← Nat.cast_add, ← Nat.choose_succ_succ]
    · rw [markedWalk_eq_zero_of_lt w A (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      simp

theorem markedStep_add_unmarkedStep (w : ℕ → ℝ≥0∞) (A : Set ℕ) :
    markedStep w A + unmarkedStep w A = weightedStep w := by
  unfold unmarkedStep markedStep weightedStep
  rw [Measure.sum_add_sum]
  congr 1
  funext k
  by_cases hk : k ∈ A <;> simp [hk]

theorem markedWalk_apply_bridge (w : ℕ → ℝ≥0∞) (A : Set ℕ) (p n : ℕ) :
    markedWalk w A p n {(-1 : ℤ)} =
      ∑' ω : Fin p → ℕ, (Marked.markedForestBridges A 1 p n).indicator
        (fun ω => ∏ i, w (ω i)) ω := by
  rw [markedWalk, Measure.sum_apply _ (measurableSet_singleton _)]
  apply tsum_congr
  intro ω
  have hs : wordSum ω = -1 ↔ (∑ i, ω i) + 1 = p := by
    simp only [wordSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, mul_one, ← Nat.cast_sum]
    omega
  by_cases hn : markCount A ω = n
  · have hn' := hn
    unfold markCount at hn'
    rw [ite_eq_left hn, Measure.smul_apply, smul_eq_mul]
    by_cases hsum : wordSum ω = -1
    · simp [hsum, Set.indicator, Marked.markedForestBridges, hn', hs.mp hsum]
    · simp [hsum, Set.indicator, Marked.markedForestBridges, hn', mt hs.mpr hsum]
  · have hn' := hn
    unfold markCount at hn'
    simp [hn', Set.indicator, Marked.markedForestBridges, markCount]

end
end BGWLeaves.GeneralA.MarkedWalk
