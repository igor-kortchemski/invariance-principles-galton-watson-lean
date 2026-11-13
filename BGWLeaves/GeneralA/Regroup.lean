module

public import BGWLeaves.GeneralA.MarkedWalk
public import Mathlib.Data.Nat.Choose.Sum

/-! Negative-binomial regrouping for marked-time increments, without normalized
conditional measures. Zero mass of the unmarked class needs no special convention. -/

@[expose] public section

namespace BGWLeaves.GeneralA.Regroup

open MeasureTheory BGWLeaves.StableAnalysis
open scoped ENNReal

noncomputable section

private instance walk_sfinite (ν : Measure ℤ) [SFinite ν] (n : ℕ) : SFinite (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using (inferInstance : SFinite ((intWalk ν n).conv ν))

/-- `α` convolved with the renewal measure `∑ₖ β^{*k}`. -/
noncomputable def blockLaw (α β : Measure ℤ) : Measure ℤ :=
  α.conv (Measure.sum fun k : ℕ => intWalk β k)

private instance blockLaw_sfinite (α β : Measure ℤ) [SFinite α] [SFinite β] :
    SFinite (blockLaw α β) := by unfold blockLaw; infer_instance

theorem conv_sum_right {ι : Type*} [Countable ι] (μ : Measure ℤ) (ν : ι → Measure ℤ)
    [∀ i, SFinite (ν i)] :
    μ.conv (Measure.sum ν) = Measure.sum fun i => μ.conv (ν i) := by
  rw [Measure.conv, Measure.prod_sum_right, Measure.map_sum (by fun_prop)]
  rfl

theorem conv_sum_left {ι : Type*} (μ : ι → Measure ℤ) (ν : Measure ℤ) [SFinite ν] :
    (Measure.sum μ).conv ν = Measure.sum fun i => (μ i).conv ν := by
  rw [Measure.conv, Measure.prod_sum_left, Measure.map_sum (by fun_prop)]
  rfl

private theorem walk_add (ν : Measure ℤ) [SFinite ν] (i j : ℕ) :
    intWalk ν (i + j) = (intWalk ν i).conv (intWalk ν j) := by
  induction j with
  | zero => simp [intWalk, Measure.conv_dirac]
  | succ j ih => rw [Nat.add_succ, intWalk, ih, Measure.conv_assoc]; rfl

private theorem conv_left_comm (a b c : Measure ℤ) [SFinite a] [SFinite b] [SFinite c] :
    a.conv (b.conv c) = b.conv (a.conv c) := by
  rw [← Measure.conv_assoc, Measure.conv_comm a b, Measure.conv_assoc]

private theorem conv_four (a b c d : Measure ℤ)
    [SFinite a] [SFinite b] [SFinite c] [SFinite d] :
    (a.conv b).conv (c.conv d) = (a.conv c).conv (b.conv d) := by
  rw [Measure.conv_assoc, conv_left_comm b c d, ← Measure.conv_assoc]

private theorem sum_pairs_by_add (f : ℕ × ℕ → Measure ℤ) :
    Measure.sum f = Measure.sum fun k : ℕ => ∑ p ∈ Finset.antidiagonal k, f p := by
  classical
  ext s hs
  simp only [Measure.sum_apply _ hs, Measure.finsetSum_apply]
  rw [← Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd.tsum_eq (fun p => f p s),
    ENNReal.tsum_sigma']
  apply tsum_congr
  intro k
  simp only [Finset.HasAntidiagonal.sigmaAntidiagonalEquivProd, tsum_fintype]
  exact Finset.sum_attach _ (fun p => f p s)

private theorem choose_antidiagonal (n k : ℕ) :
    (∑ p ∈ Finset.antidiagonal k, ((p.1 + n).choose n : ℝ≥0∞)) =
      ((k + n + 1).choose (n + 1) : ℝ≥0∞) := by
  have h : (∑ p ∈ Finset.antidiagonal k, (p.1 + n).choose n) =
      (k + n + 1).choose (n + 1) := by
    rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact Nat.sum_range_add_choose k n
  exact_mod_cast h

/-- `n+1` marked-time increments are the negative-binomial mixture of walks
with `n+1` marked letters and `k` unmarked letters. -/
theorem blockLaw_walk (α β : Measure ℤ) [SFinite α] [SFinite β] (n : ℕ) :
    intWalk (blockLaw α β) (n + 1) =
      Measure.sum fun k : ℕ => ((k + n).choose n : ℝ≥0∞) •
        ((intWalk α (n + 1)).conv (intWalk β k)) := by
  classical
  induction n with
  | zero => simp [intWalk, blockLaw, conv_sum_right]
  | succ n ih =>
    rw [intWalk, ih, blockLaw, conv_sum_right, conv_sum_left]
    simp_rw [conv_sum_right]
    rw [Measure.sum_sum, sum_pairs_by_add]
    congr 1
    funext k
    have he : ∀ p ∈ Finset.antidiagonal k,
        (((p.1 + n).choose n : ℝ≥0∞) • ((intWalk α (n + 1)).conv (intWalk β p.1))).conv
          (α.conv (intWalk β p.2)) =
        ((p.1 + n).choose n : ℝ≥0∞) • ((intWalk α (n + 1 + 1)).conv (intWalk β k)) := by
      intro p hp
      rw [Measure.conv_smul_left, conv_four, ← walk_add,
        Finset.mem_antidiagonal.mp hp]
      rfl
    rw [Finset.sum_congr rfl he, ← Finset.sum_smul, choose_antidiagonal]
    rfl

end
end BGWLeaves.GeneralA.Regroup
