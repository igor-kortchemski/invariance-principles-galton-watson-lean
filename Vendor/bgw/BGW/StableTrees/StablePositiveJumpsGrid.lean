/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableLocalMarkov

/-!
# Grid increments of the local stable process

The exact product law for all increments along a regular grid, including the empty grid.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private noncomputable def gridInc (a h : ℝ≥0) (n : ℕ) (f : DLoc) (i : Fin n) : ℝ :=
  f.1 (a + ((i : ℝ≥0) + 1) * h) - f.1 (a + (i : ℝ≥0) * h)

private theorem measurable_gridInc (a h : ℝ≥0) (n : ℕ) : Measurable (gridInc a h n) := by
  apply Measurable.of_eval
  intro i
  change Measurable (fun f : DLoc => f.1 (a + ((i : ℝ≥0) + 1) * h) -
    f.1 (a + (i : ℝ≥0) * h))
  exact (DLoc.measurable_eval _).sub (DLoc.measurable_eval _)

private theorem map_gridInc_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {h : ℝ≥0}
    (hh : 0 < h) {n : ℕ} (hn : 0 < n) :
    Measure.map (gridInc 0 h n) (stableLocalLaw θ : Measure DLoc) =
      Measure.pi (fun _ : Fin n => (stableLawAt θ (h : ℝ) : Measure ℝ)) := by
  let T : ℝ≥0 := (n : ℝ≥0) * h
  have hT : 0 < T := mul_pos (by exact_mod_cast hn) hh
  let v : Fin (n + 1) → Set.Icc (0 : ℝ) (T : ℝ) := fun i =>
    ⟨(i : ℝ) * (h : ℝ), mul_nonneg (Nat.cast_nonneg _) hh.le, by
      change (i : ℝ) * (h : ℝ) ≤ (n : ℝ) * (h : ℝ)
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_of_lt_succ i.isLt) hh.le⟩
  have hv : StrictMono v := by
    intro i j hij
    change (i : ℝ) * (h : ℝ) < (j : ℝ) * (h : ℝ)
    exact mul_lt_mul_of_pos_right (by exact_mod_cast hij) (by exact_mod_cast hh)
  have hv0 : (v 0 : ℝ) = 0 := by simp [v]
  have hcomp : gridInc 0 h n =
      (fun f : D (T : ℝ) ℝ => fun i : Fin n => f (v i.succ) - f (v i.castSucc)) ∘
        DLoc.restrict T := by
    funext f i
    change f.1 (0 + ((i : ℝ≥0) + 1) * h) - f.1 (0 + (i : ℝ≥0) * h) =
      f.1 ⟨((i.succ : ℝ) * (h : ℝ)), (v i.succ).property.1⟩ -
        f.1 ⟨((i.castSucc : ℝ) * (h : ℝ)), (v i.castSucc).property.1⟩
    congr 1 <;> apply congrArg f.1 <;> apply Subtype.ext <;> simp
  rw [hcomp, ← Measure.map_map]
  · rw [map_restrict_stableLocalLaw hθ hT]
    have hi := (isStableLevyLaw_stableProcessLaw hθ (by exact_mod_cast hT)).increments n v hv hv0
    convert hi using 1
    congr 1
    funext i
    congr 2
    symm
    change ((i.succ : ℝ) * (h : ℝ)) - ((i.castSucc : ℝ) * (h : ℝ)) = (h : ℝ)
    simp only [Fin.val_succ, Fin.val_castSucc]
    push_cast
    ring
  · apply Measurable.of_eval
    intro i
    exact (measurable_eval _).sub (measurable_eval _)
  · exact DLoc.measurable_restrict T

private theorem stableLawAt_Iic {θ : ℝ} {h : ℝ≥0}
    (hh : 0 < h) (δ : ℝ) :
    (stableLawAt θ (h : ℝ) : Measure ℝ) (Set.Iic δ) =
      (stableLaw θ : Measure ℝ) (Set.Iic (δ * (h : ℝ) ^ (-(1 / θ)))) := by
  rw [Real.rpow_neg (show (0 : ℝ) ≤ (h : ℝ) by positivity), ← div_eq_mul_inv]
  rw [stableLawAt, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply (by fun_prop) measurableSet_Iic]
  congr 1
  ext x
  simp only [Set.mem_preimage, Set.mem_Iic]
  have hr : 0 < (h : ℝ) ^ (1 / θ) := Real.rpow_pos_of_pos (by exact_mod_cast hh) _
  rw [mul_comm ((h : ℝ) ^ (1 / θ)) x]
  exact (le_div_iff₀ hr).symm

/-- **Grid increments**: the probability that the `n` increments of the local stable process
over the grid `a, a + h, …, a + n h` are all at most `δ` is
`stableLaw θ (Iic (δ h^{-1/θ}))^n` (independent increments with laws `stableLawAt θ h`). -/
theorem measure_grid_increments_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) {h : ℝ≥0}
    (hh : 0 < h) (n : ℕ) (δ : ℝ) :
    (stableLocalLaw θ : Measure DLoc)
        {f | ∀ k < n, f.1 (a + ((k : ℝ≥0) + 1) * h) - f.1 (a + (k : ℝ≥0) * h) ≤ δ} =
      (stableLaw θ : Measure ℝ) (Set.Iic (δ * (h : ℝ) ^ (-(1 / θ)))) ^ n := by
  by_cases hn : n = 0
  · subst n
    simp
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  let B : Set (Fin n → ℝ) := Set.univ.pi (fun _ => Set.Iic δ)
  have hB : MeasurableSet B := MeasurableSet.univ_pi (fun _ => measurableSet_Iic)
  have hpre : {f : DLoc | ∀ k < n,
      f.1 (a + ((k : ℝ≥0) + 1) * h) - f.1 (a + (k : ℝ≥0) * h) ≤ δ} =
      gridInc a h n ⁻¹' B := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, B, Set.mem_pi, Set.mem_univ,
      forall_true_left, Set.mem_Iic, gridInc]
    exact ⟨fun hf i => hf i i.isLt, fun hf k hk => hf ⟨k, hk⟩⟩
  rw [hpre, ← Measure.map_apply (measurable_gridInc a h n) hB]
  have hshift : gridInc a h n = gridInc 0 h n ∘ DLoc.shift a := by
    funext f i
    simp only [gridInc, Function.comp_apply, DLoc.shift]
    ring_nf
  rw [hshift, ← Measure.map_map (measurable_gridInc 0 h n) (DLoc.measurable_shift_fixed a),
    map_shift_stableLocalLaw hθ a, map_gridInc_zero hθ hh hnpos, Measure.pi_pi]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [stableLawAt_Iic hh]

end BGW.StableTrees
