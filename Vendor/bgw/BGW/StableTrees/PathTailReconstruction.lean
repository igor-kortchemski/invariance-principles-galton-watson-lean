/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.PathTailMeasurable
public import BGW.Skorokhod.MeasurableMaps

/-!
# Reconstruction of mesh increments from a compact step path

Mesh evaluations recover every increment seen before the deterministic horizon. Unseen
increments are set to minus one, so the reconstructed walk continues downwards.
-/

@[expose] public section

open MeasureTheory Set
open scoped NNReal Classical
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees.PathTail

/-- Mesh evaluation time, clipped to the source horizon for a total definition. -/
noncomputable def meshPoint (M : ℝ≥0) (n k : ℕ) : Icc (0 : ℝ) (M : ℝ) :=
  projIcc 0 (M : ℝ) M.2 ((k : ℝ) / n)

/-- Reconstruct the observed mesh increments and continue with minus-one increments. -/
noncomputable def reconstructIncrements (M : ℝ≥0) (n : ℕ) (b : ℝ)
    (y : D (M : ℝ) ℝ) (i : ℕ) : ℝ :=
  if i < ⌊(n : ℝ) * M⌋₊ then
    b * (y (meshPoint M n (i + 1)) - y (meshPoint M n i)) else -1

/-- The reconstruction uses finitely many measurable evaluations. -/
theorem measurable_reconstructIncrements (M : ℝ≥0) (n : ℕ) (b : ℝ) :
    Measurable (reconstructIncrements M n b) := by
  apply Measurable.of_eval
  intro i
  unfold reconstructIncrements
  split_ifs
  · exact ((measurable_eval _).sub (measurable_eval _)).const_mul b
  · exact measurable_const

private theorem meshPoint_val {M : ℝ≥0} {n k : ℕ} (hn : 0 < n)
    (hk : k ≤ ⌊(n : ℝ) * M⌋₊) : (meshPoint M n k : ℝ) = (k : ℝ) / n := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hcast : (k : ℝ) ≤ (⌊(n : ℝ) * M⌋₊ : ℝ) := by exact_mod_cast hk
  have hk' : (k : ℝ) ≤ (n : ℝ) * M :=
    hcast.trans (Nat.floor_le (by positivity))
  have hkn : (k : ℝ) / n ≤ M := (div_le_iff₀ hn').mpr (by nlinarith)
  change max 0 (min (M : ℝ) ((k : ℝ) / n)) = (k : ℝ) / n
  rw [min_eq_right hkn, max_eq_right (div_nonneg (Nat.cast_nonneg _) hn'.le)]

private theorem stepPath_meshPoint {M : ℝ≥0} {n k : ℕ} {b : ℝ} (ω : ℕ → ℝ)
    (hn : 0 < n) (hk : k ≤ ⌊(n : ℝ) * M⌋₊) :
    realStepPath (M : ℝ) n b ω (meshPoint M n k) = partialSum ω k / b := by
  rw [realStepPath_apply, meshPoint_val hn hk,
    mul_div_cancel₀ _ (by exact_mod_cast hn.ne'), Nat.floor_natCast]

/-- Every increment observed before the horizon is recovered exactly when the scales are nonzero. -/
theorem reconstructIncrements_stepPath {M : ℝ≥0} {n i : ℕ} {b : ℝ}
    (hn : 0 < n) (hb : b ≠ 0) (ω : ℕ → ℝ) (hi : i < ⌊(n : ℝ) * M⌋₊) :
    reconstructIncrements M n b (realStepPath (M : ℝ) n b ω) i = ω i := by
  rw [reconstructIncrements, ite_eq_left hi, stepPath_meshPoint ω hn (by omega),
    stepPath_meshPoint ω hn hi.le]
  simp only [partialSum, Finset.sum_range_succ]
  field_simp
  ring

/-- Reconstruction preserves skip-free increments on the image of a skip-free step path. -/
theorem reconstructIncrements_skipFree {M : ℝ≥0} {n : ℕ} {b : ℝ}
    (hb : n ≠ 0 → b ≠ 0) (ω : ℕ → ℝ) (hω : ∀ i, IsSkipFreeIncrement (ω i)) :
    ∀ i, IsSkipFreeIncrement
      (reconstructIncrements M n b (realStepPath (M : ℝ) n b ω) i) := by
  intro i
  by_cases hi : i < ⌊(n : ℝ) * M⌋₊
  · have hn : 0 < n := by
      by_contra hn
      have hz : n = 0 := by omega
      simp [hz] at hi
    rw [reconstructIncrements_stepPath hn (hb hn.ne') ω hi]
    exact hω i
  · rw [reconstructIncrements, ite_eq_right hi]
    exact ⟨0, by norm_num⟩

/-- Reconstructing the increments does not change the compact step path. -/
theorem realStepPath_reconstructIncrements {M : ℝ≥0} {n : ℕ} {b : ℝ}
    (hb : n ≠ 0 → b ≠ 0) (ω : ℕ → ℝ) :
    realStepPath (M : ℝ) n b
      (reconstructIncrements M n b (realStepPath (M : ℝ) n b ω)) =
      realStepPath (M : ℝ) n b ω := by
  apply BGW.Skorokhod.ext
  intro t
  simp only [realStepPath_apply, partialSum]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  have him : i < ⌊(n : ℝ) * M⌋₊ := (Finset.mem_range.mp hi).trans_le
    (Nat.floor_mono (mul_le_mul_of_nonneg_left t.2.2 (Nat.cast_nonneg _)))
  have hn : 0 < n := by
    by_contra hn
    have hz : n = 0 := by omega
    simp [hz] at him
  exact reconstructIncrements_stepPath hn (hb hn.ne') ω him

/-- The reconstructed sequence is skip-free and reproduces the source path almost surely under
its actual iid step-path law. -/
theorem ae_reconstructIncrements (μ : PMF ℕ) (M : ℝ≥0) (n : ℕ) (b : ℝ)
    (hb : n ≠ 0 → b ≠ 0) :
    ∀ᵐ y ∂(stepPathLaw (realOffspringStepLaw μ) M (fun _ => b) n :
      Measure (D (M : ℝ) ℝ)),
      realStepPath (M : ℝ) n b (reconstructIncrements M n b y) = y ∧
        ∀ i, IsSkipFreeIncrement (reconstructIncrements M n b y i) := by
  have hrec := measurable_reconstructIncrements M n b
  have hset : MeasurableSet {y : D (M : ℝ) ℝ |
      realStepPath (M : ℝ) n b (reconstructIncrements M n b y) = y ∧
        ∀ i, IsSkipFreeIncrement (reconstructIncrements M n b y i)} := by
    apply (measurableSet_eq_fun ((measurable_realStepPath _ _ _).comp hrec)
      measurable_id).inter
    have heq : {y : D (M : ℝ) ℝ |
        ∀ i, IsSkipFreeIncrement (reconstructIncrements M n b y i)} =
        ⋂ i : ℕ, ⋃ k : ℕ,
          {y | reconstructIncrements M n b y i = (k : ℝ) - 1} := by
      ext y
      simp [IsSkipFreeIncrement]
    apply (congrArg MeasurableSet heq).mpr
    exact MeasurableSet.iInter fun i => MeasurableSet.iUnion fun k =>
      measurableSet_eq_fun hrec.eval measurable_const
  change ∀ᵐ y ∂((iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).map
      (realStepPath (M : ℝ) n b)), _
  rw [ae_map_iff (measurable_realStepPath _ _ _).aemeasurable hset]
  filter_upwards [ae_step_ge_neg_one μ] with ω hω
  exact ⟨realStepPath_reconstructIncrements hb ω, reconstructIncrements_skipFree hb ω hω⟩

end BGW.StableTrees.PathTail
