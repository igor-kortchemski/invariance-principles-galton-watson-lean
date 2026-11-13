/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.BridgeLaw
public import Mathlib.Data.List.Count

/-!
# Degree-count marks in the cyclic bridge identity

Finitely many prescribed outdegree counts are invariant under rotating the
Łukasiewicz word. The weighted cycle identity therefore restricts to these marks,
without requiring positive mass or introducing another finite-tree carrier.
Repeated degrees are allowed; incompatible prescribed counts simply give zero.
-/

@[expose] public section

namespace BGW

open scoped ENNReal

/-- The number of steps corresponding to offspring count `k`. In particular, `k = 0`
counts steps equal to `-1`, hence leaves on a tree word. -/
def wordDegreeCount (x : List ℤ) (k : ℕ) : ℕ := x.count ((k : ℤ) - 1)

@[simp] theorem wordDegreeCount_rotate (x : List ℤ) (i k : ℕ) :
    wordDegreeCount (x.rotate i) k = wordDegreeCount x k :=
  (List.rotate_perm x i).count_eq _

private theorem wordDegreeCount_map (ds : List ℕ) (k : ℕ) :
    wordDegreeCount (ds.map fun d : ℕ => (d : ℤ) - 1) k = ds.count k := by
  exact List.count_map_of_injective ds (fun d : ℕ => (d : ℤ) - 1)
    (by intro x y h; dsimp at h; omega) k

@[simp] theorem wordDegreeCount_stepWord {n : ℕ} (ω : Fin n → ℕ) (k : ℕ) :
    wordDegreeCount (stepWord ω) k = (List.ofFn ω).count k := by
  change wordDegreeCount (List.ofFn ((fun d : ℕ => (d : ℤ) - 1) ∘ ω)) k = _
  rw [← List.map_ofFn]
  exact wordDegreeCount_map _ _

namespace PlaneTree

/-- Number of vertices whose outdegree is `k`, counting every DFS occurrence. -/
def degreeCount (t : PlaneTree) (k : ℕ) : ℕ := t.degrees.count k

@[simp] theorem wordDegreeCount_increments (t : PlaneTree) (k : ℕ) :
    wordDegreeCount t.increments k = t.degreeCount k :=
  wordDegreeCount_map _ _

theorem degreeCount_le_size (t : PlaneTree) (k : ℕ) : t.degreeCount k ≤ t.size := by
  simpa only [degreeCount, length_degrees] using List.count_le_length (l := t.degrees) (a := k)

/-- Weighted Kemperman identity with finitely many prescribed degree counts.
The marks may repeat a degree, and no assumption on the weights or size is needed. -/
theorem natCast_mul_tsum_weight_degreeCounts (p : ℕ → ℝ≥0∞) (n r : ℕ)
    (ks cs : Fin r → ℕ) :
    (n : ℝ≥0∞) * (∑' t : {t : PlaneTree // t.size = n},
      weight p t.val * (if ∀ j, t.val.degreeCount (ks j) = cs j then 1 else 0)) =
      ∑' ω : Fin n → ℕ, Set.indicator
        (countBridges n ∩ {ω | ∀ j, (List.ofFn ω).count (ks j) = cs j})
        (fun ω => ∏ i, p (ω i)) ω := by
  classical
  let g : List ℤ → ℝ≥0∞ := fun x =>
    if ∀ j, wordDegreeCount x (ks j) = cs j then 1 else 0
  calc
    _ = ∑' q : {t : PlaneTree // t.size = n} × Fin n,
        weight p q.1.val * g (q.1.val.increments.rotate q.2) := by
      simp only [g, wordDegreeCount_rotate, wordDegreeCount_increments]
      rw [ENNReal.tsum_prod']
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro t
      simp [tsum_fintype]
    _ = ∑' ω : Fin n → ℕ, Set.indicator (countBridges n)
        (fun ω => (∏ i, p (ω i)) * g (stepWord ω)) ω := by
      rw [tsum_shift_weight_mul, tsum_bridgeWords_walkWeight_mul]
    _ = _ := by
      apply tsum_congr
      intro ω
      by_cases hb : ω ∈ countBridges n
      · by_cases hm : ∀ j, (List.ofFn ω).count (ks j) = cs j
        · simp [Set.indicator, hb, g, hm]
        · simp [Set.indicator, hb, g, hm]
      · simp [Set.indicator, hb]

end PlaneTree

end BGW
