/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Tree.DFS

/-!
# First passage at forest component boundaries

An ordered forest is encoded by concatenating its component increment sequences.
Its path first reaches minus the number of components at its terminal time.
More generally, the end of the first `r` components is the first visit to `-r`.
The statements use finite prefix sums and include the empty forest.
-/

public section

namespace BGW.PlaneForest

@[simp] theorem increments_append (ts ss : PlaneForest) :
    increments (ts ++ ss) = increments ts ++ increments ss := by
  simp [increments]

/-- A forest path stays strictly above its terminal level before its final step. -/
theorem sum_take_increments_gt (ts : PlaneForest) {i : ℕ}
    (hi : i < (increments ts).length) :
    -(ts.length : ℤ) < ((increments ts).take i).sum := by
  induction ts generalizing i with
  | nil => simp [increments] at hi
  | cons t ts ih =>
    change i < (PlaneTree.increments t ++ increments ts).length at hi
    change -((ts.length + 1 : ℕ) : ℤ) <
      ((PlaneTree.increments t ++ increments ts).take i).sum
    rw [List.length_append] at hi
    by_cases hit : i < (PlaneTree.increments t).length
    · rw [List.take_append_of_le_length (Nat.le_of_lt hit)]
      have hp := PlaneTree.sum_take_increments_nonneg t hit
      simp only [Int.natCast_add, Int.natCast_one]
      omega
    · have hti : (PlaneTree.increments t).length ≤ i := by omega
      have hitail : i - (PlaneTree.increments t).length < (increments ts).length := by
        omega
      have hp := ih hitail
      rw [List.take_append, List.take_of_length_le hti, List.sum_append,
        PlaneTree.sum_increments]
      simp only [Int.natCast_add, Int.natCast_one]
      omega

/-- The first `r` components occupy exactly their total size in the full code.
This also holds when `r` exceeds the component count, since `List.take` saturates. -/
theorem take_increments_size_take (ts : PlaneForest) (r : ℕ) :
    (increments ts).take (size (ts.take r)) = increments (ts.take r) := by
  have hsplit : increments ts = increments (ts.take r) ++ increments (ts.drop r) := by
    rw [← increments_append, List.take_append_drop]
  rw [hsplit, ← length_increments (ts.take r), List.take_append_length]

/-- At the end of the first `r` components, the path has value `-r`. -/
theorem sum_take_increments_size_take (ts : PlaneForest) {r : ℕ}
    (hr : r ≤ ts.length) :
    ((increments ts).take (size (ts.take r))).sum = -(r : ℤ) := by
  rw [take_increments_size_take, sum_increments, List.length_take_of_le hr]

/-- The path has not yet reached `-r` before the end of the first `r` components. -/
theorem sum_take_increments_gt_before_size_take (ts : PlaneForest) {r i : ℕ}
    (hr : r ≤ ts.length) (hi : i < size (ts.take r)) :
    -(r : ℤ) < ((increments ts).take i).sum := by
  have hi' : i < (increments (ts.take r)).length := by simpa using hi
  have hp := sum_take_increments_gt (ts.take r) hi'
  rw [List.length_take_of_le hr] at hp
  have hsplit : increments ts = increments (ts.take r) ++ increments (ts.drop r) := by
    rw [← increments_append, List.take_append_drop]
  rw [hsplit, List.take_append_of_le_length (Nat.le_of_lt hi')]
  exact hp

end BGW.PlaneForest
