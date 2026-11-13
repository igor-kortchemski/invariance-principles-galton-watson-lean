/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Basic
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions

/-!
# Canonical pruning of an offspring field

An arbitrary field of potential offspring counts, indexed by all addresses, is turned into a
canonical tree by keeping the counts at addresses that exist and setting every other
coordinate to zero. This is the standard construction of a locally finite tree from i.i.d.
offspring counts; it is adapted from `Freezing1/PlaneTreePruning.lean`.

A retained coordinate equal to zero is a present leaf, whereas the coordinates below an absent
address are all discarded: `prune_val_of_present` and `not_present_offspring_zero` together
describe `prune f`. The map is the identity on canonical fields (`prune_val`) and measurable
from the product σ-algebra on `Offspring` to the subtype σ-algebra on `Tree`, which is its Borel
σ-algebra (see `BGW/LocallyFinite/Topology.lean`).
-/

@[expose] public section

namespace BGW.LocallyFinite

/-- Keep the offspring count at an address only if every step of the address is a valid child
of the retained counts above it. -/
def pruneRaw (f : Offspring) : Address → ℕ
  | [] => f []
  | j :: u => if 1 ≤ j ∧ j ≤ f [] then pruneRaw (fun v => f (j :: v)) u else 0

theorem canonical_pruneRaw (f : Offspring) : Canonical (pruneRaw f) := by
  intro u j
  induction u generalizing f with
  | nil =>
    simp only [List.nil_append, pruneRaw]
    intro hj
    rw [ite_eq_right hj]
  | cons i u ih =>
    by_cases hi : 1 ≤ i ∧ i ≤ f []
    · simpa only [List.cons_append, pruneRaw, ite_eq_left hi] using ih (fun v => f (i :: v))
    · simp [List.cons_append, pruneRaw, hi]

/-- The tree obtained from an offspring field by discarding the counts at absent addresses. -/
def prune (f : Offspring) : Tree := ⟨pruneRaw f, canonical_pruneRaw f⟩

@[simp] theorem degree_prune (f : Offspring) : degree (prune f) = f [] := rfl

theorem child_prune (f : Offspring) (j : ℕ) :
    child (prune f) j =
      if 1 ≤ j ∧ j ≤ f [] then prune (fun v => f (j :: v)) else leaf := by
  apply Subtype.ext
  funext u
  by_cases hj : 1 ≤ j ∧ j ≤ f [] <;>
    simp [child, prune, pruneRaw, hj]

theorem pruneRaw_eq_of_canonical {f : Offspring} (hf : Canonical f) (u : Address) :
    pruneRaw f u = f u := by
  induction u generalizing f with
  | nil => rfl
  | cons j u ih =>
    have hs : Canonical (fun v => f (j :: v)) := fun v k hk => hf (j :: v) k hk
    by_cases hj : 1 ≤ j ∧ j ≤ f []
    · simpa only [pruneRaw, ite_eq_left hj] using ih hs
    · rw [pruneRaw, ite_eq_right hj]
      exact (hf.zero_of_absent_child [] j hj u).symm

/-- Pruning does not change a field that is already canonical. -/
@[simp] theorem prune_val (T : Tree) : prune T.val = T := by
  apply Subtype.ext
  funext u
  exact pruneRaw_eq_of_canonical T.property u

theorem measurable_pruneRaw_eval (u : Address) :
    Measurable (fun f : Offspring => pruneRaw f u) := by
  induction u with
  | nil => exact measurable_pi_apply []
  | cons j u ih =>
    have hs : Measurable (fun f : Offspring => fun v => f (j :: v)) :=
      Measurable.of_eval fun v => measurable_pi_apply (j :: v)
    have hP : MeasurableSet {f : Offspring | 1 ≤ j ∧ j ≤ f []} :=
      (MeasurableSet.of_discrete (s := {k : ℕ | 1 ≤ j ∧ j ≤ k})).preimage (measurable_pi_apply [])
    exact Measurable.ite hP (ih.comp hs) measurable_const

/-- At a present address the pruned tree keeps the original count. -/
theorem prune_val_of_present {f : Offspring} {u : Address} (h : Present (prune f) u) :
    (prune f).val u = f u := by
  induction u generalizing f with
  | nil => rfl
  | cons j u ih =>
    have hc : 1 ≤ j ∧ j ≤ f [] := ⟨h.1, h.2.1⟩
    have hch : child (prune f) j = prune (fun v => f (j :: v)) := by
      rw [child_prune, ite_eq_left hc]
    have h' := ih (f := fun v => f (j :: v)) (hch ▸ h.2.2)
    change (child (prune f) j).val u = f (j :: u)
    rw [hch]
    exact h'

theorem measurable_prune : Measurable prune :=
  Measurable.subtype_mk (Measurable.of_eval measurable_pruneRaw_eval)

end BGW.LocallyFinite
