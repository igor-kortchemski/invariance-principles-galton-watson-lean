/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Basic
public import Mathlib.Topology.MetricSpace.Polish
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

/-!
# Topology and Borel structure on locally finite trees

`Offspring` is a countable product of discrete copies of `ℕ`, hence Polish, and the canonical
fields form a closed subset. The topology is the subtype topology: a sequence of trees converges
exactly when every offspring coordinate is eventually constant. This is the Polish structure
of `Freezing1/PlaneTree.lean`, from which `isClosed_canonical` and the continuity lemmas are
adapted.

The only instance declared in this file is `PolishSpace Tree`. The measurable structure is
Mathlib's subtype σ-algebra, induced by the product σ-algebra of `Offspring`; Mathlib's
`Subtype.borelSpace` and `Pi.borelSpace` already make it the Borel σ-algebra of the topology. No
instance is installed on `Address = List ℕ`: the product σ-algebra only involves the measurable
space on the values.
-/

@[expose] public section

namespace BGW.LocallyFinite

theorem isClosed_canonical : IsClosed {f : Offspring | Canonical f} := by
  have he : {f : Offspring | Canonical f} =
      ⋂ u : Address, ⋂ j : ℕ, {f | ¬(1 ≤ j ∧ j ≤ f u) → f (u ++ [j]) = 0} := by
    ext f
    simp only [Canonical, Set.mem_iInter, Set.mem_ofPred_eq]
  rw [he]
  refine isClosed_iInter fun u => isClosed_iInter fun j => ?_
  have hc : Continuous (fun f : Offspring => (f u, f (u ++ [j]))) :=
    (continuous_apply u).prodMk (continuous_apply (u ++ [j]))
  have hd : IsClosed {q : ℕ × ℕ | ¬(1 ≤ j ∧ j ≤ q.1) → q.2 = 0} := isClosed_discrete _
  exact hd.preimage hc

instance : PolishSpace Tree := isClosed_canonical.polishSpace

theorem continuous_offspring (u : Address) : Continuous (fun T : Tree => T.val u) :=
  (continuous_apply u).comp continuous_subtype_val

theorem continuous_degree : Continuous degree := continuous_offspring []

theorem continuous_child (j : ℕ) : Continuous (fun T : Tree => child T j) :=
  Continuous.subtype_mk (continuous_pi fun u => continuous_offspring (j :: u)) _

end BGW.LocallyFinite
