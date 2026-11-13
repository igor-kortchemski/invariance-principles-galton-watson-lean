/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.LocallyFinite.Basic
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Algebra.BigOperators.Fin
import Lean.Elab.Tactic.Omega

/-!
# Independent groups of potential offspring coordinates

Group zero contains the root coordinate and the unused addresses; group `i + 1` contains all
addresses below child `i + 1`. The explicit injection `branchAddress` retains the coordinates
needed for any finite family of child subtrees. Its pushforward under an i.i.d. field is the
product of `k + 1` independent i.i.d. fields. Adapted from `Freezing1/OffspringFieldGroups.lean`.
-/

@[expose] public section

namespace BGW.LocallyFinite

open MeasureTheory

/-- Regroup the addresses: the pair `(i, u)` with `i ≠ 0` is the address `u` below child `i`,
while `(0, u)` is the root coordinate and the addresses `u` shifted past the first `k` children
(so that it never meets another group). -/
def branchAddress (k : ℕ) (q : Fin (k + 1) × Address) : Address :=
  if q.1 = 0 then match q.2 with
    | [] => []
    | j :: u => (k + 1 + j) :: u
  else q.1.val :: q.2

theorem branchAddress_injective (k : ℕ) : Function.Injective (branchAddress k) := by
  rintro ⟨i, u⟩ ⟨j, v⟩ h
  by_cases hi : i = 0
  · subst i
    by_cases hj : j = 0
    · subst j
      cases u <;> cases v <;> simp_all [branchAddress]
    · cases u with
      | nil => simp [branchAddress, hj] at h
      | cons a u =>
        have hh : k + 1 + a = j.val := (List.cons.inj
          (by simpa [branchAddress, hj] using h)).1
        have hJ := j.isLt
        omega
  · by_cases hj : j = 0
    · subst j
      cases v with
      | nil => simp [branchAddress, hi] at h
      | cons b v =>
        have hh : i.val = k + 1 + b := (List.cons.inj
          (by simpa [branchAddress, hi] using h)).1
        have hI := i.isLt
        omega
    · have hh : i.val = j.val ∧ u = v := List.cons.inj
        (by simpa [branchAddress, hi, hj] using h)
      exact Prod.ext (Fin.ext hh.1) hh.2

/-- Regrouping an i.i.d. field of offspring counts yields independent i.i.d. fields. -/
theorem iid_branch_groups (μ : Measure ℕ) [IsProbabilityMeasure μ] (k : ℕ) :
    (Measure.infinitePi (fun _ : Address => μ)).map
        (fun f (i : Fin (k + 1)) (u : Address) => f (branchAddress k (i, u))) =
      Measure.pi (fun _ : Fin (k + 1) => Measure.infinitePi (fun _ : Address => μ)) := by
  have hi := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Address => μ) (branchAddress_injective k)
  calc
    _ = ((Measure.infinitePi (fun _ : Address => μ)).map
          (fun f q => f (branchAddress k q))).map
          (MeasurableEquiv.curry (Fin (k + 1)) Address ℕ) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by
      rw [hi, Measure.infinitePi_map_curry
        (fun (_ : Fin (k + 1)) (_ : Address) => μ), Measure.infinitePi_eq_pi]

end BGW.LocallyFinite
