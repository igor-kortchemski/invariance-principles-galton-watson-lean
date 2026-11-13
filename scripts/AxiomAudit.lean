module

import BGWLeaves
import Lean.Elab.Command
import Lean.Util.CollectAxioms

/-!
Transitive axiom audit of every exported declaration of the project modules (`BGWLeaves`) and
of the vendored modules (`BGW`, `BrownianMotion`, `KolmogorovExtension4`) imported by the root
`BGWLeaves`; the axiom set of each one includes those of the private declarations it uses.
Run after `lake build` with `lake env lean scripts/AxiomAudit.lean`; it fails if a declaration
depends on an axiom other than `propext`, `Classical.choice` and `Quot.sound` (in particular on
`sorryAx`). It uses Lean's axiom collector, the mechanism of `#print axioms`; it is not a kernel
replay or a check of statement fidelity.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let roots : Array Name := #[`BGWLeaves, `BGW, `BrownianMotion, `KolmogorovExtension4]
  let moduleOf? (n : Name) : Option Name :=
    (env.getModuleIdxFor? n).bind fun idx => env.header.moduleNames[idx.toNat]?
  let inProject (n : Name) : Bool :=
    match moduleOf? n with
    | some m => roots.any (·.isPrefixOf m)
    | none => false
  let names : Array Name := env.constants.fold (init := #[]) fun acc n _ =>
    if inProject n then acc.push n else acc
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  let mut theorems : Nat := 0
  for name in names.qsort Name.lt do
    if (env.find? name).any (·.isTheorem) then theorems := theorems + 1
    for ax in (← collectAxioms name) do
      unless allowed.contains ax do
        throwError "{name} depends on the disallowed axiom {ax}"
  logInfo m!"Axiom audit passed: {names.size} declarations ({theorems} theorems) of the \
    project and vendored modules; allowed axioms: {allowed}"

#print axioms BGWLeaves.intro_II_general
#print axioms BGWLeaves.intro_II
#print axioms BGWLeaves.thm_ltn_ii
#print axioms BGWLeaves.thm_cvG_ii
#print axioms BGWLeaves.thm_cvW3
#print axioms BGWLeaves.thm_max_i
#print axioms BGWLeaves.thm_max_ii
#print axioms BGWLeaves.thm81_corrected_general
#print axioms BGWLeaves.thm_general_II
#print axioms BGWLeaves.intro_GHP_leaf
#print axioms BGWLeaves.StableAnalysis.locallimit_i
