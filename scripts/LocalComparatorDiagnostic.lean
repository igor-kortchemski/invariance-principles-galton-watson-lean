module

public import Lake.Check.Compare
public import Lake.Check.Util
import Lake.Check.Axioms
import Lean.Data.Json

/-!
# Local diagnostic using Lake's Comparator implementation

Consumes NDJSON exports produced by the pinned toolchain's `leanexport`.
This runs `compareAt` and `checkAxioms` without building, sandboxing or kernel
replay. It is a diagnostic, not the official Linux Comparator or Palomar report.
Usage: `lake env lean --run scripts/LocalComparatorDiagnostic.lean CONFIG CHALLENGE SOLUTION`.
-/

open Lean in
public def primitiveTargets : Array Name := #[
  ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.gcd, ``Nat.div, ``Nat.mod, ``Nat.beq,
  ``Nat.ble, ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight,
  ``String.ofList, ``Char.ofNat, ``List, ``eagerReduce, ``Nat, ``String, ``String.mk, ``Char, ``optParam,
  ``autoParam, ``semiOutParam, ``outParam]

open Lean in
public partial def firstDifference (a b : Expr) : Expr × Expr :=
  match a, b with
  | .app f x, .app g y => if f != g then firstDifference f g else firstDifference x y
  | .lam _ t e _, .lam _ u f _ | .forallE _ t e _, .forallE _ u f _ =>
    if t != u then firstDifference t u else firstDifference e f
  | .letE _ t v e _, .letE _ u w f _ =>
    if t != u then firstDifference t u else if v != w then firstDifference v w else firstDifference e f
  | .mdata _ e, .mdata _ f => firstDifference e f
  | .proj _ _ e, .proj _ _ f => firstDifference e f
  | _, _ => (a, b)

open Lean in
/-- List all reached discrepancies after a failed comparison, to diagnose them together. -/
public def reportMismatches (challenge solution : LeanExport.ExportedEnv)
    (targets holes : Array Name) : IO Unit := do
  let mut todo := primitiveTargets ++ targets ++ holes
  let mut seen : NameSet := {}
  while !todo.isEmpty do
    let n := todo.back!
    todo := todo.pop
    if seen.contains n then continue
    seen := seen.insert n
    let some sc := solution.constMap[n]?
      | IO.println s!"missing from solution: {n}"; continue
    let cc := challenge.constMap[n]?
    let selected := targets.contains n || holes.contains n
    if selected then
      if let some cc := cc then
        if cc.type != sc.type then
          let (a, b) := firstDifference cc.type sc.type
          IO.println s!"selected type mismatch: {n}"
          IO.println s!"  first type difference: {a} / {b}"
    if !selected && cc != some sc then
      IO.println s!"reached mismatch: {n}"
      if let some cc := cc then
        if cc.type != sc.type then
          let (a, b) := firstDifference cc.type sc.type
          IO.println s!"  first type difference: {a} / {b}"
        if let some cv := cc.value? (allowOpaque := true) then
          if let some sv := sc.value? (allowOpaque := true) then
            if cv != sv then
              let (a, b) := firstDifference cv sv
              IO.println s!"  first value difference: {a} / {b}"
    if selected then
      todo := todo ++ sc.type.getUsedConstants
    else
      let collect : StateM (Array Name) Unit := Lake.Check.runForUsedConsts sc
        (fun d => modify (fun ds : Array Name => ds.push d))
      let deps := (collect.run #[]).2
      todo := todo ++ deps

open Lean in
public def main (args : List String) : IO UInt32 := do
  let [cfgPath, challengePath, solutionPath] := args
    | IO.eprintln "usage: CONFIG CHALLENGE.ndjson SOLUTION.ndjson"; return 2
  let cfg ← IO.ofExcept (Json.parse (← IO.FS.readFile cfgPath))
  let strs (k : String) : IO (Array Name) := do
    return (← IO.ofExcept (cfg.getObjValAs? (Array String) k)).map String.toName
  let theoremNames ← strs "theorem_names"
  let definitionNames ← strs "definition_names"
  let legalAxioms ← strs "permitted_axioms"
  let challenge ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk challengePath .read)
  let solution ← LeanExport.parseStream <| .ofHandle (← IO.FS.Handle.mk solutionPath .read)
  match Lake.Check.compareAt challenge solution (theoremNames ++ legalAxioms) definitionNames primitiveTargets with
  | .error e =>
    IO.println s!"COMPARE FAILED: {e}"
    reportMismatches challenge solution (theoremNames ++ legalAxioms) definitionNames
    return 1
  | .ok _ => IO.println "compare: statements and reachable constants match"
  match Lake.Check.checkAxioms solution theoremNames definitionNames legalAxioms with
  | .error e => IO.println s!"AXIOMS FAILED: {e}"; return 1
  | .ok _ => IO.println "axioms: only permitted axioms"
  return 0
