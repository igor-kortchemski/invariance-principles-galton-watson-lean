module

public import BGWLeaves.GeneralAFunctional.Defs
public import BGWLeaves.LeafLimits.Defs
public import BGWLeaves.Coding.Defs
public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.GeneralA.Defs
public import BGWLeaves.StableAnalysis
public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.JointExcursion
public import BGW.Skorokhod.ExitPartition
public import BGW.StableTrees.Defs
public import BGW.Skorokhod.Basic
public import BGW.Skorokhod.Measurable
public import BGW.LocallyFinite.Basic
public import BGWLeaves.StableAnalysis.Defs
import BGWLeaves.GeneralAFunctional.Proof

/-!
# Theorem 8.1(II), functional part (M15): the statements

Source: arXiv:1110.2163v4, `largetrees_final.tex`, Theorem 8.1 (`thm:general`), part (II) (line 2502 of the
UTF-8 copy `.orchestration/t2-arch/paper_utf8.tex`; the paper sketches the proof, lines 2510–2540).

The type of `thm_general_II` was approved by the read-only Astra review of 13 Nov 2026
(`.orchestration/astra-81II/attempt-1/result.md`: APPROVE WITH AMENDMENTS, on the owner's overnight delegation "ask astra
if you have questions"); the amendments are in the docstrings; `thm_general_II_canonical` is Astra's amendment 1. Registered as an OPTIONAL-SCOPE package after the owner's deferral (Q3, 12 Nov 2026)
was lifted by the sealing of M11–M14. A statement registered here is NOT a proved theorem until its hole is
sealed and re-audited.

Conventions. `m = μ(A)`, `ζ = ζ(τ)` the total size, `ζ_A` the number of vertices with a number of children in `A`.
* `m = 0`: `ζ_A = 0` almost surely, there is no admissible sequence tending to infinity, and the statements are
  vacuously true (not a convergence claim about the junk Dirac law).
* `m = 1`: `ζ_A = ζ` almost surely (also when `A ≠ ℕ`); the case is included, and the proof must identify the
  conditioning events rather than divide by `1 − m`.
* `0 < m < 1`: the substantive marked case.
No lattice or non-lattice hypothesis is needed: the arithmetic of `A` enters only the intermediate local
estimates, through `arithFactor μ A`.
The remaining difficulty is the functional conditioning machinery, including the random final marked increment.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- **Theorem 8.1(II) (`thm:general`, line 2502), functional part**: for nonempty `A ⊂ ℕ` (finite or cofinite
when `σ² = ∞`, as printed) and `τ_n ∼ P_μ[· | ζ_A = n]`, the three codings rescaled at the RANDOM TOTAL SIZE
`ζ = ζ(τ_n)`, `(W_{⌊ζ t⌋}/B_ζ, (B_ζ/ζ) C_{2ζt}, (B_ζ/ζ) H_{ζt})_{0 ≤ t ≤ 1}`, converge JOINTLY in law to
`(X^exc, H^exc, H^exc)` (`excTripleLaw θ`, the joint excursion law with the height duplicated), along every
sequence `q k → ∞` of admissible sizes (`P_μ[ζ_A = q k] > 0`). `B` is ANY admissible norming for the paper's
specified stable law (`IsRealStableAttracted`, which includes `1 < θ ≤ 2` and eventual positivity); the printed
explicit norming formula of Theorem 1.10 needs the corrections R2/R4, so the corrected canonical norming is the
corollary `thm_general_II_canonical`. Form: STRONGER than printed in the norming; the printed index set
("for `n` with `P[ζ_A = n] > 0`") is kept; no lattice hypothesis. Measurability: `measurable_codingTriple`
(`BGWLeaves/Coding/Defs.lean`); the conditioning event is measurable (`measurableSet_zetaAEvent`). Boundary
cases: if `μ(A) = 0` then `ζ_A = 0` almost surely, no admissible `q k ≥ 1` exists and the statement is vacuous;
if `μ(A) = 1` then `ζ_A = ζ` almost surely and the statement is the size-conditioned one. Statement approved
(Astra, 13 Nov 2026); the proof is a registered hole until sealed. -/
theorem thm_general_II {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} {A : Set ℕ} (hA : A.Nonempty)
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hAfin : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (codingTriple B)) atTop
      (𝓝 (excTripleLaw θ)) := by
  exact BGWLeaves.GeneralAFunctional.Main.thm_general_II hA hc hne hap hB hAfin hqtop hq

/-- **Theorem 8.1(II), canonical-norming corollary**: as `thm_general_II` with the CORRECTED canonical norming
`B_n = norming (stepLaw μ) θ n` of tranche 1 (R2, R4), under `(H_θ)` in tranche 1's form. ROUTINE from
`thm_general_II` and `isRealStableAttracted_norming` (M11). `hne` and `hap` are carried for uniformity with
`thm_general_II`. -/
theorem thm_general_II_canonical {μ : PMF ℕ} {θ : ℝ} {A : Set ℕ} (hA : A.Nonempty)
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a)
    (hAfin : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) → A.Finite ∨ Aᶜ.Finite)
    {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k)) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).map (codingTriple (norming (stepLaw μ) θ))) atTop
      (𝓝 (excTripleLaw θ)) := by
  exact BGWLeaves.GeneralAFunctional.Main.thm_general_II_canonical hA hc hne hap hDA hAfin hqtop hq

end BGWLeaves
