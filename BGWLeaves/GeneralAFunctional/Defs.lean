module

public import BGWLeaves.Coding.Defs
public import BGWLeaves.GeneralA.Defs
public import BGW.StableTrees.ExactContourBasic

/-!
# Theorem 8.1(II), functional part: definitions

Source: arXiv:1110.2163v4, Theorem 8.1 (`thm:general`, lines 2494–2508 of the LaTeX source;
Section 8 starts at line 2486).

* `ζ_A(τ)` is `zetaA A τ` (the number of vertices of `τ` whose number of children lies in `A`,
  `ℕ∞`-valued).
* `ZetaAAdmissible μ A n`: `P_μ[ζ_A(τ) = n] > 0`, for finite trees (infinite trees are null under criticality
  and `μ 1 ≠ 1`: BGW `ae_finiteVertices_bienaymeLaw`). The event is measurable (`measurableSet_zetaAEvent`:
  it consists of finite trees, which are countably many).
* `zetaATreeLaw μ A n`: `P_μ[· | ζ_A = n]` as a probability measure; the Dirac mass at the one-vertex tree when
  the event is null (junk; excluded by admissibility in the sequence-indexed statements).
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- `P_μ[ζ_A(τ) = n] > 0` (finite trees). -/
def ZetaAAdmissible (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) : Prop :=
  bienaymeLaw μ.toMeasure {T | FiniteVertices T ∧ zetaA A T = n} ≠ 0

open Classical in
/-- `P_μ[· | ζ_A = n]` as a probability measure (junk Dirac mass at the one-vertex tree if null). -/
noncomputable def zetaATreeLaw (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) :
    ProbabilityMeasure LocallyFinite.Tree :=
  if h : ZetaAAdmissible μ A n then
    ⟨(bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = n}],
      cond_isProbabilityMeasure h⟩
  else ⟨Measure.dirac LocallyFinite.leaf, inferInstance⟩

/-- `zetaATreeLaw` is the conditional law at admissible `n`. -/
theorem coe_zetaATreeLaw {μ : PMF ℕ} {A : Set ℕ} {n : ℕ} (hn : ZetaAAdmissible μ A n) :
    (zetaATreeLaw μ A n : Measure LocallyFinite.Tree) =
      (bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = n}] := by
  have h : zetaATreeLaw μ A n =
      ⟨(bienaymeLaw μ.toMeasure)[|{T | FiniteVertices T ∧ zetaA A T = n}],
        cond_isProbabilityMeasure hn⟩ := by
    unfold zetaATreeLaw
    exact dite_eq_left hn
  rw [h]
  rfl

/-- The conditioning event `{ζ_A = n}` (finite trees) is measurable: it is a set of finite trees, and the finite
trees form a countable set (BGW `ExactContour.countable_finiteVertices`). -/
theorem measurableSet_zetaAEvent (A : Set ℕ) (n : ℕ) :
    MeasurableSet {T : LocallyFinite.Tree | FiniteVertices T ∧ zetaA A T = n} :=
  (ExactContour.countable_finiteVertices.mono fun _ hT => hT.1).measurableSet

end BGWLeaves
