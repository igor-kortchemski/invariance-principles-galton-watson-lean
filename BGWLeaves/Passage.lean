module

public import BGWLeaves.Passage.Defs
import BGWLeaves.Passage.Proof

/-!
# Proposition 1.4, `eq:kemperman` and `eq:f` (M2b)

Source: arXiv:1110.2163v4, Section 1.3 (lines 291, 471–542): the stopped walk and the forest of
`j` independent Galton–Watson trees, the marked and unmarked Kemperman formulas, and the
Introduction's one-tree formula.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory BGW
open scoped ENNReal

/-- Proposition 1.4 (`prop:RW`), atoms: the stopped word of the walk with step law `μ(k)` for the
step `k-1` has the law of the Łukasiewicz word of a forest of `j` independent GW trees. -/
theorem stoppedWord_atom (μ : Measure ℕ) [IsProbabilityMeasure μ] {j : ℕ} (hj : 1 ≤ j)
    (x : List ℤ) :
    (Measure.infinitePi fun _ : ℕ => μ) (stoppedWordEvent j x) =
      (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestCodeEvent j x) := by
  exact BGWLeaves.Passage.Atoms.stoppedWord_atom μ hj x

/-- Proposition 1.4, the remaining atom: the walk never hits `-j` iff some tree of the forest is
infinite. -/
theorem stoppedWord_none (μ : Measure ℕ) [IsProbabilityMeasure μ] {j : ℕ} (hj : 1 ≤ j) :
    (Measure.infinitePi fun _ : ℕ => μ) {ω | ∀ p, ¬ IsFirstHit j ω p} =
      (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ)
        {F | ∃ i, ¬ LocallyFinite.FiniteVertices (F i)} := by
  exact BGWLeaves.Passage.Atoms.stoppedWord_none μ hj

/-- Proposition 1.4, total progeny: the hitting time `ζ_j` of `-j` by the walk has the law of the
total progeny of a forest of `j` independent GW trees. -/
theorem firstHit_law (μ : Measure ℕ) [IsProbabilityMeasure μ] {j : ℕ} (hj : 1 ≤ j) (p : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ) {ω | IsFirstHit j ω p} =
      (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestSizeEvent j p) := by
  exact BGWLeaves.Passage.FirstHit.firstHit_law μ hj p

/-- Joint law of `(ζ_j, Λ(ζ_j))` of the walk, `Λ` counting the steps equal to `-1` before `ζ_j`,
and of the total progeny and number of leaves of a forest of `j` independent GW trees. -/
theorem firstHit_leaves_law (μ : Measure ℕ) [IsProbabilityMeasure μ] {j : ℕ} (hj : 1 ≤ j)
    (p n : ℕ) :
    (Measure.infinitePi fun _ : ℕ => μ)
        {ω | IsFirstHit j ω p ∧ (Finset.univ.filter fun i : Fin p => ω i = 0).card = n} =
      (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestEvent j p n) := by
  exact BGWLeaves.Passage.FirstHit.firstHit_leaves_law μ hj p n

/-- `eq:kemperman`: `P[ζ_j = p, Λ(p) = n] = (j/p) P[W_p = -j, Λ(p) = n]`. -/
theorem kemperman_marked (μ : Measure ℕ) [IsProbabilityMeasure μ] {j p n : ℕ} (hj : 1 ≤ j)
    (hp : 1 ≤ p) :
    (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestEvent j p n) =
      ((j : ℝ≥0∞) / p) * Measure.pi (fun _ : Fin p => μ) (leafMarkedForestBridges j p n) := by
  exact BGWLeaves.Passage.Kemperman.kemperman_marked μ hj hp

/-- The unmarked form: `P[ζ_j = p] = (j/p) P[W_p = -j]`. -/
theorem kemperman_unmarked (μ : Measure ℕ) [IsProbabilityMeasure μ] {j p : ℕ} (hj : 1 ≤ j)
    (hp : 1 ≤ p) :
    (Measure.pi fun _ : Fin j => LocallyFinite.bienaymeLaw μ) (forestSizeEvent j p) =
      ((j : ℝ≥0∞) / p) * Measure.pi (fun _ : Fin p => μ) (countForestBridges j p) := by
  exact BGWLeaves.Passage.Kemperman.kemperman_unmarked μ hj hp

/-- The introduction's formula (`eq:f`, the case `j = 1` of Proposition 1.6) for one tree. -/
theorem eq_f (μ : Measure ℕ) [IsProbabilityMeasure μ] (h0 : μ {0} ≠ 1) {p n : ℕ} (hp : 1 ≤ p)
    (hn : n ≤ p) :
    LocallyFinite.bienaymeLaw μ (treeSizeLeavesEvent p n) =
      ((1 : ℝ≥0∞) / p) * ((p.choose n : ℝ≥0∞) * μ {0} ^ n * (1 - μ {0}) ^ (p - n)) *
        Measure.pi (fun _ : Fin (p - n) => eta μ) {ω | ∑ i, ω i + 1 = n} := by
  exact BGWLeaves.Passage.Kemperman.eq_f μ h0 hp hn

end BGWLeaves
