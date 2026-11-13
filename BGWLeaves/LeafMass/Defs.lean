module

public import BGWLeaves.LeafConcentration.Defs
public import BGWLeaves.GeneralA.Defs
public import BGWLeaves.StableAnalysis

/-!
# Exact leaf counts (M4b): definitions and proved bridges

Source: arXiv:1110.2163v4, `largetrees_final.tex`, Section 3 (exact leaf counts): Theorem 3.1
(`thm:ltn`, lines 864-882), the remark after it (line 880), Remark 3.2 (line 885), Corollary 3.3
(`cor:Lambda`, lines 890-896), Section 3.1 (`eq:Y`, line 904, `eq:ll`, line 915) and Section 3.2
(the lattice case and the periodic remark, lines 1074-1096).

This file contains every definition of milestone M4b and the proved bridges.  It contains no proof
holes.  The definitions of Section 2 (`IsOe`, `finiteTreeEvent`, `supDev`, `childCountAt`, `Lambda`,
`treeLeafDev`) are those of `BGWLeaves.LeafConcentration.Defs`, which is imported here.  The
statements still to be proved are in `BGWLeaves.LeafMass`; their proofs are supplied by the provider
modules `BGWLeaves.LeafMass.*` (imported through `BGWLeaves.LeafMass.Proof`).

Conventions.
* Offspring law `μ : PMF ℕ`; the law of a Galton-Watson tree is `bienaymeLaw μ.toMeasure` on
  `LocallyFinite.Tree`; `P_μ[λ(τ) = m]` is `leafProb μ m`, the mass of the event `leafCountEvent m`
  (the tree is finite and has exactly `m` leaves).  Infinite trees are null in the critical case.
* The laws on `ℤ` of M3 (`stepLaw μ`, `etaLaw μ`, `intWalkProb`, `norming`, `IsStableAttracted`,
  `IsLatticeLaw`, `HasSpan`, `mean`, `variance`) are used as they are.
* `B_n = norming (stepLaw μ) θ n` is the CORRECTED norming (`MANUSCRIPT_RECOMMENDATIONS.md` R2, R4);
  `h = hSlow μ θ` is the slowly varying function with `B_n = h(n) n^{1/θ}`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## 3.0 Events and conventions -/

/-- `x_n = oe_ε(n)` **as `n` tends to infinity in the set `S`** (the form of the statement of
Corollary 3.3, "when `n - 1` tends to infinity in the set of multiples of `gcd(b-1,d)`"): there are
`C, c > 0` with `x_n ≤ C exp(-c n^ε)` for every `n ∈ S`.  For the bounded sequences of the paper
(probabilities) this is equivalent to the bound for all large `n ∈ S` (enlarge `C`); with
`S = Set.univ` it is `IsOe ε x`. -/
def IsOeOn (S : Set ℕ) (ε : ℝ) (x : ℕ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n ∈ S, x n ≤ C * Real.exp (-c * (n : ℝ) ^ ε)

/-- `{λ(τ) = m}` (Theorem 3.1, Corollary 3.3): the tree is finite and has exactly `m` leaves
(vertices of outdegree `0`; `λ(τ) = t.degreeCount 0`).  Infinite trees never belong to it. -/
def leafCountEvent (m : ℕ) : Set LocallyFinite.Tree :=
  finiteTreeEvent fun t => t.degreeCount 0 = m

/-- `P_μ[λ(τ) = m]` (the `Prmu{lt = m}` of Theorem 3.1): the probability that a `GW_μ` tree has
exactly `m` leaves. -/
noncomputable def leafProb (μ : PMF ℕ) (m : ℕ) : ℝ :=
  (bienaymeLaw μ.toMeasure).real (leafCountEvent m)

/-- The slowly varying function `h` of Theorem 3.1 (`B_n = h(n) n^{1/θ}`, introduced before
Lemma 1.11 of the paper): `h(x) = B_{⌊x⌋} / x^{1/θ}` with `B_n = norming (stepLaw μ) θ n` (the
corrected norming of M3).  That it is slowly varying is `hSlow_slowlyVarying`. -/
noncomputable def hSlow (μ : PMF ℕ) (θ : ℝ) : ℝ → ℝ :=
  fun x => norming (stepLaw μ) θ ⌊x⌋₊ / x ^ (1 / θ)

/-- The paper's `h` is slowly varying (the second part of `locallimit_ii` for `ν = stepLaw μ`; the
domain of attraction `StableDomain μ θ a` of `(H_θ)` is transferred to `stepLaw μ`). -/
theorem hSlow_slowlyVarying {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ)
    (hDA : ∃ a, StableDomain μ θ a) : SlowlyVarying (hSlow μ θ) := by
  obtain ⟨b, hb⟩ := hDA
  have := isProbabilityMeasure_stepLaw μ
  exact (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩).2

/-! ## 3.1 The arithmetic data of Theorem 3.1 -/

/-- The pair `(d, b)` of Theorem 3.1 (line 864): `d ≥ 1` is the **largest** integer such that
`supp μ ∖ {0} ⊂ b + dℤ` for some `b ∈ ℕ`, and then `b` is the **least** natural number with
`supp μ ∖ {0} ⊂ b + dℤ`.  It is a property, not a definition by choice: the pair exists exactly when
`supp μ ∖ {0}` has at least two points (otherwise there is no largest `d`), see
`exists_isSuppSpan`, and it is then unique (`isSuppSpan_unique`).  Equivalently: `IsSuppSpan μ d b`
holds iff `d` is the gcd of the differences of the points of `supp μ ∖ {0}` and `b` is the residue of
any of them modulo `d`. -/
def IsSuppSpan (μ : PMF ℕ) (d b : ℕ) : Prop :=
  1 ≤ d ∧
  (∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d : ℤ) ∣ (k : ℤ) - b) ∧
  (∀ d' : ℕ, 1 ≤ d' → (∃ b' : ℕ, ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d' : ℤ) ∣ (k : ℤ) - b') → d' ≤ d) ∧
  (∀ b' : ℕ, (∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d : ℤ) ∣ (k : ℤ) - b') → b ≤ b')

/-- The pair `(d, b)` of Theorem 3.1 is unique: "largest `d`" and "minimal `b`" determine it. -/
theorem isSuppSpan_unique {μ : PMF ℕ} {d b d' b' : ℕ} (h : IsSuppSpan μ d b)
    (h' : IsSuppSpan μ d' b') : d = d' ∧ b = b' := by
  obtain ⟨hd1, hdv, hdmax, hbmin⟩ := h
  obtain ⟨hd1', hdv', hdmax', hbmin'⟩ := h'
  have hdd : d = d' :=
    le_antisymm (hdmax' d hd1 ⟨b, hdv⟩) (hdmax d' hd1' ⟨b', hdv'⟩)
  subst hdd
  exact ⟨rfl, le_antisymm (hbmin b' hdv') (hbmin' b hdv)⟩

/-- The additive monoid generated by the nonnegative steps of `Y` (`etaLaw μ`): `supp Y =
{k - 1 : k ∈ supp μ, k ≥ 1}`, so `λ - 1` is a sum of such steps (Section 3.2, line 1081: "`n` can be
written as a sum of elements of `supp(Y)`").  It contains `0` (the empty sum). -/
def leafMonoid (μ : PMF ℕ) : AddSubmonoid ℕ :=
  AddSubmonoid.closure {i : ℕ | μ (i + 1) ≠ 0}

/-! ## 3.2 The law of `Y`: a proved bridge -/

/-- The finite-variance norming of `W'` (`largetrees_final.tex`, line 920: `B'_n = σ' √(n/2)`,
`σ'² = Var(Y)`): proved from `integrable_sq_etaLaw` and `norming_of_integrable_sq`. -/
theorem norming_etaLaw_finiteVariance {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) (n : ℕ) :
    norming (etaLaw μ) θ n = Real.sqrt (variance (etaLaw μ)) * Real.sqrt (n / 2) :=
  norming_of_integrable_sq (integrable_sq_etaLaw hc hne hfin) θ n

end BGWLeaves
