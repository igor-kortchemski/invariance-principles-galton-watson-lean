module

public import BGWLeaves.LeafConcentration.Defs
import BGWLeaves.LeafConcentration.Proof

/-!
# Leaf concentration (M4a): the results still to be proved

Source: arXiv:1110.2163v4, `largetrees_final.tex`, Section 2: Definition 2.1 (`def:Lambda`),
Lemma 2.2 (`lem:phi`), Remark 2.4 (`rem:oe`), Lemma 2.5 (`lem:GdesDev`), Corollary 2.6
(`cor:GD2mieux`), Lemma 2.7 (`lem:GdesDev2`).  Each declaration here is a statement approved for
freezing; its proof is to be supplied in the provider modules `BGWLeaves.LeafConcentration.*`
(imported through `BGWLeaves.LeafConcentration.Proof`).  Definitions and proved bridges are in
`BGWLeaves.LeafConcentration.Defs`.  `lem_GdesDev_tree` is a proved assembly of the statements
above it.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-- **Remark 2.4 (`rem:oe`)** (`largetrees_final.tex`, Section 2.3): if `x_n ≥ 0` is `oe_ε(n)` then
`y_n = ∑_{k ≥ n} x_k` is `oe_ε(n)`, with the same exponent `ε` (a smaller constant `c` is needed).
The conclusion states `Summable x` explicitly, so that the `tsum` is not the junk value `0`; `IsOe`
is the paper's definition of `oe_ε(n)` (`IsOe`, all `n : ℕ`). -/
theorem IsOe.tail {ε : ℝ} (hε : 0 < ε) {x : ℕ → ℝ} (hx0 : ∀ n, 0 ≤ x n) (hx : IsOe ε x) :
    Summable x ∧ IsOe ε (fun n => ∑' k : ℕ, x (n + k)) := by
  exact BGWLeaves.LeafConcentration.OeLemmas.IsOe.tail hε hx0 hx

/-- Semantic bridge for **Definition 2.1 (`def:Lambda`)**: `k_j(τ)` is the number of children of the
`j`-th vertex in lexicographic order.  Here `childCountAt` reads the `j`-th entry of the
depth-first degree list `PlaneTree.degrees`, and the right-hand side is the intrinsic offspring
number `PlaneTree.offspringAt` of the vertex `u(j)` of the depth-first listing `PlaneTree.vertices`
(zero-based addresses, converted by `PlaneTree.positiveAddress`), for `j < ζ(τ) = t.size`. -/
theorem childCountAt_eq_offspringAt (t : PlaneTree) {j : ℕ} (hj : j < t.size) :
    childCountAt t j =
      t.offspringAt (PlaneTree.positiveAddress (t.vertices.getD j [])) := by
  exact BGWLeaves.LeafConcentration.WalkDeviation.childCountAt_eq_offspringAt t hj

/-- **Lemma 2.2(i) (`lem:phi`)**: Chernoff-Cramér bounds, both tails, for `n` iid Bernoulli(`p`)
variables `X_0, …, X_{n-1}` on an arbitrary probability space `(Ω, P)`, `0 < p < 1` (the paper's
`p = μ₀`).  The sums are indexed by `Finset.range n` (the paper's `X_1, …, X_n` shifted to start at
`0`, so that `X i ω = 1{ω i = 0}` applies to the walk directly).  For every `a > 0` and `n ≥ 1`
(arbitrary, no restriction to `[0,1]`):
`P[(1/n) ∑ X_k > p + a] ≤ 2 exp(-n φ*(p + a))` and `P[(1/n) ∑ X_k < p - a] ≤ 2 exp(-n φ*(p - a))`.
When `p + a ≥ 1` (resp. `a ≥ p`) the event is null (the empirical mean lies in `[0,1]` almost
surely), so the bound is trivial, and the junk values of `phiStar` outside `[0,1]` play no role.
The factor `2` is the printed one. -/
theorem lem_phi_i {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) (X : ℕ → Ω → ℝ) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X P)
    (hber : ∀ i, P {ω | X i ω = 1} = ENNReal.ofReal p ∧ P {ω | X i ω = 0} = ENNReal.ofReal (1 - p))
    {a : ℝ} (ha : 0 < a) {n : ℕ} (hn : 1 ≤ n) :
    P.real {ω | p + a < (∑ k ∈ Finset.range n, X k ω) / n} ≤
        2 * Real.exp (-(n * phiStar p (p + a))) ∧
      P.real {ω | (∑ k ∈ Finset.range n, X k ω) / n < p - a} ≤
        2 * Real.exp (-(n * phiStar p (p - a))) := by
  exact BGWLeaves.LeafConcentration.Chernoff.lem_phi_i P hp0 hp1 X hX hind hber ha hn

/-- **Lemma 2.2(ii) (`lem:phi`)**: `φ*(p + x) = x² / (2 p (1 - p)) + o(x²)` as `x → 0`, for
`0 < p < 1`, stated as `φ*(p + x) - x²/(2p(1-p)) = o(x²)` along `𝓝 0`. -/
theorem lem_phi_ii {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) :
    (fun x : ℝ => phiStar p (p + x) - x ^ 2 / (2 * p * (1 - p))) =o[𝓝 0] fun x : ℝ => x ^ 2 := by
  exact BGWLeaves.LeafConcentration.Chernoff.lem_phi_ii hp0 hp1

/-- **Lemma 2.5(i) (`lem:GdesDev`)**, walk version.  Only `0 < μ₀ < 1` is used (neither criticality
nor `(H_θ)`).  `ω` is the walk with steps `ω i - 1`, of law `Measure.infinitePi (fun _ => μ)`, and the
event is `sup_{η ≤ t ≤ 1} |(1/(nt)) ∑_{j=0}^{⌊nt⌋} 1{X_j = -1} - μ₀| > δ n^{-1/4}`, with the vertex
indexing of Definition 2.1 (`walkLeafDev`: the sum runs over the first `⌊nt⌋ + 1` steps; the printed
`X_0` is ill-indexed).  Its probability is `oe_{1/2}(n)` (`IsOe (1/2)`), for `0 < η < 1`, `δ > 0`. -/
theorem lem_GdesDev_walk (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) :
    IsOe (1 / 2) fun n : ℕ =>
      ((Measure.infinitePi fun _ : ℕ => μ.toMeasure).real
        {ω | ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) <
          supDev η (walkLeafDev (μ 0).toReal ω n)}) := by
  exact BGWLeaves.LeafConcentration.WalkDeviation.lem_GdesDev_walk μ h0 h1 hη0 hη1 hδ

/-- **Proposition 1.4 (`prop:RW`) for one tree, at the level of events of finite trees** (the step
"use Proposition 1.4" in the proof of Lemma 2.5(ii)): the law of an event `Q` of finite trees
(lifted to `LocallyFinite.Tree` by `finiteTreeEvent`) equals the law of the corresponding union of
stopped-word events (`j = 1`) of the walk.  Hypothesis-free (any offspring law). -/
theorem tree_law_eq_walk_law (μ : PMF ℕ) (Q : PlaneTree → Prop) :
    bienaymeLaw μ.toMeasure (finiteTreeEvent Q) =
      (Measure.infinitePi fun _ : ℕ => μ.toMeasure)
        {ω | ∃ t : PlaneTree, Q t ∧ ω ∈ stoppedWordEvent 1 t.increments} := by
  exact BGWLeaves.LeafConcentration.WalkDeviation.tree_law_eq_walk_law μ Q

/-- **Lemma 2.5(ii) (`lem:GdesDev`)**, abstract form: for `0 < μ₀ < 1` and a polynomial lower bound
`P[ζ = n] ≥ n^{-A}` valid for those `n ≥ N` of positive mass, the conditional deviation probability
`P[ sup_{η ≤ t ≤ 1} |Λ_τ(nt)/(nt) - μ₀| ≥ δ n^{-1/4} | ζ = n ]` is `oe_{1/2}(n)`.  The conditional
law of a null event is `0` (`ProbabilityTheory.cond`), so the printed restriction to `n` with
`P[ζ = n] > 0` is automatic.  No criticality is used; the analytic input (the lower bound) is
isolated in `sizeProb_poly_lower`. -/
theorem lem_GdesDev_tree_of_lower (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) (A : ℝ) (N : ℕ)
    (hlow : ∀ n : ℕ, N ≤ n → bienaymeLaw μ.toMeasure (sizeEvent n) ≠ 0 →
      (n : ℝ) ^ (-A) ≤ (bienaymeLaw μ.toMeasure).real (sizeEvent n)) :
    IsOe (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|sizeEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t n))) := by
  exact BGWLeaves.LeafConcentration.TreeDeviation.lem_GdesDev_tree_of_lower μ h0 h1 hη0 hη1 hδ A N hlow

/-- The polynomial lower bound `P[ζ = n] ≥ n^{-1/θ-2}` for large `n` used in the proof of
Lemma 2.5(ii) (`largetrees_final.tex`, Section 2.5): by Lemma 1.11 (`n B_n P[ζ = n] → p₁(0) > 0`,
`B_n = h(n) n^{1/θ}`) and Proposition 1.7(i) (`h(n) ≤ n^ε` eventually; the paper cites 1.7(ii)).
Under `(H_θ)`, formalized as in M3 (critical, `μ 1 ≠ 1`, aperiodic, in a stable domain of attraction
of index `θ`; aperiodicity gives positive mass for all large `n`). -/
theorem sizeProb_poly_lower {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ b, StableDomain μ θ b) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (n : ℝ) ^ (-(1 / θ + 2)) ≤ (bienaymeLaw μ.toMeasure).real (sizeEvent n) := by
  exact BGWLeaves.LeafConcentration.SizeLower.sizeProb_poly_lower hc hne hap hDA

/-- **Lemma 2.5(ii) (`lem:GdesDev`)** under `(H_θ)` (formalized as in M3: critical, `μ 1 ≠ 1`,
aperiodic, `∃ b, StableDomain μ θ b`): for `0 < η < 1`, `δ > 0`,
`P[ sup_{η ≤ t ≤ 1} |Λ_τ(nt)/(nt) - μ₀| ≥ δ n^{-1/4} | ζ(τ) = n ]` is `oe_{1/2}(n)`.  The printed
restriction to `n` with `P[ζ = n] > 0` is automatic (the conditional law of a null event is `0`).
Assembled from `lem_GdesDev_tree_of_lower` and `sizeProb_poly_lower`; the assembly proof is kept. -/
theorem lem_GdesDev_tree {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ b, StableDomain μ θ b) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) :
    IsOe (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|sizeEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t n))) := by
  obtain ⟨N, hN⟩ := sizeProb_poly_lower hc hne hap hDA
  obtain ⟨b, hb⟩ := hDA
  have h0 : μ 0 ≠ 0 := hc.apply_zero_ne_zero hne
  have h1 : μ 0 ≠ 1 := by
    intro h
    have hsupp := (PMF.apply_eq_one_iff μ 0).1 h
    have hz : ∀ j : ℕ, j ≠ 0 → μ j = 0 := fun j hj => by
      by_contra hne'
      have : j ∈ μ.support := (PMF.mem_support_iff μ j).2 hne'
      rw [hsupp] at this
      exact hj (by simpa using this)
    have h0sum : ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 0 := by
      have : ∀ j : ℕ, (j : ℝ≥0∞) * μ j = 0 := fun j => by
        by_cases hj : j = 0
        · simp [hj]
        · simp [hz j hj]
      simp [this]
    have hcr := hc
    unfold IsCritical at hcr
    rw [h0sum] at hcr
    exact zero_ne_one hcr
  exact lem_GdesDev_tree_of_lower μ h0 h1 hη0 hη1 hδ _ N (fun n hn _ => hN n hn)

/-- **Corollary 2.6 (`cor:GD2mieux`)**: under `(H_θ)` (as in `lem_GdesDev_tree`), conditionally on
`ζ(τ) ≥ n` (`sizeGeEvent n`; this includes the null event of infinite trees), the probability that
`sup_{η ≤ t ≤ 1} |Λ_τ(ζ(τ) t)/(ζ(τ) t) - μ₀| ≥ δ n^{-1/4}` is `oe_{1/2}(n)`.  The threshold has the
fixed `n`, not `ζ^{-1/4}`. -/
theorem cor_GD2mieux {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ b, StableDomain μ θ b) {η δ : ℝ}
    (hη0 : 0 < η) (hη1 : η < 1) (hδ : 0 < δ) :
    IsOe (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|sizeGeEvent n]).real
        (finiteTreeEvent fun t =>
          ENNReal.ofReal (δ / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
            supDev η (treeLeafDev (μ 0).toReal t (t.size : ℝ)))) := by
  exact BGWLeaves.LeafConcentration.TreeDeviation.cor_GD2mieux hc hne hap hDA hη0 hη1 hδ

/-- **Lemma 2.7(i) (`lem:GdesDev2`)**: for `1 ≤ j ≤ n`, the joint probability (no division) that a
forest of `j` independent `GW_μ` trees has `ζ(f) = n` and `|λ(f)/n - μ₀| > δ n^{-1/4}` is
`oe_{1/2}(n)`, uniformly in `1 ≤ j ≤ n` (`IsOeUniform`).  Only `0 < μ₀ < 1` is used.  The event is
`{F | ∃ m, F ∈ forestEvent j n m ∧ δ / n^{1/4} < |m/n - μ₀|}` (`forestEvent j p m`: `ζ = p`, `λ = m`). -/
theorem lem_GdesDev2_i (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    IsOeUniform (1 / 2) fun j n : ℕ =>
      ((Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real
        {F | ∃ m : ℕ, F ∈ forestEvent j n m ∧
          δ / (n : ℝ) ^ (1 / 4 : ℝ) < |(m : ℝ) / n - (μ 0).toReal|}) := by
  exact BGWLeaves.LeafConcentration.ForestDeviation.lem_GdesDev2_i μ h0 h1 hδ

/-- **Lemma 2.7(ii) (`lem:GdesDev2`)**: for `1 ≤ j ≤ n`, the joint probability that `λ(f) = n` and
`|ζ(f) - n/μ₀| > ζ(f)^{3/4}` for a forest `f` of `j` independent `GW_μ` trees is `oe_{1/2}(n)`,
uniformly in `1 ≤ j ≤ n`.  Only `0 < μ₀ < 1` is used.  The event is
`{F | ∃ p, F ∈ forestEvent j p n ∧ p^{3/4} < |p - n/μ₀|}` (finite forests; `ζ = ∞` cannot satisfy
the inequality). -/
theorem lem_GdesDev2_ii (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) :
    IsOeUniform (1 / 2) fun j n : ℕ =>
      ((Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure).real
        {F | ∃ p : ℕ, F ∈ forestEvent j p n ∧
          (p : ℝ) ^ (3 / 4 : ℝ) < |(p : ℝ) - n / (μ 0).toReal|}) := by
  exact BGWLeaves.LeafConcentration.ForestDeviation.lem_GdesDev2_ii μ h0 h1

end BGWLeaves
