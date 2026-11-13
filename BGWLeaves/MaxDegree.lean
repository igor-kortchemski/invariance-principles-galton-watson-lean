module

public import BGWLeaves.MaxDegree.Defs
public import BGWLeaves.Vervaat
public import BGWLeaves.Conditioning
public import BGWLeaves.LocalEstimates
import BGWLeaves.MaxDegree.Proof

/-!
# Maximum degree of large trees, finite variance

Source: arXiv:1110.2163v4 (line numbers refer to its LaTeX source): Theorem 7.1(ii) (`thm:max`, finite variance, lines 2328-2486),
Lemma 7.2 (`lem:MM`, Meir and Moon) and the discrete lemmas of the proof of 7.1 (`eq:Deltanon`, `eq:i`, truncation to
the first half of the marks, reverse half, density bounds, tightness of the midpoint of the bridge), Remark 7.3
(`eq:better`, the window for the uniform tree law).

The proofs are in the modules `BGWLeaves.MaxDegree.*` (imported through `BGWLeaves.MaxDegree.Proof`).
Definitions and bridges are in `BGWLeaves.MaxDegree.Defs`.  The declarations `eq_Deltanon`, `eq_Deltanon_upper`,
`bridgeStepsLt_subset_prefix`, `lower_half_le`, `bridgeStepsGt_subset_split`, `chi_density_bound`,
`thm_max_ii`, `thm_max_ii_tendsto`, `neBot_leafProb_ne_zero` and `rem_uniformtree_window` are proved here
from other statements of this file (and of the principles).

Layout.
* hypothesis `𝓗` and the law: `HypH.mu_zero_pos`, `HypH.mu_zero_lt_one`,
  `HypH.not_isLatticeLaw_etaLaw_of_unbounded`, `stepTail_eq_offTail`, `offTail_*`, `tendsto_offTail`,
  `bigD_spec`, `eventually_bigD_spec`, `bigD_mono`, `tendsto_bigD_atTop_iff`, `bigD_eq_of_bounded`,
  `lem_MM` (Lemma 7.2), `MM_lower_limit`, `MM_upper_limit` (module `Law`).
* steps versus degrees and the transfer of the cyclic maximum: `maxDegree_lt_iff`, `lt_maxDegree_iff`,
  `maximum_increments`, `maxDegree_eq_zero_iff`, `two_le_maxDegree_of_two_le_leaves`,
  `transfer_vervaat_invariant`, `exists_isMarkTime_of_le`, `walkWord_take`, `IsMarkTime.last_step`
  (module `Transfer`).
* the first half of the marks (`eq:i`) and the reverse half: `bridge_reverse_half`, `eq_i_lower`, `eq_i_upper`
  (module `Bridge`).
* the density bounds and the tightness of the midpoint of the bridge (discrete replacement of
  `eq:trucsuperutile`): `chi_sup_bound`, `chi_zero_lower`, `wald_second_moment`, `bridge_midpoint_tight`
  (module `Concentration`).
* the principles and the inputs of the case split of 7.1(ii): `maxDegree_lower_principle`,
  `maxDegree_upper_principle` (both WITH `hnl`), `thm_max_ii_of_bounded`, `leafProb_ne_zero_frequently`,
  `displayedLaw_not_isLatticeLaw_etaLaw` (module `Principles`).
* Remark 7.3 (`eq:better`): `rem_uniformtree_window` (assembly).

Structure: the two principles are stated with the hypothesis `hnl : ¬ IsLatticeLaw (etaLaw μ)`; `thm_max_ii`
keeps the printed strength (`HypH` only, no `hnl`) and is a case split (unbounded support: `HypH` gives `hnl`;
bounded support: elementary argument `thm_max_ii_of_bounded`); `chi_density_bound` is derived from
`chi_sup_bound` and `chi_zero_lower`.  The window `eq:better` of Remark 7.3 needs no functional limit
theorem: the discrete tightness `bridge_midpoint_tight` replaces the bridge convergence `eq:trucsuperutile`.

Not stated here: see the comment at the end of this file.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- Notation only (the Vervaat notation is `local`): the law of the iid walk, steps `ω i - 1`. -/
local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

/-! ## 0. The hypothesis `𝓗` -/

/-- `μ₀ > 0` under `𝓗` ("Note that `μ₀ > 0` under `(H_θ)`", line 376). -/
theorem HypH.mu_zero_pos {μ : PMF ℕ} (h : HypH μ) : 0 < (μ 0).toReal := by
  exact BGWLeaves.MaxDegree.Law.HypH.mu_zero_pos h

theorem HypH.mu_zero_lt_one {μ : PMF ℕ} (h : HypH μ) : (μ 0).toReal < 1 := by
  exact BGWLeaves.MaxDegree.Law.HypH.mu_zero_lt_one h

/-- **`𝓗` and unbounded support give `hnl`**: if the support of `μ` is unbounded, then `μ(k) > 0`
for all large `k` (for `R < ∞` because `μ(n)^{1/n} → 1/R > 0`; for `R = ∞` because the non-increasing sequence
`μ(k)^{1/k}` stays positive once positive), so `etaLaw μ` (the law of `K - 1` given `K ≥ 1`) has two consecutive
atoms and is not lattice.  (For bounded support `hnl` can fail under `𝓗`, e.g.
`μ = (0.6, 0.2, 0, 0.1, 0, 0.1)`.) -/
theorem HypH.not_isLatticeLaw_etaLaw_of_unbounded {μ : PMF ℕ} (h : HypH μ)
    (hub : ∀ K : ℕ, ∃ k : ℕ, K < k ∧ μ k ≠ 0) : ¬ IsLatticeLaw (etaLaw μ) := by
  exact BGWLeaves.MaxDegree.Principles.HypH.not_isLatticeLaw_etaLaw_of_unbounded h hub

/-! ## 1. `D(n)` and the tails -/

/-- The `stepTail μ a = P[W_1 ≥ a]` is `μ([a+1, ∞))` (`W_1 = K - 1`).  This is the shift by one between
the degree and the step, in terms of tails. -/
theorem stepTail_eq_offTail (μ : PMF ℕ) (a : ℝ) : stepTail μ a = offTail μ (a + 1) := by
  exact BGWLeaves.MaxDegree.Law.stepTail_eq_offTail μ a

theorem offTail_antitone (μ : PMF ℕ) : Antitone (offTail μ) := by
  exact BGWLeaves.MaxDegree.Law.offTail_antitone μ

theorem offTail_of_nonpos (μ : PMF ℕ) {x : ℝ} (hx : x ≤ 0) : offTail μ x = 1 := by
  exact BGWLeaves.MaxDegree.Law.offTail_of_nonpos μ hx

theorem offTail_one (μ : PMF ℕ) : offTail μ 1 = 1 - (μ 0).toReal := by
  exact BGWLeaves.MaxDegree.Law.offTail_one μ

theorem tendsto_offTail (μ : PMF ℕ) : Tendsto (fun k : ℕ => offTail μ k) atTop (𝓝 0) := by
  exact BGWLeaves.MaxDegree.Law.tendsto_offTail μ

/-- **Existence of `D(n)` on the indices used.**  For `n ≥ 1` with `1/n ≤ 1 - μ₀` (i.e. `μ([1,∞)) ≥ 1/n`),
the set `{k ≥ 1 ; μ([k,∞)) ≥ 1/n}` is nonempty, bounded (`μ([k,∞)) → 0`), and `D(n)` is its largest element.
Holds for all `n ≥ 1/(1-μ₀)`, in particular eventually when `μ₀ < 1`. -/
theorem bigD_spec (μ : PMF ℕ) {n : ℕ} (hn : 1 ≤ n) (h : 1 / (n : ℝ) ≤ 1 - (μ 0).toReal) :
    IsGreatest {k : ℕ | 1 ≤ k ∧ 1 / (n : ℝ) ≤ offTail μ k} (bigD μ n) := by
  exact BGWLeaves.MaxDegree.Law.bigD_spec μ hn h

theorem eventually_bigD_spec {μ : PMF ℕ} (h : μ 0 ≠ 1) :
    ∀ᶠ n : ℕ in atTop, IsGreatest {k : ℕ | 1 ≤ k ∧ 1 / (n : ℝ) ≤ offTail μ k} (bigD μ n) := by
  exact BGWLeaves.MaxDegree.Law.eventually_bigD_spec h

/-- `D(n+1) ≥ D(n)` (for the indices where `D` is defined). -/
theorem bigD_mono {μ : PMF ℕ} (h : μ 0 ≠ 1) : ∀ᶠ n : ℕ in atTop, bigD μ n ≤ bigD μ (n + 1) := by
  exact BGWLeaves.MaxDegree.Law.bigD_mono h

/-- `D(n) → ∞` iff the support of `μ` is unbounded; if `μ` has bounded support with largest atom `K`
then `D(n) = K` eventually (used to see that Lemma 7.2 and Theorem 7.1(ii) have no hidden degenerate case). -/
theorem tendsto_bigD_atTop_iff {μ : PMF ℕ} (h : μ 0 ≠ 1) :
    Tendsto (bigD μ) atTop atTop ↔ ∀ K : ℕ, ∃ k : ℕ, K < k ∧ μ k ≠ 0 := by
  exact BGWLeaves.MaxDegree.Law.tendsto_bigD_atTop_iff h

theorem bigD_eq_of_bounded {μ : PMF ℕ} {K : ℕ} (hK1 : 1 ≤ K) (hK : μ K ≠ 0) (hb : ∀ k : ℕ, K < k → μ k = 0) :
    ∀ᶠ n : ℕ in atTop, bigD μ n = K := by
  exact BGWLeaves.MaxDegree.Law.bigD_eq_of_bounded hK1 hK hb

/-! ## 2. Lemma 7.2 (`lem:MM`, Meir and Moon) -/

/-- **Lemma 7.2 (`lem:MM`)**, as printed: for `ε > 0` and `n` large,
`μ([(1-ε) D(n), ∞)) ≥ n^{-1/(1+ε/3)}` and `μ([(1+ε) D(n), ∞)) ≤ n^{-1-ε/3}`, under `𝓗`.
NOT a cited input: it is a statement about the law only and is derivable from `𝓗` by an elementary
argument (`𝓗` with `R < ∞` gives `tail(k) = R^{-k(1+o(1))}` and `D(n) ~ ln n / ln R`;
`𝓗` with `R = ∞` gives `ν(k) ≤ tail(k) ≤ 2ν(k)` and `a_k = ν(k)^{1/k}` decreasing; bounded support is trivial). -/
theorem lem_MM {μ : PMF ℕ} (h : HypH μ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (-(1 / (1 + ε / 3))) ≤ offTail μ ((1 - ε) * (bigD μ n : ℝ)) ∧
        offTail μ ((1 + ε) * (bigD μ n : ℝ)) ≤ (n : ℝ) ^ (-1 - ε / 3) := by
  exact BGWLeaves.MaxDegree.Law.lem_MM h hε

/-- **Corollary of 7.2 for the lower bound (corrected shift).**  With `p_n = (1-ε) D(n) - 1` (NOT the printed
`(1-ε) D(n)`: with `W_1 = K - 1` the printed step is off by one), `P[W_1 ≥ p_n] = μ([(1-ε) D(n), ∞)) ≥
n^{-1/(1+ε/3)}`, hence the hypothesis of `maxDegree_lower_principle`: `(1 - P[W_1 ≥ p_n])^{n/(4μ₀)} → 0`. -/
theorem MM_lower_limit {μ : PMF ℕ} (h : HypH μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ ((1 - ε) * (bigD μ n : ℝ) - 1)) ^ ((n : ℝ) / (4 * (μ 0).toReal))) atTop (𝓝 0) := by
  exact BGWLeaves.MaxDegree.Law.MM_lower_limit h hε

/-- **Corollary of 7.2 for the upper bound (corrected shift).**  With `q_n = (1+ε) D(n) - 1`,
`P[W_1 ≥ q_n] = μ([(1+ε) D(n), ∞)) ≤ n^{-1-ε/3}`, hence the hypothesis of `maxDegree_upper_principle`:
`(1 - P[W_1 ≥ q_n])^{n/μ₀} → 1` (Bernoulli: `≥ 1 - n^{-ε/3}/μ₀`). -/
theorem MM_upper_limit {μ : PMF ℕ} (h : HypH μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ ((1 + ε) * (bigD μ n : ℝ) - 1)) ^ ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 1) := by
  exact BGWLeaves.MaxDegree.Law.MM_upper_limit h hε

/-! ## 3. Steps versus degrees: the difference of one -/

/-- `Δ(τ) = M(W_1(τ) - W_0(τ), …, W_ζ(τ) - W_{ζ-1}(τ)) + 1` (line 2390), the printed identity, in the
form of the equivalences used in the proof: `Δ(τ) < p + 1 ⟺ M < p` ... -/
theorem maxDegree_lt_iff (t : PlaneTree) (p : ℝ) :
    (maxDegree t : ℝ) < p + 1 ↔ StepsLt p t.increments := by
  exact BGWLeaves.MaxDegree.Transfer.maxDegree_lt_iff t p

/-- ... and `Δ(τ) > q + 1 ⟺ M > q`. -/
theorem lt_maxDegree_iff (t : PlaneTree) (q : ℝ) :
    q + 1 < (maxDegree t : ℝ) ↔ StepsGt q t.increments := by
  exact BGWLeaves.MaxDegree.Transfer.lt_maxDegree_iff t q

/-- The exact identity: the largest increment of the Łukasiewicz word is `Δ(τ) - 1` (as an element of
`WithBot ℤ`, `List.maximum`; the word is never empty). -/
theorem maximum_increments (t : PlaneTree) :
    t.increments.maximum = (((maxDegree t : ℤ) - 1 : ℤ) : WithBot ℤ) := by
  exact BGWLeaves.MaxDegree.Transfer.maximum_increments t

/-- Exceptional one-vertex convention: `Δ(τ) = 0` iff `τ` is the one-vertex tree.  For this tree the
largest increment is `-1 = Δ - 1`, but the largest jump of the step path "with value `0` when there is no
positive jump" would be `0 ≠ Δ - 1`.  So the printed "`Δ̄(W(τ)) = Δ(τ) - 1`" (line 2362) holds for every tree
except the one-vertex tree, under the convention `Δ̄(Z) = max(0, sup of the jumps)`. -/
theorem maxDegree_eq_zero_iff (t : PlaneTree) : maxDegree t = 0 ↔ t.size = 1 := by
  exact BGWLeaves.MaxDegree.Transfer.maxDegree_eq_zero_iff t

/-- A tree with at least two leaves has a vertex with at least two children, so `Δ ≥ 2` and the largest
increment `Δ - 1 ≥ 1` is positive.  (So for `τ_n`, `n ≥ 2`, no convention for the one-vertex tree or for paths
matters.) -/
theorem two_le_maxDegree_of_two_le_leaves (t : PlaneTree) (h : 2 ≤ t.degreeCount 0) : 2 ≤ maxDegree t := by
  exact BGWLeaves.MaxDegree.Transfer.two_le_maxDegree_of_two_le_leaves t h

/-! ## 4. Transfer of the cyclic maximum (`eq:Deltanon`) -/

/-- **General form of `eq:Deltanon` (second equality of line 2394 and third).**  For a set `S` of words invariant
under the Vervaat transform (`V(u) ∈ S ⟺ u ∈ S`), and `n ≥ 1`,
`P_μ[(increments of τ) ∈ S | λ(τ) = n] = P[(W_1, …, W_{T_n} - W_{T_n-1}) ∈ S | W_{T_n} = -1]`.
From `prop_vervaatdiscrete` (6.5) on atoms: both events are countable disjoint unions over `x ∈ S` of the atoms
(`List ℤ` is countable).  The null case `P_μ[λ = n] = 0` is the zero-measure convention (both sides `0`). -/
theorem transfer_vervaat_invariant (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n)
    (S : Set (List ℤ)) (hS : ∀ x : List ℤ, vervaat x ∈ S ↔ x ∈ S) :
    ((bienaymeLaw μ)[|leafCountEvent n]) (treeStepsIn S) =
      ((𝐏w[μ])[|bridgeAtMark n]) (bridgeStepsIn n S) := by
  exact BGWLeaves.MaxDegree.Transfer.transfer_vervaat_invariant μ hn S hS

/-- **`eq:Deltanon`** (line 2394): `P[Δ(τ_n) < p + 1] = E[1{M(Z^{T_n}) < p} | W_{T_n} = -1]`, for every real `p`
(the paper has `p = p_n`).  Derived from `transfer_vervaat_invariant`, `stepsLt_vervaat`, `maxDegree_lt_iff`.
(The printed third expression is this one: `F^{(n)}(V(u)) = F^{(n)}(u)`.) -/
theorem eq_Deltanon (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) (p : ℝ) :
    ((bienaymeLaw μ)[|leafCountEvent n]) (finiteTreeEvent fun t => (maxDegree t : ℝ) < p + 1) =
      ((𝐏w[μ])[|bridgeAtMark n]) (bridgeStepsIn n {x | StepsLt p x}) := by
  have h1 : (finiteTreeEvent fun t => (maxDegree t : ℝ) < p + 1) = treeStepsIn {x | StepsLt p x} := by
    unfold treeStepsIn
    congr 1
    funext t
    exact propext (maxDegree_lt_iff t p)
  rw [h1]
  exact transfer_vervaat_invariant μ hn _ (fun x => stepsLt_vervaat p x)

/-- **`P[Δ(τ_n) > q + 1] = P[M(Z^{T_n}) > q | W_{T_n} = -1]`** (the sentence "by an argument similar to the one we
used to establish `eq:Deltanon`", line 2431). -/
theorem eq_Deltanon_upper (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) (q : ℝ) :
    ((bienaymeLaw μ)[|leafCountEvent n]) (finiteTreeEvent fun t => q + 1 < (maxDegree t : ℝ)) =
      ((𝐏w[μ])[|bridgeAtMark n]) (bridgeStepsIn n {x | StepsGt q x}) := by
  have h1 : (finiteTreeEvent fun t => q + 1 < (maxDegree t : ℝ)) = treeStepsIn {x | StepsGt q x} := by
    unfold treeStepsIn
    congr 1
    funext t
    exact propext (lt_maxDegree_iff t q)
  rw [h1]
  exact transfer_vervaat_invariant μ hn _ (fun x => stepsGt_vervaat q x)

/-! ## 5. Truncation to the first half of the marks, and the reverse half -/

/-- `T_m ≤ T_n` and `T_m < ∞` when `T_n < ∞` and `m ≤ n` (`Λ` increases by steps of `0` or `1`, from `Λ(0) = 0`). -/
theorem exists_isMarkTime_of_le {n m : ℕ} {ω : ℕ → ℕ} {k : ℕ} (h : IsMarkTime n ω k) (hmn : m ≤ n) :
    ∃ k' : ℕ, k' ≤ k ∧ IsMarkTime m ω k' := by
  exact BGWLeaves.MaxDegree.Transfer.exists_isMarkTime_of_le h hmn

/-- The prefix of the word of the first `k` steps is the word of the first `k'` steps. -/
theorem walkWord_take (ω : ℕ → ℕ) {k' k : ℕ} (h : k' ≤ k) : (walkWord ω k).take k' = walkWord ω k' := by
  exact BGWLeaves.MaxDegree.Transfer.walkWord_take ω h

/-- The mark steps: the `T_m`-th step of the walk is `-1` (`ω (T_m - 1) = 0`) for `m ≥ 1`. -/
theorem IsMarkTime.last_step {m : ℕ} (hm : 1 ≤ m) {ω : ℕ → ℕ} {k : ℕ} (h : IsMarkTime m ω k) :
    1 ≤ k ∧ ω (k - 1) = 0 := by
  exact BGWLeaves.MaxDegree.Transfer.IsMarkTime.last_step hm h

/-- **Truncation to the first half (the inequality `E[F_{T_n}(W) | …] ≤ E[F_{T_{n/2}}(W) | …]` of line 2401,
and the upper-bound analogue is `stepsGt_take_or_drop`).**  For `m ≤ n`, the event "`M(Z^{T_n}) < p` (on the
bridge)" is contained in "`M(Z^{T_m}) < p`".  The paper's `n/2` is `m = ⌊n/2⌋` (`T_u = T_{⌊u⌋}`). -/
theorem bridgeStepsLt_subset_prefix {n m : ℕ} (hmn : m ≤ n) (p : ℝ) :
    bridgeStepsIn n {x | StepsLt p x} ⊆ prefixStepsIn m {x | StepsLt p x} := by
  rintro ω ⟨k, hk, -, hS⟩
  obtain ⟨k', hk'k, hk'⟩ := exists_isMarkTime_of_le hk hmn
  refine ⟨k', hk', ?_⟩
  have := stepsLt_take (j := k') hS
  rwa [walkWord_take ω hk'k] at this

/-- Conditional form: `P[M(Z^{T_n}) < p | W_{T_n} = -1] ≤ P[M(Z^{T_m}) < p | W_{T_n} = -1]`. -/
theorem lower_half_le (μ : Measure ℕ) [IsProbabilityMeasure μ] {n m : ℕ} (hmn : m ≤ n) (p : ℝ) :
    ((𝐏w[μ])[|bridgeAtMark n]) (bridgeStepsIn n {x | StepsLt p x}) ≤
      ((𝐏w[μ])[|bridgeAtMark n]) (prefixStepsIn m {x | StepsLt p x}) :=
  measure_mono (bridgeStepsLt_subset_prefix hmn p)

/-- Upper bound, first piece (the split of line 2431): under the bridge, "`M(Z^{T_n}) > q`" is contained in
"`M(Z^{T_m}) > q`" or "`M` of the steps after `T_m` `> q`". -/
theorem bridgeStepsGt_subset_split {n m : ℕ} (hmn : m ≤ n) (q : ℝ) :
    bridgeStepsIn n {x | StepsGt q x} ⊆
      prefixStepsIn m {x | StepsGt q x} ∪
        {ω | ∃ k, IsMarkTime n ω k ∧ walkSum ω k = -1 ∧ ∃ k', IsMarkTime m ω k' ∧
          StepsGt q ((walkWord ω k).drop k')} := by
  rintro ω ⟨k, hk, hs, hS⟩
  obtain ⟨k', hk'k, hk'⟩ := exists_isMarkTime_of_le hk hmn
  rcases stepsGt_take_or_drop hS k' with h | h
  · left
    refine ⟨k', hk', ?_⟩
    rwa [walkWord_take ω hk'k] at h
  · right
    exact ⟨k, hk, hs, k', hk', h⟩

/-- **The reverse-half upper bound (the "time-reversal argument based on Proposition 6.8", line 2433).**
For `1 ≤ m < n` and EVERY real `q`: under `P[· | W_{T_n} = -1]`, the event "some step after `T_m` is `> q`" has the
SAME probability as "some step among `Z^{T_{n-m}}` is `> q`" (the first `n - m` marks).  Proof: on `{T_n = k}` the last
step is the mark `-1`, `W_{k-1} = 0`, `Λ(k-1) = n - 1`; reversal of the first `k - 1` steps (6.8 for `(k-1, n-1)`)
preserves the conditional law, exchanges the steps after the `m`-th mark (there are `n-1-m` marks among them,
and the step before them, in reversed order, is the `m`-th mark) with the steps before the `(n-m)`-th mark;
the extra last step `-1` and the step `-1` at `T_{n-m}` do not matter for `q ≥ -1`, and for `q < -1` both events are
the whole bridge mass (every step is `≥ -1` and both words are nonempty): so no hypothesis `-1 ≤ q` is
needed.
NOTE the index: it is `n - m` (`= ⌈n/2⌉` for `m = ⌊n/2⌋`), not `m`; the paper's single "`n/2`" hides this. -/
theorem bridge_reverse_half (μ : Measure ℕ) [IsProbabilityMeasure μ] {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (q : ℝ) :
    ((𝐏w[μ])[|bridgeAtMark n])
        {ω | ∃ k, IsMarkTime n ω k ∧ walkSum ω k = -1 ∧ ∃ k', IsMarkTime m ω k' ∧
          StepsGt q ((walkWord ω k).drop k')} =
      ((𝐏w[μ])[|bridgeAtMark n]) (prefixStepsIn (n - m) {x | StepsGt q x}) := by
  exact BGWLeaves.MaxDegree.Bridge.bridge_reverse_half μ hm hmn q

/-! ## 6. Density bounds and the first-half estimate (`eq:i`) -/

/-- `χ_n(j) ≤ C/√n`, uniformly in the starting point `j ∈ ℤ` and all `n ≥ 1` (`χ_k(j) = P_j[W_{T_k} = -1]` is
`BGWLeaves.chi`).  A global bound, NOT part of 6.11 which has the window `|j| ≤ αB_n`; from the
exact decomposition `chi_eq_tsum` and the uniform local limit bound for `W'`, `sup_x P[W'_q = x] ≤ C/√(q+1)`. -/
theorem chi_sup_bound {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 1 ≤ n → ∀ j : ℤ, (chi μ n j).toReal ≤ C / Real.sqrt n := by
  exact BGWLeaves.MaxDegree.Concentration.chi_sup_bound h hnl

/-- `χ_n(0) ≥ c/√n` for large `n` (the remark after 6.11: `χ_n(0) ∼ p₁(0)/B_{n/μ₀}`; `chi_zero_asymp`). -/
theorem chi_zero_lower {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop, c / Real.sqrt n ≤ (chi μ n 0).toReal := by
  exact BGWLeaves.MaxDegree.Concentration.chi_zero_lower h hnl

/-- **Density bound** ("By Lemma 6.11 there exists `C > 0` such that for every `n` large enough,
`χ_{n-⌊n/2⌋}(W_{T_{n/2}})/χ_n(0) ≤ C` on the event `A_n^α`", lines 2410-2412).  `m n` is `⌊n/2⌋` or `⌈n/2⌉`
(`n/2 ≤ m n ≤ (n+1)/2`).  Derived from `chi_sup_bound` and `chi_zero_lower`: the bound holds for
ALL `j ∈ ℤ`, so no window `|j| ≤ α√n` is needed.  `hnl` is the hypothesis of those two. -/
theorem chi_density_bound {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {m : ℕ → ℕ} (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ,
      (chi μ (n - m n) j).toReal ≤ C * (chi μ n 0).toReal := by
  obtain ⟨C₁, hC₁, hsup⟩ := chi_sup_bound h hnl
  obtain ⟨c, hc, hlow⟩ := chi_zero_lower h hnl
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hlow
  refine ⟨C₁ * Real.sqrt 3 / c, by positivity, max N₀ 3, fun n hn j => ?_⟩
  have hn3 : 3 ≤ n := le_trans (le_max_right _ _) hn
  have hnN : N₀ ≤ n := le_trans (le_max_left _ _) hn
  have hmn := (hm n).2
  have hk : 1 ≤ n - m n := by omega
  have h1 := hsup (n - m n) hk j
  have h3 : n ≤ 3 * (n - m n) := by omega
  have h3r : (n : ℝ) ≤ 3 * ((n - m n : ℕ) : ℝ) := by exact_mod_cast h3
  have hkpos : (0 : ℝ) < ((n - m n : ℕ) : ℝ) := by exact_mod_cast hk
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have ha : 0 < Real.sqrt ((n - m n : ℕ) : ℝ) := Real.sqrt_pos.2 hkpos
  have hb : 0 < Real.sqrt n := Real.sqrt_pos.2 hnpos
  have hbd : Real.sqrt n ≤ Real.sqrt 3 * Real.sqrt ((n - m n : ℕ) : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt h3r
  have h2 : C₁ / Real.sqrt ((n - m n : ℕ) : ℝ) ≤ C₁ * Real.sqrt 3 / Real.sqrt n := by
    rw [div_le_div_iff₀ ha hb]
    nlinarith
  have h4 := hN₀ n hnN
  have h5 : C₁ * Real.sqrt 3 / Real.sqrt n = (C₁ * Real.sqrt 3 / c) * (c / Real.sqrt n) := by
    field_simp
  calc (chi μ (n - m n) j).toReal ≤ C₁ / Real.sqrt ((n - m n : ℕ) : ℝ) := h1
    _ ≤ C₁ * Real.sqrt 3 / Real.sqrt n := h2
    _ = (C₁ * Real.sqrt 3 / c) * (c / Real.sqrt n) := h5
    _ ≤ (C₁ * Real.sqrt 3 / c) * (chi μ n 0).toReal := by
        gcongr

/-- **`eq:i` (lower bound)** (line 2418): for `m = ⌊n/2⌋` or `⌈n/2⌉`, `α > 0`, uniformly in the threshold `p`,
`P[M(Z^{T_m}) < p | W_{T_n} = -1] ≤ P[|W_{T_m}| ≥ α√n | W_{T_n} = -1] + C P[W_1 < p]^{⌊n/(4μ₀)⌋} + C e^{-c√n}`.
Steps of the paper: `lem:CVf2(i)` (concentration of `T_m` in `[n/(4μ₀), n/μ₀]`), `lem:absolueC2` (strong Markov),
`chi_density_bound`, then `M(Z^{T_m}) < p` and `T_m ≥ n/(4μ₀)` imply `M(Z^{⌊n/4μ₀⌋}) < p`, whose probability
is `P[W_1 < p]^{⌊n/4μ₀⌋} = (1 - stepTail μ p)^{⌊n/4μ₀⌋}`.  `oe_{1/2}(n)` is absorbed in `C e^{-c√n}`. -/
theorem eq_i_lower {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {m : ℕ → ℕ} (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) {α : ℝ} (hα : 0 < α) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ,
      (((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (prefixStepsIn (m n) {x | StepsLt p x})) ≤
        ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
            {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} +
          C * (1 - stepTail μ p) ^ ⌊(n : ℝ) / (4 * (μ 0).toReal)⌋₊ + C * Real.exp (-c * Real.sqrt n) := by
  exact BGWLeaves.MaxDegree.Bridge.eq_i_lower h hnl hm hα

/-- **`eq:i` (upper bound analogue)** (lines 2433-2440): `P[M(Z^{T_m}) > q | W_{T_n} = -1] ≤
P[|W_{T_m}| ≥ α√n | W_{T_n} = -1] + C (1 - (1 - P[W_1 > q])^{⌊n/μ₀⌋}) + C e^{-c√n}`
(the paper has the strict tail `P[W_1 > q]`, which is smaller; `stepTail` with `≥` gives the weaker bound that the
principle uses). -/
theorem eq_i_upper {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {m : ℕ → ℕ} (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) {α : ℝ} (hα : 0 < α) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ,
      (((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (prefixStepsIn (m n) {x | StepsGt q x})) ≤
        ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
            {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} +
          C * (1 - (1 - stepTail μ q) ^ ⌊(n : ℝ) / (μ 0).toReal⌋₊) + C * Real.exp (-c * Real.sqrt n) := by
  exact BGWLeaves.MaxDegree.Bridge.eq_i_upper h hnl hm hα

/-! ## 7. Tightness at the midpoint (`eq:trucsuperutile`), discrete form -/

/-- Wald's identities for the stopping time `T_m` (`E T_m = m/μ₀ < ∞`; mean-zero steps of variance `σ²`):
`E[W_{T_m}] = 0` and `E[W_{T_m}²] = σ² E[T_m] = σ² m/μ₀`.  (Only the second moment is used.) -/
theorem wald_second_moment {μ : PMF ℕ} (h : HypH μ) (m : ℕ) :
    ∫ ω, ((walkAtMark m ω : ℤ) : ℝ) ^ 2 ∂(𝐏w[μ.toMeasure]) =
      variance (stepLaw μ) * (m : ℝ) / (μ 0).toReal := by
  exact BGWLeaves.MaxDegree.Concentration.wald_second_moment h m

/-- **Tightness of the midpoint under the bridge law, WITHOUT any functional limit** (the discrete form of
`eq:trucsuperutile`, line 2269; the paper derives it from the convergence `eq:cvBr`, which needs `lem:CVf2(ii)` and
`prop:bridge(ii)`, the cited bridge law).  Here: `lem_absolueC2_k` with `f = 1{|W_{T_m}| ≥ α√n}`, the global bound
`chi_sup_bound`, the lower bound `chi_zero_lower`, and Chebyshev with `wald_second_moment`:
`P[|W_{T_m}| ≥ α√n | W_{T_n} = -1] ≤ (C√n/(c√(n-m))) σ² m/(μ₀ α² n) ≤ C'/α²`. -/
theorem bridge_midpoint_tight {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {m : ℕ → ℕ} (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) :
    ∀ ε : ℝ, 0 < ε → ∃ α : ℝ, 0 < α ∧ ∀ᶠ n : ℕ in atTop,
      ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
        {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} < ε := by
  exact BGWLeaves.MaxDegree.Concentration.bridge_midpoint_tight h hnl hm

/-! ## 8. The principles (with `hnl`) -/

/-- **The argument of the proof of Theorem 7.1(ii), isolated for arbitrary thresholds** (the sentence "the proof of
Theorem 7.1 shows that it is sufficient to verify ..." of Remark 7.3), lower bound: for critical aperiodic `μ` of
finite variance and real `p_n` with `(1 - P[W_1 ≥ p_n])^{n/4μ₀} → 0`, `P[Δ(τ_n) < p_n + 1] → 0`.
Chain (modules `Bridge`, `Concentration`): `eq_Deltanon`, `lower_half_le`, `eq_i_lower`, `bridge_midpoint_tight`,
with `lem_CVf2_i` (6.2(i)), `lem_absolueC2` (6.10) and `lem_technic3` (6.11).  The hypothesis
`hnl : ¬ IsLatticeLaw (etaLaw μ)` is the one of 6.11: the proof uses 6.11, which needs it;
`Theorem 7.1(ii)` does not use it for bounded support (`thm_max_ii_of_bounded`). -/
theorem maxDegree_lower_principle {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {p : ℕ → ℝ}
    (hp : Tendsto (fun n : ℕ => (1 - stepTail μ (p n)) ^ ((n : ℝ) / (4 * (μ 0).toReal)))
      atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t => (maxDegree t : ℝ) < p n + 1))) atTop (𝓝 0) := by
  exact BGWLeaves.MaxDegree.Principles.maxDegree_lower_principle hc hne hap hfin hnl hp

/-- The upper bound of the same argument: if `(1 - P[W_1 ≥ q_n])^{n/μ₀} → 1` then `P[Δ(τ_n) > q_n + 1] → 0`
(the proof uses the strict tail `P[W_1 > q_n] ≤ P[W_1 ≥ q_n]`; chain `eq_Deltanon_upper`,
`bridgeStepsGt_subset_split`, `bridge_reverse_half`, `eq_i_upper`, `bridge_midpoint_tight`), WITH `hnl` as above. -/
theorem maxDegree_upper_principle {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℝ}
    (hq : Tendsto (fun n : ℕ => (1 - stepTail μ (q n)) ^ ((n : ℝ) / (μ 0).toReal))
      atTop (𝓝 1)) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t => q n + 1 < (maxDegree t : ℝ)))) atTop (𝓝 0) := by
  exact BGWLeaves.MaxDegree.Principles.maxDegree_upper_principle hc hne hap hfin hnl hq

/-! ## 9. Theorem 7.1(ii) (`thm:max`), finite variance -/

/-- **Bounded support, elementary argument** (no 6.11, no `hnl`).  For `𝓗` with `μ(k) = 0` for
`k > K` and `μ(K) ≠ 0` (`K ≥ 1` follows from `𝓗`): `D(n) = K` eventually, `Δ ≤ K` always, and
`P_μ[λ = n, Δ < K] = (1/n) P[W_{T_n} = -1, all steps ≤ K-2] ≤ (1/n) ∑_{k ≥ n} (1-μ(K))^k = (1-μ_K)^n/(n μ_K)`
(Vervaat identity `transfer_vervaat_invariant`, joint form of 6.5; `T_n ≥ n`), while `P_μ[λ = n] ≥ c n^{-3/2}`
along the non-null `n` (Theorem 3.1, arithmetic form, `LeafMass`).  So `P[Δ < K | λ = n] → 0` along the
non-null `n`, lattice or not.  The conclusion is exactly that of `thm_max_ii`. -/
theorem thm_max_ii_of_bounded {μ : PMF ℕ} (h : HypH μ) {K : ℕ} (hK : μ K ≠ 0)
    (hb : ∀ k : ℕ, K < k → μ k = 0) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → leafProb μ n ≠ 0 →
      1 - δ ≤ ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          (1 - ε) * (bigD μ n : ℝ) ≤ (maxDegree t : ℝ) ∧ (maxDegree t : ℝ) ≤ (1 + ε) * (bigD μ n : ℝ)) := by
  exact BGWLeaves.MaxDegree.Principles.thm_max_ii_of_bounded h hK hb hε hδ

/-- **Theorem 7.1(ii)** (`thm:max`), finite variance and `𝓗`, AT THE PRINTED STRENGTH (no `hnl`): for every `ε > 0`
and `δ > 0` there is `N` such that for all `n ≥ N` with `P_μ[λ(τ) = n] > 0`,
`P[(1-ε) D(n) ≤ Δ(τ_n) ≤ (1+ε) D(n)] ≥ 1 - δ` (this is the printed "`→ 1`" along the `n` for which `τ_n` is
defined; `τ_n ∼ P_μ[· | λ = n]`).  The printed hypotheses: `(H_θ)` with `σ² < ∞`, and `𝓗`; the Lean hypothesis is
`HypH μ` (= `(H_2)` + `𝓗`, `HypH.hthetaTail`, plus `μ 1 ≠ 1` from `(H_θ)(i)`).

`hnl` is deliberately NOT a hypothesis (it would silently drop the lattice laws of bounded support, a
specialisation of the printed claim).  Proof, a case split on the support (`tendsto_bigD_atTop_iff`):
* unbounded support: `HypH` implies `hnl` (`HypH.not_isLatticeLaw_etaLaw_of_unbounded`), and the two principles
  `maxDegree_lower_principle` (`p_n = (1-ε) D(n) - 1`, `MM_lower_limit`) and `maxDegree_upper_principle`
  (`q_n = (1+ε) D(n) - 1`, `MM_upper_limit`) give `P[Δ < (1-ε)D] → 0` and `P[Δ > (1+ε)D] → 0`;
* bounded support: `thm_max_ii_of_bounded`.
This is proved here from those statements. -/
theorem thm_max_ii {μ : PMF ℕ} (h : HypH μ) {ε : ℝ} (hε : 0 < ε) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → leafProb μ n ≠ 0 →
      1 - δ ≤ ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          (1 - ε) * (bigD μ n : ℝ) ≤ (maxDegree t : ℝ) ∧ (maxDegree t : ℝ) ≤ (1 + ε) * (bigD μ n : ℝ)) := by
  by_cases hub : ∀ K : ℕ, ∃ k : ℕ, K < k ∧ μ k ≠ 0
  · have hnl := h.not_isLatticeLaw_etaLaw_of_unbounded hub
    have hA := maxDegree_lower_principle h.critical h.nondegenerate h.aperiodic h.integrable_sq hnl
      (p := fun n : ℕ => (1 - ε) * (bigD μ n : ℝ) - 1) (MM_lower_limit h hε)
    have hB := maxDegree_upper_principle h.critical h.nondegenerate h.aperiodic h.integrable_sq hnl
      (q := fun n : ℕ => (1 + ε) * (bigD μ n : ℝ) - 1) (MM_upper_limit h hε)
    simp only [sub_add_cancel] at hA hB
    have hδ2 : 0 < δ / 2 := by linarith
    obtain ⟨N₁, hN₁⟩ := eventually_atTop.1 ((tendsto_order.1 hA).2 _ hδ2)
    obtain ⟨N₂, hN₂⟩ := eventually_atTop.1 ((tendsto_order.1 hB).2 _ hδ2)
    refine ⟨max N₁ N₂, fun n hn hne => ?_⟩
    have h1 := hN₁ n (le_trans (le_max_left _ _) hn)
    have h2 := hN₂ n (le_trans (le_max_right _ _) hn)
    have key := cond_leafCount_window_ge (bienayme_leafCountEvent_ne_zero hne)
      (fun t => (maxDegree t : ℝ) < (1 - ε) * (bigD μ n : ℝ))
      (fun t => (1 + ε) * (bigD μ n : ℝ) < (maxDegree t : ℝ))
      (fun t => (1 - ε) * (bigD μ n : ℝ) ≤ (maxDegree t : ℝ) ∧
        (maxDegree t : ℝ) ≤ (1 + ε) * (bigD μ n : ℝ))
      (fun t _ => by
        by_cases a : (maxDegree t : ℝ) < (1 - ε) * (bigD μ n : ℝ)
        · exact Or.inl a
        · by_cases b : (1 + ε) * (bigD μ n : ℝ) < (maxDegree t : ℝ)
          · exact Or.inr (Or.inl b)
          · exact Or.inr (Or.inr ⟨not_lt.1 a, not_lt.1 b⟩))
    linarith
  · push Not at hub
    obtain ⟨K₀, hK₀⟩ := hub
    have hne : {k : ℕ | μ k ≠ 0}.Nonempty := by
      by_contra hcon
      rw [Set.not_nonempty_iff_eq_empty] at hcon
      have hz : ∀ k, μ k = 0 := fun k => by
        by_contra hk
        have : k ∈ {k : ℕ | μ k ≠ 0} := hk
        rw [hcon] at this
        exact this
      have := μ.tsum_coe
      simp [hz] at this
    have hbdd : BddAbove {k : ℕ | μ k ≠ 0} := ⟨K₀, fun k hk => by
      by_contra hlt
      exact hk (hK₀ k (not_le.1 hlt))⟩
    have hmem := Nat.sSup_mem hne hbdd
    exact thm_max_ii_of_bounded h hmem (fun k hk => by
      by_contra hk0
      exact absurd (le_csSup hbdd hk0) (not_le.2 hk)) hε hδ

/-- `P_μ[λ(τ) = n] > 0` for infinitely many `n` (for `hc hne`, lattice or not): the trees with
`n = 1 + a(k-1)` leaves (a root of degree `k ≥ 2` with `μ(k) > 0`, then `a` iterated branchings) have positive mass,
for infinitely many `n`. -/
theorem leafProb_ne_zero_frequently {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ᶠ n : ℕ in atTop, leafProb μ n ≠ 0 := by
  exact BGWLeaves.MaxDegree.Principles.leafProb_ne_zero_frequently hc hne

/-- The filter `atTop ⊓ 𝓟 {n | P_μ[λ = n] ≠ 0}` of the non-null indices is `NeBot`, so the `Tendsto`
statement `thm_max_ii_tendsto` along it is not vacuous. -/
theorem neBot_leafProb_ne_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    (atTop ⊓ 𝓟 {n : ℕ | leafProb μ n ≠ 0}).NeBot :=
  Filter.frequently_iff_neBot.1 (leafProb_ne_zero_frequently hc hne)

/-- The same as `Tendsto`, along the filter of non-null indices, for the printed `→ 1` form (the filter
`atTop ⊓ 𝓟 {n | P_μ[λ = n] ≠ 0}`; it is `NeBot` by `neBot_leafProb_ne_zero`).  Proved from `thm_max_ii`. -/
theorem thm_max_ii_tendsto {μ : PMF ℕ} (h : HypH μ) {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          (1 - ε) * (bigD μ n : ℝ) ≤ (maxDegree t : ℝ) ∧ (maxDegree t : ℝ) ≤ (1 + ε) * (bigD μ n : ℝ)))
      (atTop ⊓ 𝓟 {n : ℕ | leafProb μ n ≠ 0}) (𝓝 1) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun b hb => ?_⟩
  · obtain ⟨N, hN⟩ := thm_max_ii h hε (δ := (1 - a) / 2) (by linarith)
    rw [Filter.eventually_inf_principal]
    filter_upwards [eventually_ge_atTop N] with n hn hmem
    have := hN n hn hmem
    linarith
  · rw [Filter.eventually_inf_principal]
    refine Filter.Eventually.of_forall fun n hmem => ?_
    have : IsProbabilityMeasure ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]) :=
      cond_isProbabilityMeasure (bienayme_leafCountEvent_ne_zero hmem)
    exact lt_of_le_of_lt (measureReal_le_one) hb

/-! ## 10. Remark 7.3 (`eq:better`): the window for the uniform tree law -/

/-- The displayed law of Remark 7.3 (`μ(2), μ(3) > 0`: consecutive atoms) satisfies `hnl`: the law of `K - 1` given
`K ≥ 1` has the consecutive atoms `1` and `2`, so it is not lattice (the displayed law has full support from `2`).
Needed by the principles. -/
theorem displayedLaw_not_isLatticeLaw_etaLaw {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) :
    ¬ IsLatticeLaw (etaLaw μ) := by
  exact BGWLeaves.MaxDegree.Principles.displayedLaw_not_isLatticeLaw_etaLaw hμ

/-- **Remark 7.3, `eq:better`**: for the displayed law and every `c > 0`, with `b = 2 + √2`,
`P[log_b n - c log_b log_b n ≤ Δ(τ_n) ≤ log_b n + c log_b log_b n] → 1`, `τ_n ∼ P_μ[· | λ = n]`.
(The printed `P[...]` is `P_μ[· | λ = n]` of `τ_n`; the face-degree application to uniform dissections,
`[CK, Prop. 3.5]`, is a cited correspondence and is not stated.)

Assembled from `maxDegree_lower_principle` and `maxDegree_upper_principle` (WITH `hnl`, from
`displayedLaw_not_isLatticeLaw_etaLaw`) and the displayed limits `rem_uniformtree_tail_lower` /
`rem_uniformtree_tail_upper` of `BGWLeaves.Vervaat`.  The window needs no functional limit theorem: the
discrete tightness of the midpoint of the bridge (`bridge_midpoint_tight`, inside the principles) replaces
`eq:trucsuperutile`.  Note the shift of one: the upper principle gives `Δ ≤ q_n + 1`, so it is applied with
`c/2` and the extra `1` is absorbed since `log_b log_b n → ∞`. -/
theorem rem_uniformtree_window {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          Real.logb bConst n - c * Real.logb bConst (Real.logb bConst n) ≤ (maxDegree t : ℝ) ∧
          (maxDegree t : ℝ) ≤ Real.logb bConst n + c * Real.logb bConst (Real.logb bConst n))))
      atTop (𝓝 1) := by
  obtain ⟨hcrit, hne, hap, hfin⟩ := displayedLaw_hypotheses hμ
  have hnl := displayedLaw_not_isLatticeLaw_etaLaw hμ
  have hA := maxDegree_lower_principle hcrit hne hap hfin hnl
    (p := fun n : ℕ => Real.logb bConst n - c * Real.logb bConst (Real.logb bConst n))
    (rem_uniformtree_tail_lower hμ hc)
  have hB := maxDegree_upper_principle hcrit hne hap hfin hnl
    (q := fun n : ℕ => Real.logb bConst n + (c / 2) * Real.logb bConst (Real.logb bConst n))
    (rem_uniformtree_tail_upper hμ (half_pos hc))
  have hb1 : 1 < bConst := by
    unfold bConst
    have := Real.sqrt_nonneg 2
    linarith
  have hll : Tendsto (fun n : ℕ => Real.logb bConst (Real.logb bConst n)) atTop atTop :=
    (Real.tendsto_logb_atTop hb1).comp
      ((Real.tendsto_logb_atTop hb1).comp tendsto_natCast_atTop_atTop)
  have hev : ∀ᶠ n : ℕ in atTop, 2 / c ≤ Real.logb bConst (Real.logb bConst n) :=
    hll.eventually (eventually_ge_atTop _)
  have hlow : Tendsto (fun n : ℕ => 1 -
      ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real (finiteTreeEvent fun t =>
        (maxDegree t : ℝ) < Real.logb bConst n - c * Real.logb bConst (Real.logb bConst n) + 1) -
      ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real (finiteTreeEvent fun t =>
        Real.logb bConst n + (c / 2) * Real.logb bConst (Real.logb bConst n) + 1 < (maxDegree t : ℝ)))
      atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub hA |>.sub hB
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [hev, eventually_ge_atTop 1] with n hn1 hn2
    have hn : bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0 := displayedLaw_leafProb_ne_zero hμ hn2
    have h1 : 1 ≤ c / 2 * Real.logb bConst (Real.logb bConst n) := by
      have := mul_le_mul_of_nonneg_left hn1 (le_of_lt (half_pos hc))
      rwa [show c / 2 * (2 / c) = 1 by field_simp] at this
    refine cond_leafCount_window_ge hn _ _ _ (fun t _ => ?_)
    by_cases a : (maxDegree t : ℝ) <
        Real.logb bConst n - c * Real.logb bConst (Real.logb bConst n) + 1
    · exact Or.inl a
    · by_cases b : Real.logb bConst n + (c / 2) * Real.logb bConst (Real.logb bConst n) + 1 <
          (maxDegree t : ℝ)
      · exact Or.inr (Or.inl b)
      · refine Or.inr (Or.inr ⟨by linarith [not_lt.1 a], ?_⟩)
        have := not_lt.1 b
        nlinarith
  · filter_upwards [eventually_ge_atTop 1] with n hn2
    have hn : bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0 := displayedLaw_leafProb_ne_zero hμ hn2
    have : IsProbabilityMeasure ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]) :=
      cond_isProbabilityMeasure hn
    exact measureReal_le_one

/-! ## Not stated in this module

* **Theorem 7.1(i)** (`1 < θ < 2`, `μ₀^{1/θ} Δ(τ_n)/B_n → Δ̄(X^exc)` in law): a functional statement, in
  `BGWLeaves.MaxDegreeLimit`.  Its inputs: the convergence `eq:thmcvW32` (Theorem 6.1 `thm:cvW3` with Remark
  `rem:changement`), the continuity of the largest-jump functional `Δ̄` on the Skorokhod space `D([0,1], ℝ)` (J1),
  and `Δ̄(X^exc) > 0` almost surely (`θ < 2`, infinite activity).  Only the discrete part is here
  (`maximum_increments`, `maxDegree_eq_zero_iff`, `two_le_maxDegree_of_two_le_leaves`).
* **The case `θ = 2`, `σ² = ∞` of the Introduction, item (i)** (`μ₀^{1/θ} Δ(τ_n)/B_n → Δ̄(X) = 0`, `X` Brownian):
  not printed in Theorem 7.1(i), which treats `1 < θ < 2` only; also in `BGWLeaves.MaxDegreeLimit`.
* **The paper's route to `eq:trucsuperutile`** (convergence of the bridge `eq:cvBr`, which needs `lem:CVf2(ii)` and
  `prop:bridge(ii)`, cited Chaumont and Bertoin): bypassed, replaced by the discrete `bridge_midpoint_tight`.
* The finite-variance consequence of the Introduction, item (ii), `Δ(τ_n)/D(n) → 1` in probability, is
  `thm_max_ii_tendsto` (the closed and the open windows are immaterial since `ε` is arbitrary).
-/

end BGWLeaves
