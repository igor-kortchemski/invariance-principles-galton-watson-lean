module

public import BGWLeaves.Vervaat.Defs
import BGWLeaves.Vervaat.Proof

/-!
# Vervaat transform, time reversal, uniform trees

Source: arXiv:1110.2163v4 (line numbers refer to its LaTeX source): Lemma 6.2(i) (`lem:CVf2`, line 2004:
the concentration part; the functional limit (ii) is in `BGWLeaves.ClassicalLimits`), Definition 6.3 (`def:vervaat`), Lemma 6.4 (`lem:cool`),
Proposition 6.5 (`prop:vervaatdiscrete`, lines 2073-2146), Proposition 6.8 (`prop:timereversal`,
lines 2147-2160) and Remark 7.3 (`rem:uniformtree`, lines 2459-2486).

The proofs are in the modules `BGWLeaves.Vervaat.*` (imported through `BGWLeaves.Vervaat.Proof`).
Definitions and bridges are in `BGWLeaves.Vervaat.Defs`.  The declarations `prop_vervaatdiscrete`,
`isProbabilityMeasure_cond_timeReversalEvent` and `prop_timereversal` are proved here from other
statements of this file.

Layout.
* 6.3 and the Cyclic Lemma bridge: `vervaatIdx_mem`, `mem_SBar_iff`, `vervaat_mem_SBar`,
  `vervaatIdx_unique`, `walkWord_atom`, `sum_walkWord` (module `Cyclic`).
* 6.4: `lem_cool_i_joint` (working form), `lem_cool_i`, `lem_cool_ii`, `vervaat_prob_eq` (module
  `Cyclic`).
* 6.5: helpers `vervaatAtMark_eq`, `vervaatAtMark_eq_empty`, `treeWordLeaves_prob`,
  `bridgeAtMark_eq_iUnion`, `leafCountEvent_eq_iUnion`, `measurableSet_*`, then
  `prop_vervaatdiscrete_joint`, `prop_vervaatdiscrete_total`, `prop_vervaatdiscrete` (module
  `Discrete`).
* 6.8: `measurable_*`, `timeReversal_atom`, `timeReversal_map`, `prop_timereversal` (module
  `TimeReversal`).
* 6.2(i): `ae_exists_markTime`, `exists_isMarkTime_iff`, `IsMarkTime.unique`, `lem_CVf2_i` (module
  `MarkTime`).
* 7.3: the displayed law, its constants and `rem_uniformtree_iff`, the three displayed limits (module
  `UniformTree`).
* In `BGWLeaves.MaxDegree`, not here: `maxDegree_lower_principle`, `maxDegree_upper_principle`,
  `rem_uniformtree_window`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-- The law of the walk `W_n = ∑_{i<n} (ω i - 1)` with step law `μ(k)` for the step `k - 1`
(`Measure.infinitePi`, as in `stoppedWord_atom`).  Notation only. -/
local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

/-! ## 6.3 The Vervaat transform: bridges to the Cyclic Lemma -/

/-- `1 ≤ i_*(x) ≤ k` for `k ≥ 1`. -/
theorem vervaatIdx_mem {x : List ℤ} (hx : x ≠ []) : 1 ≤ vervaatIdx x ∧ vervaatIdx x ≤ x.length := by
  exact BGWLeaves.Vervaat.Cyclic.vervaatIdx_mem hx

/-- `S̄^k(n)` is the set of BGW tree excursions (`BGW.IsTreeExcursion`: entries `≥ -1`, sum `-1`, all
proper prefix sums `≥ 0`) of length `k` with `n` entries `-1`; this is the bridge to `BGW.Tree.CycleLemma`
(`exists_unique_rotate_isTreeExcursion`, `exists_first_min`) used by the two statements below. -/
theorem mem_SBar_iff {x : List ℤ} {k n : ℕ} :
    x ∈ SBar k n ↔ x.length = k ∧ IsTreeExcursion x ∧ x.count (-1) = n := by
  exact BGWLeaves.Vervaat.Cyclic.mem_SBar_iff

/-- **Cyclic Lemma, as used in the proof of Lemma 6.4**: for a word `x` of entries `≥ -1` and sum `-1`,
`V(x) ∈ S̄^k(n)` with `n` the number of entries `-1`. -/
theorem vervaat_mem_SBar {x : List ℤ} (hx : x ≠ []) (hge : ∀ a ∈ x, -1 ≤ a) (hsum : x.sum = -1) :
    vervaat x ∈ SBar x.length (x.count (-1)) := by
  exact BGWLeaves.Vervaat.Cyclic.vervaat_mem_SBar hx hge hsum

/-- **Cyclic Lemma (uniqueness), as used in the proof of Lemma 6.4**: if `x` has entries `≥ -1`, sum `-1`
and some shift `x^{(i)}`, `1 ≤ i ≤ k`, lies in `S̄^k(·)`, then `i = i_*(x)`. -/
theorem vervaatIdx_unique {x : List ℤ} (hge : ∀ a ∈ x, -1 ≤ a) (hsum : x.sum = -1) {i n : ℕ}
    (hi : 1 ≤ i ∧ i ≤ x.length) (hS : cyclicShift x i ∈ SBar x.length n) : vervaatIdx x = i := by
  exact BGWLeaves.Vervaat.Cyclic.vervaatIdx_unique hge hsum hi hS

/-- The atoms of the walk word: `P[Z^k = y] = ∏ μ(y_j + 1)` for `y` of length `k` with entries
`≥ -1`, and `0` otherwise.  Permuting `y` does not change the probability (exchangeability, used for
cyclic shifts in 6.4 and for the reversal in 6.8; no `infinitePi_map_piCongrLeft` is needed). -/
theorem walkWord_atom (μ : Measure ℕ) [IsProbabilityMeasure μ] (y : List ℤ) :
    𝐏w[μ] {ω | walkWord ω y.length = y} =
      if ∀ a ∈ y, -1 ≤ a then (y.map fun a => μ {(a + 1).toNat}).prod else 0 := by
  exact BGWLeaves.Vervaat.Cyclic.walkWord_atom μ y

/-- The word determines the partial sums: `W_k = ∑ Z^k`. -/
theorem sum_walkWord (ω : ℕ → ℕ) (k : ℕ) : (walkWord ω k).sum = walkSum ω k := by
  exact BGWLeaves.Vervaat.Cyclic.sum_walkWord ω k

/-! ## 6.4 Lemma `lem:cool` -/

/-- **Lemma 6.4(i), joint (null-safe) form.**  For `k ≥ 1`, `1 ≤ i ≤ k` and every word `x`,
`P[i_*(Z^k) = i, V(Z^k) = x, W_k = -1] = (1/k) P[V(Z^k) = x, W_k = -1]`.
No positivity hypothesis; both sides vanish if `P[W_k = -1] = 0`.  This is the content of
"conditionally on `W_k = -1`, `i_*(Z^k)` is uniform on `{1..k}` and independent of `V(Z^k)`". -/
theorem lem_cool_i_joint (μ : Measure ℕ) [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k) {i : ℕ}
    (hi : 1 ≤ i ∧ i ≤ k) (x : List ℤ) :
    𝐏w[μ] {ω | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} =
      (1 / (k : ℝ≥0∞)) * 𝐏w[μ] {ω | vervaat (walkWord ω k) = x ∧ walkSum ω k = -1} := by
  exact BGWLeaves.Vervaat.Cyclic.lem_cool_i_joint μ hk hi x

/-- **Lemma 6.4(i)** (`lem:cool`), as printed: conditionally on `{W_k = -1}`, `i_*(Z^k)` is uniformly
distributed on `{1,…,k}` (first conjunct) and independent of `V(Z^k)` (second conjunct, as the
product formula on atoms).  Added hypothesis `hpos : P[W_k = -1] ≠ 0` (implicit in the paper; Lean
conditions a null event to the zero measure, for which "uniform" is false).  The printed `k ≥ n` is
not needed (`n` does not occur in (i)).  Atoms: the pair `(i_*, V)` lives in the countable space
`ℕ × List ℤ`, which has no measurable space instance. -/
theorem lem_cool_i (μ : Measure ℕ) [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    (hpos : 𝐏w[μ] {ω | walkSum ω k = -1} ≠ 0) :
    (∀ i : ℕ, ((𝐏w[μ])[|{ω | walkSum ω k = -1}]) {ω | vervaatIdx (walkWord ω k) = i} =
        if 1 ≤ i ∧ i ≤ k then 1 / (k : ℝ≥0∞) else 0) ∧
      (∀ (i : ℕ) (x : List ℤ),
        ((𝐏w[μ])[|{ω | walkSum ω k = -1}])
            {ω | vervaatIdx (walkWord ω k) = i ∧ vervaat (walkWord ω k) = x} =
          ((𝐏w[μ])[|{ω | walkSum ω k = -1}]) {ω | vervaatIdx (walkWord ω k) = i} *
            ((𝐏w[μ])[|{ω | walkSum ω k = -1}]) {ω | vervaat (walkWord ω k) = x}) := by
  exact BGWLeaves.Vervaat.Cyclic.lem_cool_i μ hk hpos

/-- **Lemma 6.4(ii)** (`lem:cool`, `eq:v1`): for `x ∈ S̄^k(n)`,
`P[V(Z^k) = x, Z^k_k = -1] = (n/k) P[V(Z^k) = x]`.  `Z^k_k = W_k - W_{k-1} = ω(k-1) - 1`, so the
event `Z^k_k = -1` is `ω (k-1) = 0`.  The printed `k ≥ n` positive integers is kept
(`hn`, `hkn`; `hkn` is implied by `x ∈ S̄^k(n)`, and `k ≥ 1`). -/
theorem lem_cool_ii (μ : Measure ℕ) [IsProbabilityMeasure μ] {k n : ℕ} (hn : 1 ≤ n) (hkn : n ≤ k)
    {x : List ℤ} (hx : x ∈ SBar k n) :
    𝐏w[μ] {ω | vervaat (walkWord ω k) = x ∧ ω (k - 1) = 0} =
      ((n : ℝ≥0∞) / k) * 𝐏w[μ] {ω | vervaat (walkWord ω k) = x} := by
  exact BGWLeaves.Vervaat.Cyclic.lem_cool_ii μ hn hkn hx

/-! ## 6.5 Proposition `prop:vervaatdiscrete` -/

/-- Helper (the "last step is a mark" and "`Λ(k) = n`" bookkeeping of the proof of 6.5): for
`x ∈ S̄^k(n)` and `n ≥ 1`, `{T_n = k, W_k = -1, V(Z^k) = x} = {V(Z^k) = x, Z^k_k = -1}`; and
`vervaatAtMark n x` is this event with `k = x.length`. -/
theorem vervaatAtMark_eq {n k : ℕ} (hn : 1 ≤ n) {x : List ℤ} (hx : x ∈ SBar k n) :
    vervaatAtMark n x = {ω | vervaat (walkWord ω k) = x ∧ ω (k - 1) = 0} := by
  exact BGWLeaves.Vervaat.Discrete.vervaatAtMark_eq hn hx

/-- Helper: if `x ∉ S̄^{|x|}(n)` the event `{V(Z) = x, W_{T_n} = -1}` is empty. -/
theorem vervaatAtMark_eq_empty {n : ℕ} {x : List ℤ} (hx : x ∉ SBar x.length n) :
    vervaatAtMark n x = ∅ := by
  exact BGWLeaves.Vervaat.Discrete.vervaatAtMark_eq_empty hx

open Classical in
/-- Helper (Proposition 1.4 for one tree, on atoms): the finite trees with Łukasiewicz word `x` and `n`
leaves have probability `P[Z^k = x]` if `x ∈ S̄^k(n)` and `0` otherwise. -/
theorem treeWordLeaves_prob (μ : Measure ℕ) [IsProbabilityMeasure μ] (n : ℕ) (x : List ℤ) :
    bienaymeLaw μ (treeWordLeaves n x) =
      if x ∈ SBar x.length n then 𝐏w[μ] {ω | walkWord ω x.length = x} else 0 := by
  exact BGWLeaves.Vervaat.Discrete.treeWordLeaves_prob μ n x

/-- Helper (sum over `x`): `{W_{T_n} = -1}` is the disjoint union of the events `vervaatAtMark n x`,
`x ∈ List ℤ` (countable), and `leafCountEvent n` that of the `treeWordLeaves n x`. -/
theorem bridgeAtMark_eq_iUnion (n : ℕ) : bridgeAtMark n = ⋃ x : List ℤ, vervaatAtMark n x := by
  exact BGWLeaves.Vervaat.Discrete.bridgeAtMark_eq_iUnion n

theorem leafCountEvent_eq_iUnion (n : ℕ) :
    leafCountEvent n = ⋃ x : List ℤ, treeWordLeaves n x := by
  exact BGWLeaves.Vervaat.Discrete.leafCountEvent_eq_iUnion n

/-- Measurability of the conditioning events (needed to unfold `cond`; countable unions of
the atoms `{walkWord ω k = y}`, resp. of the finite-tree atoms). -/
theorem measurableSet_bridgeAtMark (n : ℕ) : MeasurableSet (bridgeAtMark n) := by
  exact BGWLeaves.Vervaat.Discrete.measurableSet_bridgeAtMark n

theorem measurableSet_leafCountEvent (n : ℕ) : MeasurableSet (leafCountEvent n) := by
  exact BGWLeaves.Vervaat.Discrete.measurableSet_leafCountEvent n

/-- Helper: the key factor `P[V(Z^k) = x] = k P[Z^k = x]` for `x ∈ S̄^k(n)` (Cyclic Lemma and
exchangeability, equation `eq:V` of the proof of 6.4). -/
theorem vervaat_prob_eq (μ : Measure ℕ) [IsProbabilityMeasure μ] {k n : ℕ} {x : List ℤ}
    (hx : x ∈ SBar k n) :
    𝐏w[μ] {ω | vervaat (walkWord ω k) = x} = (k : ℝ≥0∞) * 𝐏w[μ] {ω | walkWord ω k = x} := by
  exact BGWLeaves.Vervaat.Cyclic.vervaat_prob_eq μ hx

/-- **Proposition 6.5, joint atoms (null-safe)**: `P[W_{T_n} = -1, V(Z) = x] = n P_μ[word(τ) = x, λ(τ) = n]`
for every word `x`, `n ≥ 1` (`Z = (W_1, …, W_{T_n} - W_{T_n-1})`).  Not printed; it is the content of the
proof (`eq:v1` and `eq:V`, summed over `k`), and contains the identity `P[W_{T_n} = -1] = n P[Z ∈ S̄(n)]`
that the paper obtains by summing. -/
theorem prop_vervaatdiscrete_joint (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n)
    (x : List ℤ) :
    𝐏w[μ] (vervaatAtMark n x) = (n : ℝ≥0∞) * bienaymeLaw μ (treeWordLeaves n x) := by
  exact BGWLeaves.Vervaat.Discrete.prop_vervaatdiscrete_joint μ hn x

/-- Total mass: `P[W_{T_n} = -1] = n P_μ[λ(τ) = n]` (sum of `prop_vervaatdiscrete_joint` over `x`). -/
theorem prop_vervaatdiscrete_total (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) :
    𝐏w[μ] (bridgeAtMark n) = (n : ℝ≥0∞) * bienaymeLaw μ (leafCountEvent n) := by
  exact BGWLeaves.Vervaat.Discrete.prop_vervaatdiscrete_total μ hn

/-- **Proposition 6.5 (`prop:vervaatdiscrete`)**, as printed, on atoms: for `n ≥ 1` and every word `x`,
`P[V(W_1, …, W_{T_n} - W_{T_n - 1}) = x | W_{T_n} = -1] = P_μ[(W_1(τ), …, W_ζ(τ) - W_{ζ-1}(τ)) = x | λ(τ) = n]`.
Both conditional measures are the zero measure iff `P_μ[λ = n] = 0` (by the total mass identity).
Atoms on the countable space `List ℤ` determine the law (the length of the word is not deterministic,
there is no natural finite-dimensional space and `List ℤ` has no measurable space instance). -/
theorem prop_vervaatdiscrete (μ : Measure ℕ) [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n)
    (x : List ℤ) :
    ((𝐏w[μ])[|bridgeAtMark n]) (vervaatAtMark n x) =
      ((bienaymeLaw μ)[|leafCountEvent n]) (treeWordLeaves n x) := by
  have hA : vervaatAtMark n x ⊆ bridgeAtMark n := fun ω ⟨k, hk, hs, _⟩ => ⟨k, hk, hs⟩
  have hB : treeWordLeaves n x ⊆ leafCountEvent n := by
    rintro T ⟨t, h1, h2⟩
    exact ⟨t, h1, h2.2⟩
  rw [cond_apply (measurableSet_bridgeAtMark n), cond_apply (measurableSet_leafCountEvent n),
    Set.inter_eq_right.2 hA, Set.inter_eq_right.2 hB, prop_vervaatdiscrete_joint μ hn x,
    prop_vervaatdiscrete_total μ hn]
  have hn0 : (n : ℝ≥0∞) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hnT : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hinv : (n : ℝ≥0∞)⁻¹ * n = 1 := ENNReal.inv_mul_cancel hn0 hnT
  rw [ENNReal.mul_inv (Or.inl hn0) (Or.inl hnT)]
  calc (n : ℝ≥0∞)⁻¹ * (bienaymeLaw μ (leafCountEvent n))⁻¹ * (n * bienaymeLaw μ (treeWordLeaves n x))
      = ((n : ℝ≥0∞)⁻¹ * n) * ((bienaymeLaw μ (leafCountEvent n))⁻¹ *
          bienaymeLaw μ (treeWordLeaves n x)) := by ring
    _ = _ := by rw [hinv, one_mul]

/-! ## 6.8 Proposition `prop:timereversal` -/

theorem measurable_walkPath (m : ℕ) : Measurable (walkPath m) := by
  exact BGWLeaves.Vervaat.TimeReversal.measurable_walkPath m

theorem measurable_reversedPath (m : ℕ) : Measurable (reversedPath m) := by
  exact BGWLeaves.Vervaat.TimeReversal.measurable_reversedPath m

theorem measurableSet_timeReversalEvent (m n : ℕ) : MeasurableSet (timeReversalEvent m n) := by
  exact BGWLeaves.Vervaat.TimeReversal.measurableSet_timeReversalEvent m n

/-- Helper (exchangeability on atoms): the reversal of the increments preserves the law of the
word, hence `P[W path = p, E] = P[Ŵ path = p, E]` for every path `p`. -/
theorem timeReversal_atom (μ : Measure ℕ) [IsProbabilityMeasure μ] (m n : ℕ) (p : Fin (m + 1) → ℤ) :
    𝐏w[μ] ({ω | walkPath m ω = p} ∩ timeReversalEvent m n) =
      𝐏w[μ] ({ω | reversedPath m ω = p} ∩ timeReversalEvent m n) := by
  exact BGWLeaves.Vervaat.TimeReversal.timeReversal_atom μ m n p

/-- **Proposition 6.8, general form (no hypotheses on `m`, `n`, `μ`)**: the law of `(W_0, …, W_m)` under
`P[· | W_m = 0, Λ(m) = n]` is the law of `(Ŵ_0, …, Ŵ_m)` under the same measure, as an equality of
`Measure.map` on the countable space `Fin (m+1) → ℤ`.  The statement is null-safe: if `P[W_m = 0, Λ(m) = n] = 0`
both sides are the zero measure. -/
theorem timeReversal_map (μ : Measure ℕ) [IsProbabilityMeasure μ] (m n : ℕ) :
    Measure.map (walkPath m) ((𝐏w[μ])[|timeReversalEvent m n]) =
      Measure.map (reversedPath m) ((𝐏w[μ])[|timeReversalEvent m n]) := by
  exact BGWLeaves.Vervaat.TimeReversal.timeReversal_map μ m n

/-- Non-vacuity: under `hpos` the conditional measure is a probability measure. -/
theorem isProbabilityMeasure_cond_timeReversalEvent (μ : Measure ℕ) [IsProbabilityMeasure μ] {m n : ℕ}
    (hpos : 𝐏w[μ] (timeReversalEvent m n) ≠ 0) :
    IsProbabilityMeasure ((𝐏w[μ])[|timeReversalEvent m n]) :=
  cond_isProbabilityMeasure hpos

set_option linter.unusedVariables false in
/-- **Proposition 6.8 (`prop:timereversal`)**, as printed (hypotheses `m ≥ n ≥ 1` and
`P[W_m = 0, Λ(m) = n] > 0` kept, all three unused: they are implied by / irrelevant to the general form). -/
theorem prop_timereversal (μ : Measure ℕ) [IsProbabilityMeasure μ] {m n : ℕ} (hn : 1 ≤ n)
    (hmn : n ≤ m) (hpos : 𝐏w[μ] (timeReversalEvent m n) ≠ 0) :
    Measure.map (walkPath m) ((𝐏w[μ])[|timeReversalEvent m n]) =
      Measure.map (reversedPath m) ((𝐏w[μ])[|timeReversalEvent m n]) :=
  timeReversal_map μ m n

/-! ## 6.2 Lemma `lem:CVf2`, part (i) ONLY (part (ii), the functional limit, is `lem_CVf2_ii` in
`BGWLeaves.ClassicalLimits`) -/

/-- Helper: `T_n < ∞` almost surely when `μ(0) > 0` (so the event of `lem_CVf2_i` is the printed one
up to a null set; as stated it already counts `T_n = ∞` as a deviation). -/
theorem ae_exists_markTime (μ : PMF ℕ) (h0 : μ 0 ≠ 0) :
    ∀ᵐ ω ∂(Measure.infinitePi fun _ : ℕ => μ.toMeasure), ∀ n : ℕ, ∃ k, IsMarkTime n ω k := by
  exact BGWLeaves.Vervaat.MarkTime.ae_exists_markTime μ h0

/-- `T_n` is unique when it exists, and exists iff `Λ(k) = n` for some `k`. -/
theorem exists_isMarkTime_iff (n : ℕ) (ω : ℕ → ℕ) :
    (∃ k, IsMarkTime n ω k) ↔ ∃ k, walkLeafCount ω k = n := by
  exact BGWLeaves.Vervaat.MarkTime.exists_isMarkTime_iff n ω

theorem IsMarkTime.unique {n : ℕ} {ω : ℕ → ℕ} {k k' : ℕ} (h : IsMarkTime n ω k)
    (h' : IsMarkTime n ω k') : k = k' := by
  exact BGWLeaves.Vervaat.MarkTime.IsMarkTime.unique h h'

/-- **Lemma 6.2(i) (`lem:CVf2`)**: `P[|T_n/n - 1/μ₀| > 1/n^{1/4}] = oe_{1/2}(n)` for the iid walk, `T_n = inf{k ; Λ(k) = n}`.
`T_n = ∞` counts as a deviation (probability `0`, `ae_exists_markTime`).  Only `0 < μ₀ < 1` is used (as in
`lem_GdesDev_walk`), instead of `(H_θ)`; this implies the printed statement.  `IsOe` is the
definition of `BGWLeaves.LeafConcentration.Defs` (`∃ C c > 0, ∀ n, x_n ≤ C exp(-c n^{1/2})`). -/
theorem lem_CVf2_i (μ : PMF ℕ) (h0 : μ 0 ≠ 0) (h1 : μ 0 ≠ 1) :
    IsOe (1 / 2) fun n : ℕ =>
      ((Measure.infinitePi fun _ : ℕ => μ.toMeasure).real
        {ω | (¬ ∃ k, IsMarkTime n ω k) ∨
          ∃ k, IsMarkTime n ω k ∧
            1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / (μ 0).toReal|}) := by
  exact BGWLeaves.Vervaat.MarkTime.lem_CVf2_i μ h0 h1

/-! ## 7.3 Remark `rem:uniformtree` -/

/-- The displayed weights form a probability measure (`μ` "is a probability measure"). -/
theorem exists_displayedLaw : ∃ μ : PMF ℕ, IsDisplayedLaw μ := by
  exact BGWLeaves.Vervaat.UniformTree.exists_displayedLaw

/-- The displayed law is critical ("one verifies that `μ` is a critical probability measure"):
`∑ i μ(i) = (2-√2) + ∑_{i≥2} q^{i-1} = 1`, `∑ i μ(i) = 1/(1-q)² - 1 = 1`, `q = (2-√2)/2`, `1 - q = √2/2`. -/
theorem displayedLaw_critical {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) : IsCritical μ := by
  exact BGWLeaves.Vervaat.UniformTree.displayedLaw_critical hμ

/-- `μ(2) = (2-√2)/2 = 1/(2+√2) = 1/b`. -/
theorem displayedLaw_two {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) :
    (μ 2).toReal = 1 / bConst := by
  exact BGWLeaves.Vervaat.UniformTree.displayedLaw_two hμ

/-- The displayed law satisfies the standing hypotheses of Section 7: critical, `μ 1 ≠ 1`, aperiodic,
finite variance (hence `(H_2)`, via `StableDomain`). -/
theorem displayedLaw_hypotheses {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) :
    IsCritical μ ∧ μ 1 ≠ 1 ∧ Aperiodic μ ∧
      Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) := by
  exact BGWLeaves.Vervaat.UniformTree.displayedLaw_hypotheses hμ


theorem uniformTrees_nonempty {n : ℕ} (hn : 1 ≤ n) : (uniformTrees n).Nonempty := by
  exact BGWLeaves.Vervaat.UniformTree.uniformTrees_nonempty hn


/-- `P_μ[λ = n] > 0` for every `n ≥ 1` under the displayed law (so `τ_n` is defined for all `n ≥ 1`). -/
theorem displayedLaw_leafProb_ne_zero {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {n : ℕ} (hn : 1 ≤ n) :
    bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0 := by
  exact BGWLeaves.Vervaat.UniformTree.displayedLaw_leafProb_ne_zero hμ hn

/-- Weights are constant: a finite tree with `n` leaves and no unary vertex has weight
`μ(0)^n q^{n-1}` (`∑_{non-leaf} (k_u - 1) = n - 1`), `q = (2-√2)/2`; trees with a unary vertex have weight `0`. -/
theorem displayedLaw_atom {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) (t : PlaneTree) :
    bienaymeLaw μ.toMeasure {t.toLocallyFinite} =
      if 1 ∉ t.degrees then
        ENNReal.ofReal ((2 - Real.sqrt 2) ^ (t.degreeCount 0) *
          ((2 - Real.sqrt 2) / 2) ^ (t.degreeCount 0 - 1))
      else 0 := by
  exact BGWLeaves.Vervaat.UniformTree.displayedLaw_atom hμ t

/-- **Remark 7.3, first claim and characterization** ("`μ` is the unique critical probability measure
such that `τ_n` is uniformly distributed over the set of all rooted plane trees with `n` leaves such
that no vertex has exactly one child"): for a critical `μ`, `μ` is the displayed law iff `τ_n` is uniform
over `uniformTrees n` for every `n ≥ 1` with `P_μ[λ = n] > 0`. The hypothesis `hne : μ 1 ≠ 1` excludes
`δ₁`, which is critical and satisfies the uniformity condition vacuously (the tree is the infinite path,
`P[λ = n] = 0` for all `n ≥ 1`); the printed remark implicitly assumes it. -/
theorem rem_uniformtree_iff {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    IsDisplayedLaw μ ↔ IsUniformConditioned μ := by
  exact BGWLeaves.Vervaat.UniformTree.rem_uniformtree_iff hc hne

/-- Explicit tail of the step: `P[W_1 ≥ j] = √2 b^{-j}` for integers `j ≥ 1`
(`∑_{i ≥ j+1} q^{i-1} = q^j/(1-q)`, `1/(1-q) = √2`, `q = 1/b`). -/
theorem displayedLaw_stepTail {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {j : ℕ} (hj : 1 ≤ j) :
    stepTail μ j = Real.sqrt 2 * (1 / bConst) ^ j := by
  exact BGWLeaves.Vervaat.UniformTree.displayedLaw_stepTail hμ hj

/-- **Remark 7.3, first displayed limit** (printed exponent `n/4μ₀`): for every `c > 0`,
`(1 - P[W_1 ≥ log_b n - c log_b log_b n])^{n/(4μ₀)} → 0`, `μ₀ = 2 - √2`, `b = 2 + √2`. -/
theorem rem_uniformtree_tail_lower {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ (Real.logb bConst n - c * Real.logb bConst (Real.logb bConst n))) ^
        ((n : ℝ) / (4 * (μ 0).toReal))) atTop (𝓝 0) := by
  exact BGWLeaves.Vervaat.UniformTree.rem_uniformtree_tail_lower hμ hc

/-- **Remark 7.3, second displayed limit**, with the exponent `n/μ₀` that the upper bound of the proof of
Theorem 7.1 uses (`1 - (1 - P[W_1 > q_n])^{⌊n/μ₀⌋}`): for every `c > 0`,
`(1 - P[W_1 ≥ log_b n + c log_b log_b n])^{n/μ₀} → 1`. -/
theorem rem_uniformtree_tail_upper {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ (Real.logb bConst n + c * Real.logb bConst (Real.logb bConst n))) ^
        ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 1) := by
  exact BGWLeaves.Vervaat.UniformTree.rem_uniformtree_tail_upper hμ hc

/-- The second displayed limit with the PRINTED exponent `n/(4μ₀)` (weaker than
`rem_uniformtree_tail_upper`: `x^{n/μ₀} ≤ x^{n/4μ₀} ≤ 1` for `0 ≤ x ≤ 1`). -/
theorem rem_uniformtree_tail_upper_printed {μ : PMF ℕ} (hμ : IsDisplayedLaw μ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun n : ℕ =>
      (1 - stepTail μ (Real.logb bConst n + c * Real.logb bConst (Real.logb bConst n))) ^
        ((n : ℝ) / (4 * (μ 0).toReal))) atTop (𝓝 1) := by
  exact BGWLeaves.Vervaat.UniformTree.rem_uniformtree_tail_upper_printed hμ hc

end BGWLeaves
