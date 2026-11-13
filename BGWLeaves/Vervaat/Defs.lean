module

public import BGWLeaves.Passage.Defs
public import BGWLeaves.ForestLaw.Defs
public import BGWLeaves.LeafConcentration.Defs
public import BGWLeaves.LeafMass.Defs
public import BGWLeaves.StableAnalysis.Defs
public import BGW.LocallyFinite.Atoms
public import BGW.Tree.Finite
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Tactic.IntervalCases
public import Mathlib.Probability.ConditionalProbability
public import Mathlib.Probability.Distributions.Uniform

/-!
# Vervaat transform, mark times, time reversal, uniform trees (M5): definitions and proved bridges

Source: arXiv:1110.2163v4, `largetrees_final.tex`, Section 6.2(i) (`lem:CVf2`, line 2004), 6.3
(`def:vervaat`), 6.4 (`lem:cool`), 6.5 (`prop:vervaatdiscrete`), 6.8 (`prop:timereversal`, line 2147)
and 7.3 (`rem:uniformtree`, lines 2459-2486).

This file contains every definition of milestone M5 and the proved elementary bridges.  It contains no
proof holes.  The statements still to be proved are in `BGWLeaves.Vervaat`; their proofs are supplied by
the provider modules `BGWLeaves.Vervaat.*` (imported through `BGWLeaves.Vervaat.Proof`).

Conventions.
* Walk laws: `Measure.infinitePi (fun _ : ℕ => μ)` on `ℕ → ℕ`, the step at time `i` being `ω i - 1`
  (as in M2b and M4a); `Λ` is `walkLeafCount` of `BGWLeaves.LeafConcentration.Defs`.
* Words are `List ℤ`; the countable discrete spaces `List ℤ` and `Fin (m+1) → ℤ` are handled by atoms
  (there is no measurable-space instance on `List ℤ`).
* Conditioning is `ProbabilityTheory.cond`: conditioning on a null event gives the zero measure.
* Not in this package (see the README): the maximum-degree principles and the window `eq:better` of
  Remark 7.3, which depend on tranche-2 input.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## 0. Walk words, marks, the Vervaat transform (NEW definitions) -/

/-- `W_k = ∑_{i<k} (ω i - 1)`, the walk of Section 1.3 (same expression as `IsFirstHit`). -/
def walkSum (ω : ℕ → ℕ) (k : ℕ) : ℤ := ∑ i ∈ Finset.range k, ((ω i : ℤ) - 1)

/-- `Z^k = (W_1, W_2 - W_1, …, W_k - W_{k-1})`, the word of the first `k` steps, as a list
`[ω 0 - 1, …, ω (k-1) - 1]` (the paper's `x_j` is `Z^k.get (j-1)`). -/
def walkWord (ω : ℕ → ℕ) (k : ℕ) : List ℤ := (List.range k).map fun i => (ω i : ℤ) - 1

/-- The `i`-th cyclic shift `x^{(i)}` of Section 1.3: `x^{(i)}_k = x_{i+k mod p}` for `1 ≤ k ≤ p`
(`p = x.length`), in 0-based form `y[m] = x[(i+m) mod p]`.  The junk value `[]` for `p = 0`. -/
def cyclicShift (x : List ℤ) (i : ℕ) : List ℤ :=
  List.ofFn fun m : Fin x.length => x.getD ((i + m) % x.length) 0

/-- **Definition 6.3 (`def:vervaat`)**, the index `i_*(x) = inf {j ≥ 1 ; w_j = min_{1 ≤ i ≤ k} w_i}`,
`w_j = x_1 + … + x_j` (`(x.take j).sum`).  The set is the set of `1 ≤ j ≤ k` with `w_j ≤ w_i` for all
`1 ≤ i ≤ k` (equivalently `w_j = min`).  It is nonempty for `k ≥ 1`; for `x = []` the junk value is `0`. -/
noncomputable def vervaatIdx (x : List ℤ) : ℕ :=
  sInf {j : ℕ | 1 ≤ j ∧ j ≤ x.length ∧
    ∀ i : ℕ, 1 ≤ i → i ≤ x.length → (x.take j).sum ≤ (x.take i).sum}

/-- **Definition 6.3 (`def:vervaat`)**: the Vervaat transform `V(x) = x^{(i_*(x))}`. -/
noncomputable def vervaat (x : List ℤ) : List ℤ := cyclicShift x (vervaatIdx x)

/-- `S̄^k(n)` of Section 6.3: words of length `k` with entries in `{-1,0,1,…}`, sum `-1`, exactly
`n` entries `-1`, and partial sums `> -1` for `1 ≤ m ≤ k-1` (the printed `S^k(n)` has the exponent
`k` missing on the alphabet, a typo).  `S̄(n) = ⋃_{k ≥ n} S̄^k(n)` is `⋃ k, SBar k n`. -/
def SBar (k n : ℕ) : Set (List ℤ) :=
  {x | x.length = k ∧ (∀ a ∈ x, -1 ≤ a) ∧ x.sum = -1 ∧ x.count (-1) = n ∧
    ∀ m : ℕ, 1 ≤ m → m < k → -1 < (x.take m).sum}

/-- `T_n = k`: `k` is the first time at which `Λ(k) = n` (`eq:notations`,
`T_u = inf {k ≥ 0 ; Λ(k) = ⌊u⌋}`, here for integer `u = n`).  `Λ` is `walkLeafCount` (M4a). -/
def IsMarkTime (n : ℕ) (ω : ℕ → ℕ) (k : ℕ) : Prop :=
  walkLeafCount ω k = n ∧ ∀ q < k, walkLeafCount ω q < n

/-- The event `{W_{T_n} = -1}` (`T_n < ∞` is part of it: on `{T_n = ∞}` the value `W_{T_n}` is
undefined and the event does not hold). -/
def bridgeAtMark (n : ℕ) : Set (ℕ → ℕ) :=
  {ω | ∃ k, IsMarkTime n ω k ∧ walkSum ω k = -1}

/-- The event `{W_{T_n} = -1, V(W_1, W_2 - W_1, …, W_{T_n} - W_{T_n - 1}) = x}`. -/
def vervaatAtMark (n : ℕ) (x : List ℤ) : Set (ℕ → ℕ) :=
  {ω | ∃ k, IsMarkTime n ω k ∧ walkSum ω k = -1 ∧ vervaat (walkWord ω k) = x}

/-- Tree side: the finite tree has `n` leaves and Łukasiewicz increment word
`(W_1(τ), W_2(τ) - W_1(τ), …, W_ζ(τ) - W_{ζ-1}(τ)) = x` (`PlaneTree.increments`, as in M4a). -/
def treeWordLeaves (n : ℕ) (x : List ℤ) : Set LocallyFinite.Tree :=
  finiteTreeEvent fun t => t.increments = x ∧ t.degreeCount 0 = n

/-! ### Elementary lemmas on the definitions -/

/-- The paper's cyclic shift is Mathlib's `List.rotate`. -/
theorem cyclicShift_eq_rotate (x : List ℤ) (i : ℕ) : cyclicShift x i = x.rotate i := by
  apply List.ext_getElem
  · simp [cyclicShift]
  · intro m h1 h2
    have hl : m < x.length := by simpa [cyclicShift] using h1
    have hp : (i + m) % x.length < x.length := Nat.mod_lt _ (by omega)
    simp [cyclicShift, List.getElem_rotate, List.getD_eq_getElem?_getD, Nat.add_comm,
      List.getElem?_eq_getElem hp]

theorem length_vervaat (x : List ℤ) : (vervaat x).length = x.length := by
  simp [vervaat, cyclicShift_eq_rotate]

theorem sum_vervaat (x : List ℤ) : (vervaat x).sum = x.sum := by
  rw [vervaat, cyclicShift_eq_rotate]; exact (List.rotate_perm _ _).sum_eq

theorem count_vervaat (x : List ℤ) (a : ℤ) : (vervaat x).count a = x.count a := by
  rw [vervaat, cyclicShift_eq_rotate]; exact (List.rotate_perm _ _).count_eq a

/-- `i_*` is the FIRST minimizing index (characterization used by the hand checks). -/
theorem vervaatIdx_eq_of {x : List ℤ} {j : ℕ} (h1 : 1 ≤ j) (h2 : j ≤ x.length)
    (hmin : ∀ i : ℕ, 1 ≤ i → i ≤ x.length → (x.take j).sum ≤ (x.take i).sum)
    (hfirst : ∀ j' : ℕ, 1 ≤ j' → j' < j → ∃ i : ℕ, 1 ≤ i ∧ i ≤ x.length ∧
      (x.take i).sum < (x.take j').sum) :
    vervaatIdx x = j := by
  apply le_antisymm
  · exact Nat.sInf_le ⟨h1, h2, hmin⟩
  · have hne : {j : ℕ | 1 ≤ j ∧ j ≤ x.length ∧
        ∀ i : ℕ, 1 ≤ i → i ≤ x.length → (x.take j).sum ≤ (x.take i).sum}.Nonempty :=
      ⟨j, h1, h2, hmin⟩
    obtain ⟨a1, a2, a3⟩ := Nat.sInf_mem hne
    by_contra hlt
    have hlt := Nat.lt_of_not_le hlt
    obtain ⟨i, i1, i2, i3⟩ := hfirst _ a1 hlt
    exact absurd (a3 i i1 i2) (not_le.2 i3)

/-- Hand check (`k = 3`, `n = 2`): `V(-1, 1, -1) = (1, -1, -1)` (`w = (-1, 0, -1)`, `i_* = 1`). -/
example : vervaat [-1, 1, -1] = [1, -1, -1] := by
  have : vervaatIdx [-1, 1, -1] = 1 := by
    refine vervaatIdx_eq_of (by norm_num) (by simp) ?_ ?_
    · intro i h1 h2
      simp only [List.length_cons, List.length_nil] at h2
      interval_cases i <;> simp
    · intro j' h1 h2; omega
  simp [vervaat, this, cyclicShift]

/-- Hand check: `V(1, -1, -1) = (1, -1, -1)` (`w = (1, 0, -1)`, `i_* = 3`, shift by `k` is the identity). -/
example : vervaat [1, -1, -1] = [1, -1, -1] := by
  have : vervaatIdx [1, -1, -1] = 3 := by
    refine vervaatIdx_eq_of (by norm_num) (by simp) ?_ ?_
    · intro i h1 h2
      simp only [List.length_cons, List.length_nil] at h2
      interval_cases i <;> simp
    · intro j' h1 h2
      interval_cases j'
      · exact ⟨3, by norm_num, by simp, by simp⟩
      · exact ⟨3, by norm_num, by simp, by simp⟩
  simp [vervaat, this, cyclicShift]

/-- Hand check (tie, FIRST minimizing index): `V(-1, 0) = (0, -1)` (`w = (-1, -1)`, `i_* = 1`). -/
example : vervaat [-1, 0] = [0, -1] := by
  have : vervaatIdx [-1, 0] = 1 := by
    refine vervaatIdx_eq_of (by norm_num) (by simp) ?_ ?_
    · intro i h1 h2
      simp only [List.length_cons, List.length_nil] at h2
      interval_cases i <;> simp
    · intro j' h1 h2; omega
  simp [vervaat, this, cyclicShift]

/-! ## 6.8 Proposition `prop:timereversal` -/

/-- The vector `(W_0, …, W_m)`. -/
def walkPath (m : ℕ) (ω : ℕ → ℕ) : Fin (m + 1) → ℤ := fun i => walkSum ω i

/-- The reversed vector `(Ŵ^{(m)}_0, …, Ŵ^{(m)}_m)`, `Ŵ^{(m)}_i = W_m - W_{m-i}`. -/
def reversedPath (m : ℕ) (ω : ℕ → ℕ) : Fin (m + 1) → ℤ := fun i => walkSum ω m - walkSum ω (m - i)

/-- The conditioning event `{W_m = 0, Λ(m) = n}`. -/
def timeReversalEvent (m n : ℕ) : Set (ℕ → ℕ) := {ω | walkSum ω m = 0 ∧ walkLeafCount ω m = n}

/-! ## 7.3 The displayed law and uniform trees -/

/-- The displayed offspring weights `μ(0) = 2 - √2`, `μ(1) = 0`, `μ(i) = ((2-√2)/2)^{i-1}` (`i ≥ 2`). -/
noncomputable def displayedWeight : ℕ → ℝ≥0∞
  | 0 => ENNReal.ofReal (2 - Real.sqrt 2)
  | 1 => 0
  | i + 2 => ENNReal.ofReal (((2 - Real.sqrt 2) / 2) ^ (i + 1))

/-- `μ` is the displayed law.  (Used instead of constructing a `PMF` by hand; non-vacuity is
`exists_displayedLaw`.) -/
def IsDisplayedLaw (μ : PMF ℕ) : Prop := ∀ i : ℕ, μ i = displayedWeight i

/-- `b = 1/μ(2) = 2 + √2`. -/
noncomputable def bConst : ℝ := 2 + Real.sqrt 2

/-- `Δ(τ) = max{k_u ; u ∈ τ}`, the maximum number of children (`PlaneTree.degrees` lists all
outdegrees). -/
def maxDegree (t : PlaneTree) : ℕ := t.degrees.foldr max 0

/-- Finite plane trees with `n` leaves and no vertex with exactly one child. -/
def uniformTrees (n : ℕ) : Set LocallyFinite.Tree :=
  finiteTreeEvent fun t => t.degreeCount 0 = n ∧ 1 ∉ t.degrees

/-- `P[W_1 ≥ a]` for the step `W_1 = K - 1`, `K ∼ μ` (`a` real). -/
noncomputable def stepTail (μ : PMF ℕ) (a : ℝ) : ℝ := (stepLaw μ).real {z : ℤ | a ≤ (z : ℝ)}


/-- A finite size class (needed to state uniformity): `uniformTrees n` is finite (a tree with `n`
leaves and no unary vertex has at most `2n - 1` vertices). -/
theorem finite_uniformTrees (n : ℕ) : (uniformTrees n).Finite := by
  have key : ∀ L : List ℕ, 1 ∉ L → 2 * (L.length - L.count 0) ≤ L.sum := by
    intro L
    induction L with
    | nil => simp
    | cons a L ih =>
      intro h
      have h1 : a ≠ 1 := fun e => h (by simp [e])
      have h2 : 1 ∉ L := fun e => h (List.mem_cons_of_mem _ e)
      have := ih h2
      have hc : L.count 0 ≤ L.length := List.count_le_length
      rw [List.count_cons, List.sum_cons, List.length_cons]
      by_cases ha : a = 0
      · subst ha; simp; omega
      · have : 2 ≤ a := by omega
        simp [ha]; omega
  have hsub : uniformTrees n ⊆ (fun t : PlaneTree => t.toLocallyFinite) ''
      {t : PlaneTree | t.size ≤ 2 * n} := by
    rintro T ⟨t, rfl, h0, h1⟩
    refine ⟨t, ?_, rfl⟩
    have hk := key t.degrees h1
    have hs := t.sum_degrees_add_one
    have hl := t.length_degrees
    have hc : t.degrees.count 0 = n := h0
    show t.size ≤ 2 * n
    omega
  exact ((PlaneTree.finite_size_le (2 * n)).image _).subset hsub

/-- "`τ_n` is uniform over the plane trees with `n` leaves and no unary vertex", for every
`n ≥ 1` for which `P_μ[λ = n] > 0` (the paper's `τ_n` is only defined for those `n`). -/
noncomputable def IsUniformConditioned (μ : PMF ℕ) : Prop :=
  ∀ n : ℕ, 1 ≤ n → bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0 →
    (bienaymeLaw μ.toMeasure)[|leafCountEvent n] =
      Measure.uniformOfFinset (finite_uniformTrees n).toFinset

end BGWLeaves
