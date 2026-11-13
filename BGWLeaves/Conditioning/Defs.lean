module

public import BGWLeaves.Passage
public import BGWLeaves.ForestLaw
public import BGWLeaves.LeafConcentration
public import BGWLeaves.LeafMass
public import BGWLeaves.StableAnalysis
public import BGWLeaves.StableAnalysis.Consequences
public import BGWLeaves.Vervaat.Defs
public import BGW.Tree.Height

/-!
# Conditioning on the number of leaves (M6): definitions and proved bridges

Source: arXiv:1110.2163v4, `largetrees_final.tex`: Lemma 4.3 (`lemma:passage`, line 1149),
Proposition 4.4 (`prop:passage`, line 1200), Proposition 5.2 (`prop:abscon`, line 1384), Lemma 5.6
(`lem:CVf`, line 1473) and Lemma 6.10 (`lem:absolueC2`, line 2185).

This file contains every definition of milestone M6 and the proved bridges.  It contains no proof
holes.  The statements still to be proved are in `BGWLeaves.Conditioning`; their proofs are supplied by
the provider modules `BGWLeaves.Conditioning.*` (imported through `BGWLeaves.Conditioning.Proof`).

Conventions.
* Offspring law `μ : PMF ℕ`; one tree: `bienaymeLaw μ.toMeasure` on `LocallyFinite.Tree`; `j`
  independent trees: `forestLaw μ j = Measure.pi (fun _ : Fin j => bienaymeLaw μ.toMeasure)`; walk with
  steps `ω i - 1`: `iidWalk μ = Measure.infinitePi (fun _ : ℕ => μ.toMeasure)`, `W_m = walkSum ω m`
  (the definition of `BGWLeaves.Vervaat.Defs`).
* Measurable structure on trees: `LocallyFinite.Tree` carries the product sigma-algebra of
  `Address → ℕ` (Polish); "bounded nonnegative measurable test with bound `M`" is `IsBoundedTest M U`.  A
  functional of finite plane trees is lifted by `finiteTreeLift` / `finiteTreeLiftR` (junk `0` on infinite
  trees, which are null in the critical case with `μ 1 ≠ 1`).
* Conditioning is `ProbabilityTheory.cond`: conditioning on a null event gives the zero measure.
* Events of "number of leaves / vertices" are events of FINITE trees (`finiteTreeEvent`, `forestEvent`),
  except `sizeGeEvent` and `forestSizeGeEvent`, which contain the infinite trees (the sealed convention of
  `cor_GD2mieux`).  `psi μ p j = P_{μ,j}(λ = p)` and `psiStar μ p j = P_{μ,j}(λ ≥ p)` are `ℝ≥0∞`-valued
  (`LocalEstimates` uses their `.toReal`); `chi μ k j = P_j[W_{T_k} = -1]` likewise.
* Two different clocks "`T_k`" (as in the paper): `treeLeafTime` (Section 5, index of the `k`-th leaf of a
  tree) and `walkLeafTime` (Section 6, time after the `k`-th step `-1` of the walk).
* `μ₀ = (μ 0).toReal`; `B_n = norming (stepLaw μ) θ n` (the corrected norming); `(H_θ)` is spelled out as
  `IsCritical μ`, `μ 1 ≠ 1`, `Aperiodic μ`, `∃ a, StableDomain μ θ a`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## 0. The tree space, tests, and the events -/

/-- The law of `j` independent `GW_μ` trees, `P_{μ,j}` of the paper. -/
noncomputable abbrev forestLaw (μ : PMF ℕ) (j : ℕ) : Measure (Fin j → LocallyFinite.Tree) :=
  Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure

/-- "`U` is a bounded nonnegative measurable test with bound `M`": `0 ≤ U ≤ M` pointwise and `U`
measurable for the sigma-algebra of the ambient space (`LocallyFinite.Tree`, or `Fin j → LocallyFinite.Tree`).
The paper's `‖U‖` is any `M` with this property (the least one is `‖U‖_∞`). -/
def IsBoundedTest {α : Type*} [MeasurableSpace α] (M : ℝ) (U : α → ℝ) : Prop :=
  Measurable U ∧ ∀ x, 0 ≤ U x ∧ U x ≤ M

open scoped Classical in
/-- Lift of a functional of finite plane trees to `LocallyFinite.Tree`: `g t` at `t.toLocallyFinite`,
junk value `0` at infinite trees (null in the critical case).  Used to state results about functionals of
`PlaneTree` (the Łukasiewicz prefix, ...) against `bienaymeLaw`. -/
noncomputable def finiteTreeLift (g : PlaneTree → ℝ≥0∞) : LocallyFinite.Tree → ℝ≥0∞ :=
  fun T => if h : ∃ t : PlaneTree, t.toLocallyFinite = T then g h.choose else 0

theorem finiteTreeLift_toLocallyFinite (g : PlaneTree → ℝ≥0∞) (t : PlaneTree) :
    finiteTreeLift g t.toLocallyFinite = g t := by
  have h : ∃ t' : PlaneTree, t'.toLocallyFinite = t.toLocallyFinite := ⟨t, rfl⟩
  simp only [finiteTreeLift, h, ↓reduceDIte]
  exact congrArg g (PlaneTree.toLocallyFinite_injective h.choose_spec)

theorem finiteTreeLift_of_infinite (g : PlaneTree → ℝ≥0∞) {T : LocallyFinite.Tree}
    (hT : ¬ FiniteVertices T) : finiteTreeLift g T = 0 := by
  have h : ¬ ∃ t : PlaneTree, t.toLocallyFinite = T := fun h =>
    hT ((exists_toLocallyFinite_iff T).1 h)
  simp only [finiteTreeLift, h, ↓reduceDIte]

open scoped Classical in
/-- Real-valued version of `finiteTreeLift`, for real tests `U : Tree → ℝ` built from a functional of
finite plane trees (e.g. `F(B_ζ/ζ · C_{2ζ·}(τ))` of Theorems 4.1/4.5, tranche 2); junk value `0` at infinite
trees. -/
noncomputable def finiteTreeLiftR (g : PlaneTree → ℝ) : LocallyFinite.Tree → ℝ :=
  fun T => if h : ∃ t : PlaneTree, t.toLocallyFinite = T then g h.choose else 0

theorem finiteTreeLiftR_toLocallyFinite (g : PlaneTree → ℝ) (t : PlaneTree) :
    finiteTreeLiftR g t.toLocallyFinite = g t := by
  have h : ∃ t' : PlaneTree, t'.toLocallyFinite = t.toLocallyFinite := ⟨t, rfl⟩
  simp only [finiteTreeLiftR, h, ↓reduceDIte]
  exact congrArg g (PlaneTree.toLocallyFinite_injective h.choose_spec)

/-- `{λ(F) = m}` for a forest of `j` trees: the forest is finite and has `m` leaves in total
(`= ⋃_p forestEvent j p m`).  For `j = 1` it is `leafCountEvent m` (`psi_one`). -/
def forestLeafCountEvent (j m : ℕ) : Set (Fin j → LocallyFinite.Tree) :=
  ⋃ p : ℕ, forestEvent j p m

/-- `{λ(F) ≥ m}` for a forest of `j` trees, FINITE forests only (an infinite forest is null for
critical `μ`; this is the convention of `leafCountEvent`).  `m` is a natural number; the real threshold of the
paper is `⌈·⌉₊` (`mem_forestLeafGeEvent_real_iff`). -/
def forestLeafGeEvent (j m : ℕ) : Set (Fin j → LocallyFinite.Tree) :=
  {F | ∃ p m' : ℕ, m ≤ m' ∧ F ∈ forestEvent j p m'}

/-- `{ζ(F) ≥ n}` for a forest, INCLUDING the infinite forests (as `sizeGeEvent`). -/
def forestSizeGeEvent (j n : ℕ) : Set (Fin j → LocallyFinite.Tree) :=
  {F | (∃ i, ¬ FiniteVertices (F i)) ∨ ∃ p : ℕ, F ∈ forestSizeEvent j p ∧ n ≤ p}

/-- The size window `{n - (μ₀⁻¹ + 1) n^{3/4} ≤ ζ(F) ≤ n}` of Lemma 4.3 (`μ0 = μ₀`), finite forests. -/
def forestSizeWindow (μ0 : ℝ) (j n : ℕ) : Set (Fin j → LocallyFinite.Tree) :=
  {F | ∃ p : ℕ, F ∈ forestSizeEvent j p ∧
    (n : ℝ) - (1 / μ0 + 1) * (n : ℝ) ^ (3 / 4 : ℝ) ≤ p ∧ p ≤ n}

/-- `{λ(τ) ≥ m}` for a single tree: the tree is finite and has at least `m` leaves. -/
def leafGeEvent (m : ℕ) : Set LocallyFinite.Tree :=
  finiteTreeEvent fun t => m ≤ t.degreeCount 0

/-- The size window `{n - (μ₀⁻¹ + 1) n^{3/4} ≤ ζ(τ) ≤ n}` for a single tree. -/
def sizeWindow (μ0 : ℝ) (n : ℕ) : Set LocallyFinite.Tree :=
  {T | ∃ p : ℕ, T ∈ sizeEvent p ∧ (n : ℝ) - (1 / μ0 + 1) * (n : ℝ) ^ (3 / 4 : ℝ) ≤ p ∧ p ≤ n}

/-- The CEILING cutoff `⌈μ₀ n - n^{3/4}⌉` of Proposition 4.4(ii) (`ℕ`-valued; the ceiling of a negative
number is `0`, which only affects the small `n` for which `μ₀ n < n^{3/4}`). -/
noncomputable def leafCutoff (μ : PMF ℕ) (n : ℕ) : ℕ :=
  ⌈(μ 0).toReal * n - (n : ℝ) ^ (3 / 4 : ℝ)⌉₊

/-- `ψ_p(j) = P_{μ,j}(λ = p)` (value in `ℝ≥0∞`, the mass of `forestLeafCountEvent j p`). -/
noncomputable def psi (μ : PMF ℕ) (p j : ℕ) : ℝ≥0∞ := forestLaw μ j (forestLeafCountEvent j p)

/-- `ψ*_p(j) = P_{μ,j}(λ ≥ p)`. -/
noncomputable def psiStar (μ : PMF ℕ) (p j : ℕ) : ℝ≥0∞ := forestLaw μ j (forestLeafGeEvent j p)

/-- The real threshold of the paper is the ceiling: `λ ≥ a` iff `λ ≥ ⌈a⌉` for integer-valued `λ`.  PROVED. -/
theorem mem_forestLeafGeEvent_real_iff (j : ℕ) (a : ℝ) (F : Fin j → LocallyFinite.Tree) :
    F ∈ forestLeafGeEvent j ⌈a⌉₊ ↔ ∃ p m' : ℕ, a ≤ m' ∧ F ∈ forestEvent j p m' := by
  unfold forestLeafGeEvent
  simp only [Set.mem_ofPred_eq, Nat.ceil_le]

/-- Same for one tree. PROVED. -/
theorem mem_leafGeEvent_real_iff (a : ℝ) (T : LocallyFinite.Tree) :
    T ∈ leafGeEvent ⌈a⌉₊ ↔ ∃ t : PlaneTree, t.toLocallyFinite = T ∧ a ≤ t.degreeCount 0 := by
  unfold leafGeEvent finiteTreeEvent
  simp only [Set.mem_ofPred_eq, Nat.ceil_le]

/-- `ψ_p(j) ≤ ψ*_p(j)`.  ROUTINE (`forestLeafCountEvent ⊂ forestLeafGeEvent`).  PROVED. -/
theorem psi_le_psiStar (μ : PMF ℕ) (p j : ℕ) : psi μ p j ≤ psiStar μ p j := by
  refine measure_mono ?_
  rintro F hF
  obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hF
  exact ⟨q, p, le_rfl, hq⟩

/-- `ψ`, `ψ*` are finite (masses of events of probability measures). -/
theorem psi_ne_top (μ : PMF ℕ) (p j : ℕ) : psi μ p j ≠ ⊤ := by
  have : IsProbabilityMeasure (forestLaw μ j) := by unfold forestLaw; infer_instance
  exact measure_ne_top _ _

theorem psiStar_ne_top (μ : PMF ℕ) (p j : ℕ) : psiStar μ p j ≠ ⊤ := by
  have : IsProbabilityMeasure (forestLaw μ j) := by unfold forestLaw; infer_instance
  exact measure_ne_top _ _

/-- The real-valued form of `ψ_p(j)` used in `BGWLeaves.LocalEstimates`. -/
theorem toReal_psi (μ : PMF ℕ) (p j : ℕ) :
    (psi μ p j).toReal = (forestLaw μ j).real (forestLeafCountEvent j p) := rfl

/-- The real-valued form of `ψ*_p(j)` used in `BGWLeaves.LocalEstimates`. -/
theorem toReal_psiStar (μ : PMF ℕ) (p j : ℕ) :
    (psiStar μ p j).toReal = (forestLaw μ j).real (forestLeafGeEvent j p) := rfl

/-- Under `(H_θ)`, `P_μ[ζ = n] > 0` for all large `n` (Remark 1.12 with `d = 1`; sealed
`sizeProb_pos_iff` and `aperiodic_iff_latticeSpan_eq_one`).  PROVED from the sealed results.  This is what
makes the Lean convention (`E[U | ζ = n] := 0` for null `n`) harmless in Proposition 4.4(i). -/
theorem sizeEvent_ne_zero_eventually {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → bienaymeLaw μ.toMeasure (sizeEvent n) ≠ 0 := by
  obtain ⟨b, hb⟩ := hDA
  obtain ⟨N, hN⟩ := sizeProb_pos_iff hb
  have hd := (aperiodic_iff_latticeSpan_eq_one hc hne).1 hap
  exact ⟨N, fun n hn => (hN n hn).2 (by rw [hd]; exact one_dvd _)⟩

/-! ## 5.2 and 5.6: the tree clock -/

/-- `T_k(τ)` of Section 5 (line 1280): the first index `i` (zero-based, lexicographic order) such that
`{u(0), …, u(i)}` contains `k` leaves, `∞` if there is none (`⊤`).  Stated as the least `i` with at least
`k` leaves among `u(0..i)` (equal to "exactly `k`" for `k ≥ 1`; for `k = 0` it is `0`, an irrelevant
degenerate case: the paper takes `k ≥ 1`).  `t.degrees` is the depth-first list of offspring numbers
(`childCountAt t i = t.degrees.getD i 0`). -/
noncomputable def treeLeafTime (t : PlaneTree) (k : ℕ) : ℕ∞ :=
  ⨅ (i : ℕ) (_ : k ≤ (t.degrees.take (i + 1)).count 0), (i : ℕ∞)

/-- `W^{(k)}(τ) = (W_0(τ), …, W_{T_k(τ)}(τ))`, as a list of length `T_k + 1` (junk `[W_0] = [0]` if
`T_k = ∞`; this only happens if `λ(τ) < k`, outside every event below).  `PlaneTree.lukasiewicz t i =
∑_{r < i} (k_r - 1)` is the paper's `W_i(τ)` (`W_0 = 0`, `W_{i+1} = W_i + k_i - 1`). -/
noncomputable def treeStopPath (t : PlaneTree) (k : ℕ) : List ℤ :=
  (List.range ((treeLeafTime t k).toNat + 1)).map t.lukasiewicz

/-- `W_{T_k(τ)}(τ)`, the position of the Łukasiewicz path at the `k`-th leaf (BEFORE the leaf is
read, in the paper's indexing).  It equals the NUMBER OF PENDING TREES `j` after the leaf is read: the
remaining part of the tree is a forest of `W_{T_k}` trees (`abscon_pending_nonneg`). -/
noncomputable def treeStopPos (t : PlaneTree) (k : ℕ) : ℤ :=
  t.lukasiewicz (treeLeafTime t k).toNat

/-- The number of pending trees `j := W_{T_k(τ)}(τ)` as a natural number (`≥ 0` for `k ≤ λ(τ)`). -/
noncomputable def pendingTrees (t : PlaneTree) (k : ℕ) : ℕ := (treeStopPos t k).toNat

/-- The event "the first-leaf clock deviates": `T = ∞` or `|T/n - target| > n^{-1/4}`
(`T : ℕ∞` a value of `treeLeafTime`; the paper's `|T_u/n - b| > n^{-1/4}` with `T_u = ∞` when the tree has
fewer than `⌊u⌋` leaves, for which the deviation is `+∞`). -/
def ClockDev (n : ℕ) (target : ℝ) (T : ℕ∞) : Prop :=
  T = ⊤ ∨ (n : ℝ) ^ (-(1 / 4 : ℝ)) < |(T.toNat : ℝ) / n - target|

/-! ## 6.10 The walk, the leaf clock -/

/-- The i.i.d. walk steps `ω i ∼ μ` (the walk of Proposition 1.4 has increments `ω i - 1`);
`Measure.infinitePi`, as in M2b. -/
noncomputable abbrev iidWalk (μ : PMF ℕ) : Measure (ℕ → ℕ) :=
  Measure.infinitePi fun _ : ℕ => μ.toMeasure

/-- `T_k = inf{m ≥ 0 : Λ(m) = k}` of (`eq:notations`, line 1999), with `Λ(m) = walkLeafCount ω m`
(the number of the first `m` steps equal to `-1`); `⊤` if there is none.  `T_k` is the time just AFTER the `k`-th
step `-1` (`T_0 = 0`).  NOTE the offset with the tree clock `treeLeafTime`: `T_k(walk) = T_k(tree) + 1`
(the paper uses `T_k` for both). -/
noncomputable def walkLeafTime (ω : ℕ → ℕ) (k : ℕ) : ℕ∞ :=
  ⨅ (m : ℕ) (_ : walkLeafCount ω m = k), (m : ℕ∞)

/-- `W_{T_k}`, junk `W_0 = 0` if `T_k = ⊤` (null event, never relevant: the events below require
`T_k ≠ ⊤`). -/
noncomputable def walkStopPos (ω : ℕ → ℕ) (k : ℕ) : ℤ := walkSum ω (walkLeafTime ω k).toNat

/-- `W^{(k)} = (W_0, …, W_{T_k})` as a list of length `T_k + 1`. -/
noncomputable def walkStopPath (ω : ℕ → ℕ) (k : ℕ) : List ℤ :=
  (List.range ((walkLeafTime ω k).toNat + 1)).map (walkSum ω)

/-- `{T_k < ∞, W_{T_k} = x}`. -/
def walkStopEvent (k : ℕ) (x : ℤ) : Set (ℕ → ℕ) :=
  {ω | walkLeafTime ω k ≠ ⊤ ∧ walkStopPos ω k = x}

/-- `χ_k(j) = P_j[W_{T_k} = -1]` for the walk started at `j ∈ ℤ`; by translation
`P_j[W_{T_k} = -1] = P[W_{T_k} = -1 - j]` (the clock `T_k` does not depend on the starting point; the paper
writes this identity in the proof of Lemma 6.11).  `χ_n(0) = P[W_{T_n} = -1]`. -/
noncomputable def chi (μ : PMF ℕ) (k : ℕ) (j : ℤ) : ℝ≥0∞ := iidWalk μ (walkStopEvent k (-1 - j))

/-- The shifted sequence `θ_m ω = (ω (m + i))_{i ≥ 0}`. -/
def shiftSeq (m : ℕ) (ω : ℕ → ℕ) : ℕ → ℕ := fun i => ω (m + i)

/-! ## Non-vacuity of the test classes -/

/-- The constant test `1` is a bounded nonnegative measurable test (bound `1`); with it Lemma 4.3 and
Proposition 4.4 are statements about probabilities. -/
theorem isBoundedTest_one {α : Type*} [MeasurableSpace α] : IsBoundedTest (1 : ℝ) (fun _ : α => (1 : ℝ)) :=
  ⟨measurable_const, fun _ => ⟨zero_le_one, le_rfl⟩⟩

/-- The indicator of a measurable set is a bounded test (bound `1`): e.g. `U = 1_{height ≤ h}`, or, through
`finiteTreeLift` and `measurable_finiteTreeLift`, any `{0,1}`-valued functional of a finite plane tree. -/
theorem isBoundedTest_indicator {α : Type*} [MeasurableSpace α] {s : Set α} (hs : MeasurableSet s) :
    IsBoundedTest (1 : ℝ) (s.indicator fun _ : α => (1 : ℝ)) := by
  refine ⟨measurable_const.indicator hs, fun x => ?_⟩
  by_cases hx : x ∈ s <;> simp [hx]

/-- `χ_k(j)` is finite. -/
theorem chi_ne_top (μ : PMF ℕ) (k : ℕ) (j : ℤ) : chi μ k j ≠ ⊤ := by
  have : IsProbabilityMeasure (iidWalk μ) := by unfold iidWalk; infer_instance
  exact measure_ne_top _ _

end BGWLeaves
