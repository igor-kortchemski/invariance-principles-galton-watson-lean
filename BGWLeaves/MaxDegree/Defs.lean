module

public import BGWLeaves.Vervaat.Defs
public import BGWLeaves.Conditioning.Defs
public import BGWLeaves.LocalEstimates.Defs
public import BGWLeaves.StableAnalysis.Consequences

/-!
# Maximum degree: definitions and bridges

Source: arXiv:1110.2163v4 (line numbers refer to its LaTeX source), Section 7: Theorem 7.1(ii) (`thm:max`, finite variance,
hypothesis `𝓗`), Lemma 7.2 (`lem:MM`) and the discrete lemmas of the proof of 7.1 (lines 2328-2486); Remark 7.3
(`eq:better`).

This file contains the definitions for the maximum degree and the elementary bridges.  The main statements
are in `BGWLeaves.MaxDegree`; their proofs are in the modules `BGWLeaves.MaxDegree.*` (imported through
`BGWLeaves.MaxDegree.Proof`).

Conventions.
* Walk laws as in `BGWLeaves.Vervaat.Defs`: `Measure.infinitePi (fun _ : ℕ => μ)` on `ℕ → ℕ`, step `ω i - 1`.
* Words are `List ℤ`; "all steps `< p`" and "some step `> q`" are the predicates `StepsLt p`, `StepsGt q`
  (no `max` of a list is needed; `M([]) = -∞` is automatic).
* Conditioning is `ProbabilityTheory.cond`: conditioning on a null event gives the zero measure; the statements
  about `P_μ[· | λ = n]` are therefore made for `n` with `leafProb μ n ≠ 0`.
* `D(n)` is `bigD μ n` (`sSup` in `ℕ`), `μ([x,∞))` for a real `x` is `offTail μ x`.
-/

@[expose] public section

namespace BGWLeaves

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-- Notation only (the Vervaat notation is `local`): the law of the iid walk, steps `ω i - 1`. -/
local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

/-! ## 0. The hypothesis `𝓗` of Section 7 (lines 2344-2347) -/

/-- The radius of convergence `R ∈ [0, ∞]` of `∑ μ(i) z^i`: the supremum of the `r ≥ 0` for which
`∑ μ(i) r^i` converges (the definition; no Cauchy-Hadamard is used). -/
noncomputable def genFunRadius (μ : PMF ℕ) : ℝ≥0∞ :=
  ⨆ (r : ℝ≥0) (_ : Summable fun n : ℕ => (μ n).toReal * (r : ℝ) ^ n), (r : ℝ≥0∞)

/-- **Hypothesis `𝓗`** of Section 7: `ν` is critical, aperiodic, of finite variance, with `R > 1`, and
if `R < ∞` then `ν(n)^{1/n} → 1/R`, while if `R = ∞` there is `N` with `(ν(k)^{1/k})_{k ≥ N}` decreasing.
Spelled out (as `(H_θ)` in `BGWLeaves.LeafConcentration` and `BGWLeaves.LeafMass`): `IsCritical`, `μ 1 ≠ 1` (part (i) of `(H_θ)`: "`μ(1) < 1`"),
`Aperiodic`, finite variance (`MemLp (fun j => j) 2`, the form of `HthetaTail`), then the two clauses on `R`.
"Decreasing" is read as non-increasing (`AntitoneOn`); this is the weaker reading, which includes laws with bounded
support (`ν(k) = 0` eventually), and it makes the theorem stronger.  `finiteVariance` is redundant under
`radius_gt_one` (printed), and `nondegenerate` is not part of the printed `𝓗` but of `(H_θ)(i)`. -/
structure HypH (μ : PMF ℕ) : Prop where
  critical : IsCritical μ
  nondegenerate : μ 1 ≠ 1
  aperiodic : Aperiodic μ
  finiteVariance : MemLp (fun j : ℕ => (j : ℝ)) 2 μ.toMeasure
  radius_gt_one : 1 < genFunRadius μ
  root_limit : genFunRadius μ < ⊤ →
    Tendsto (fun n : ℕ => (μ n).toReal ^ (1 / (n : ℝ))) atTop (𝓝 ((genFunRadius μ).toReal)⁻¹)
  root_antitone : genFunRadius μ = ⊤ →
    ∃ N : ℕ, AntitoneOn (fun k : ℕ => (μ k).toReal ^ (1 / (k : ℝ))) (Set.Ici N)

/-- `𝓗` gives the finite variance in the form used by the principles (`Integrable (z^2) (stepLaw μ)`). -/
theorem HypH.integrable_sq {μ : PMF ℕ} (h : HypH μ) :
    Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ) :=
  (Scalar.memLp_step_of_memLp_offspring h.finiteVariance).integrable_sq

/-- `𝓗` implies `(H_2)` in the sense of `HthetaTail` (the standing hypothesis of Section 7 with `θ = 2`). -/
theorem HypH.hthetaTail {μ : PMF ℕ} (h : HypH μ) : HthetaTail μ 2 := Or.inl ⟨rfl, h.finiteVariance⟩

/-- `𝓗` implies `∃ a, StableDomain μ 2 a` (the form of `(H_θ)(ii)` in `BGWLeaves.LeafConcentration` and `BGWLeaves.LeafMass`). -/
theorem HypH.stableDomain {μ : PMF ℕ} (h : HypH μ) : ∃ a : ℕ → ℝ, StableDomain μ 2 a :=
  ⟨_, Scalar.stableDomain_of_finiteVariance h.critical h.nondegenerate h.finiteVariance⟩

/-! ## 1. `D(n)` and the tails -/

/-- `μ([x, ∞))` for a real threshold `x` (`{k : ℕ | x ≤ k}`); this is the paper's `μ([x,∞))`,
e.g. `μ([(1 - ε) D(n), ∞))`. -/
noncomputable def offTail (μ : PMF ℕ) (x : ℝ) : ℝ := (μ.toMeasure {k : ℕ | x ≤ (k : ℝ)}).toReal

/-- `D(n) = max {k ≥ 1 ; μ([k,∞)) ≥ 1/n}` (`sSup` in `ℕ`).  The set is nonempty and bounded for
`n ≥ 1/(1 - μ₀)` (see `bigD_spec`); for smaller `n` the value is the junk `0`. -/
noncomputable def bigD (μ : PMF ℕ) (n : ℕ) : ℕ :=
  sSup {k : ℕ | 1 ≤ k ∧ 1 / (n : ℝ) ≤ offTail μ k}

/-! ## 2. Steps versus degrees: the difference of one -/

/-- "all steps `< p`": `M(x) < p` for the maximum `M` of the word (true for `[]`, `M([]) = -∞`). -/
def StepsLt (p : ℝ) (x : List ℤ) : Prop := ∀ a ∈ x, (a : ℝ) < p

/-- "some step `> q`": `M(x) > q`. -/
def StepsGt (q : ℝ) (x : List ℤ) : Prop := ∃ a ∈ x, q < (a : ℝ)

theorem stepsLt_rotate (p : ℝ) (x : List ℤ) (i : ℕ) : StepsLt p (x.rotate i) ↔ StepsLt p x := by
  simp [StepsLt, List.mem_rotate]

theorem stepsGt_rotate (q : ℝ) (x : List ℤ) (i : ℕ) : StepsGt q (x.rotate i) ↔ StepsGt q x := by
  simp [StepsGt, List.mem_rotate]

/-- `F(V(u)) = F(u)` for `F = 1{M < p}` ("the fact that `F^{(n)}(V(u)) = F^{(n)}(u)`", line 2398):
the maximum is invariant under cyclic shifts. -/
theorem stepsLt_vervaat (p : ℝ) (x : List ℤ) : StepsLt p (vervaat x) ↔ StepsLt p x := by
  rw [vervaat, cyclicShift_eq_rotate, stepsLt_rotate]

theorem stepsGt_vervaat (q : ℝ) (x : List ℤ) : StepsGt q (vervaat x) ↔ StepsGt q x := by
  rw [vervaat, cyclicShift_eq_rotate, stepsGt_rotate]

theorem stepsLt_take {p : ℝ} {x : List ℤ} (h : StepsLt p x) (j : ℕ) : StepsLt p (x.take j) :=
  fun a ha => h a (List.mem_of_mem_take ha)

theorem stepsGt_take_or_drop {q : ℝ} {x : List ℤ} (h : StepsGt q x) (j : ℕ) :
    StepsGt q (x.take j) ∨ StepsGt q (x.drop j) := by
  obtain ⟨a, ha, hq⟩ := h
  rw [← List.take_append_drop j x] at ha
  rcases List.mem_append.1 ha with h1 | h1
  · exact Or.inl ⟨a, h1, hq⟩
  · exact Or.inr ⟨a, h1, hq⟩

/-! ## 3. Events on trees and walks for the transfer of the cyclic maximum -/

/-- The tree event "`(W_1(τ), W_2(τ) - W_1(τ), …) ∈ S`" (`τ` finite). -/
def treeStepsIn (S : Set (List ℤ)) : Set LocallyFinite.Tree :=
  finiteTreeEvent fun t => t.increments ∈ S

/-- The walk event "`T_n < ∞`, `W_{T_n} = -1` and `(W_1, W_2 - W_1, …, W_{T_n} - W_{T_n-1}) ∈ S`". -/
def bridgeStepsIn (n : ℕ) (S : Set (List ℤ)) : Set (ℕ → ℕ) :=
  {ω | ∃ k, IsMarkTime n ω k ∧ walkSum ω k = -1 ∧ walkWord ω k ∈ S}

/-- The walk event "`T_m < ∞` and `(W_1, …, W_{T_m} - W_{T_m - 1}) ∈ S`" (the prefix up to the `m`-th mark;
no condition on `W`). -/
def prefixStepsIn (m : ℕ) (S : Set (List ℤ)) : Set (ℕ → ℕ) :=
  {ω | ∃ k, IsMarkTime m ω k ∧ walkWord ω k ∈ S}

open Classical in
/-- `W_{T_m}` as an integer-valued function (junk `0` on `{T_m = ∞}`, a null event: `ae_exists_markTime`). -/
noncomputable def walkAtMark (m : ℕ) (ω : ℕ → ℕ) : ℤ :=
  if hω : ∃ k, IsMarkTime m ω k then walkSum ω (Classical.choose hω) else 0

/-! ## 4. Conditional mass of a window on the leaf-count event -/

/-- A nonzero `leafProb` is a nonzero `P_μ[λ = n]` in `ℝ≥0∞`. -/
theorem bienayme_leafCountEvent_ne_zero {μ : PMF ℕ} {n : ℕ} (h : leafProb μ n ≠ 0) :
    bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0 := by
  intro h0
  apply h
  simp [leafProb, Measure.real, h0]

/-- **Window from two exceptional events.**  If every finite tree with `n` leaves satisfies `P₁`, `P₂` or `P₃`
and `P_μ[λ = n] ≠ 0`, then `P_μ[P₃ | λ = n] ≥ 1 - P_μ[P₁ | λ = n] - P_μ[P₂ | λ = n]` (the events live on finite
trees; the infinite trees are not in `{λ = n}`).  Used to turn the two one-sided principles into the window. -/
theorem cond_leafCount_window_ge {μ : PMF ℕ} {n : ℕ}
    (hn : bienaymeLaw μ.toMeasure (leafCountEvent n) ≠ 0) (P₁ P₂ P₃ : PlaneTree → Prop)
    (hcov : ∀ t : PlaneTree, t.degreeCount 0 = n → P₁ t ∨ P₂ t ∨ P₃ t) :
    1 - ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real (finiteTreeEvent P₁)
        - ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real (finiteTreeEvent P₂) ≤
      ((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real (finiteTreeEvent P₃) := by
  set P := bienaymeLaw μ.toMeasure with hP
  set s := leafCountEvent n with hs
  have hT : P s ≠ ⊤ := measure_ne_top _ _
  have : IsProbabilityMeasure (P[|s]) := cond_isProbabilityMeasure hn
  have hsub : s ⊆ finiteTreeEvent P₁ ∪ finiteTreeEvent P₂ ∪ finiteTreeEvent P₃ := by
    rintro T ⟨t, rfl, ht⟩
    rcases hcov t ht with h | h | h
    · exact Or.inl (Or.inl ⟨t, rfl, h⟩)
    · exact Or.inl (Or.inr ⟨t, rfl, h⟩)
    · exact Or.inr ⟨t, rfl, h⟩
  have h1 : (P[|s]) (finiteTreeEvent P₁ ∪ finiteTreeEvent P₂ ∪ finiteTreeEvent P₃) = 1 := by
    rw [ProbabilityTheory.cond, Measure.smul_apply, Measure.restrict_apply_superset hsub, smul_eq_mul,
      ENNReal.inv_mul_cancel hn hT]
  have h2 := measureReal_union_le (μ := P[|s]) (finiteTreeEvent P₁ ∪ finiteTreeEvent P₂)
    (finiteTreeEvent P₃)
  have h3 := measureReal_union_le (μ := P[|s]) (finiteTreeEvent P₁) (finiteTreeEvent P₂)
  have h4 : (P[|s]).real (finiteTreeEvent P₁ ∪ finiteTreeEvent P₂ ∪ finiteTreeEvent P₃) = 1 := by
    simp [Measure.real, h1]
  linarith

end BGWLeaves
