module

public import BGWLeaves.MaxDegreeLimit.Defs
public import BGWLeaves.LeafLimits.Walk
public import BGW.StableTrees.RealAttraction
public import BGW.StableTrees.UnitExcursionLawBasic
public import BGW.StableTrees.ExcursionJump
public import BGW.Skorokhod.Jump
public import BGW.Skorokhod.Measurable
public import Mathlib.MeasureTheory.Measure.DiracProba
import Mathlib.Topology.Order.LeftRightLim
import BGWLeaves.Coding
import BGWLeaves.LeafLimits.Helpers
import BGW.StableTrees.RealAttractionBounds
import BGW.Probability.WeakConvergence
import BGW.MetricMeasure.WeakPerturbation

/-!
# Theorem 7.1(i): the largest jump

Proofs for Theorem 7.1(i): `maxJump_rescaledLuka`,
`thm_max_i`, `thm_max_i_pos` and `thm_max_two_zero` of `BGWLeaves.MaxDegreeLimit`, exported in namespace
`BGWLeaves.MaxDegreeLimit.Jump` with exactly the types stated there.

* `maxJump_rescaledLuka`: for a finite tree with at least two vertices, the Łukasiewicz path at its
  own size is BGW's word step path of the increment word `(k_u - 1)_u` (`rescaledLuka_eq_stepPath`);
  the positive jumps of a word step path are its letters (the jump at time `(i+1)/k` is the `i`-th
  letter, and no jump exceeds the largest letter), and the largest letter is `Δ(τ) - 1 ≥ 0` (the root
  has a child).
* `thm_max_i_pos`: BGW `ae_maxJump_pos_levyExcLaw`.
* `tendsto_scaledMaxDegree` (any `θ`), hence `thm_max_i` and `thm_max_two_zero`.  Only the walk part of
  the coding is used (Theorem 6.1, `BGWLeaves.LeafLimits.Walk`), not the joint Remark 5.10.  With
  `ζ = treeSize τ`, `n = q k`, `c = μ₀^{1/θ}`:
  `c Δ/B_n = (c B_ζ/B_n) · Δ̄(W/B_ζ) + c/B_n` on `{ζ ≥ 2, B_ζ > 0}` (`maxJump_rescaledLuka`).  Under
  `P_μ[· | λ = n]`, `ζ ≥ λ = n` almost surely, so this event is almost sure for `n` large and the error
  `c/B_n` is deterministic.  Theorem 6.1 and the continuity of `Δ̄` (BGW `lipschitzWith_two_maxJump`)
  give `Δ̄(W/B_ζ) → Δ̄(X^exc)`; `ζ/n → 1/μ₀` in probability (`BGWLeaves.LeafLimits.Helpers`) and the uniform
  regular variation of `B` (BGW `IsRealStableAttracted.uniform_ratio`) give `c B_ζ/B_n → 1` in
  probability; Slutsky (BGW `tendsto_map_prodMk_of_tendsto_of_error`,
  `tendsto_probabilityMap_of_error_probability`) concludes.  For `θ = 2` the limit is `δ_0`
  (BGW `ae_maxJump_eq_zero_levyExcLaw_two`).

This module does not import `BGWLeaves.LeafLimits`.
-/

@[expose] public section

namespace BGWLeaves.MaxDegreeLimit.Jump

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

/-! ## Jumps of a word step path -/

private theorem sum_take_succ (x : List ℤ) (j : ℕ) :
    (x.take (j + 1)).sum = (x.take j).sum + x.getD j 0 := by
  rw [List.take_add_one, List.sum_append]
  cases h : x[j]? <;> simp [List.getD_eq_getElem?_getD, h]

/-- No positive jump of the step path of a word exceeds `M / B` when every letter is at most `M`
(`M ≥ 0`, `B > 0`).  Stated for any path `f` with the values of the step path. -/
private theorem sub_leftLim_le_of_word {x : List ℤ} {B M : ℝ} (hB : 0 < B) (hM0 : 0 ≤ M)
    (hM : ∀ a ∈ x, (a : ℝ) ≤ M) (f : Skorokhod.D 1 ℝ)
    (hf : ∀ s : Set.Icc (0 : ℝ) 1, f s = (((x.take ⌊(x.length : ℝ) * s⌋₊).sum : ℤ) : ℝ) / B)
    (t : Set.Icc (0 : ℝ) 1) :
    f t - Function.leftLim f t ≤ M / B := by
  obtain ⟨m, hm⟩ : ∃ m, ⌊(x.length : ℝ) * (t : ℝ)⌋₊ = m := ⟨_, rfl⟩
  have hk : (m : ℝ) - 1 < (x.length : ℝ) * t := by
    have := Nat.floor_le (mul_nonneg (Nat.cast_nonneg x.length) t.2.1)
    rw [hm] at this
    linarith
  have hmul : Continuous (fun s : Set.Icc (0 : ℝ) 1 => (x.length : ℝ) * (s : ℝ)) := by
    fun_prop
  have hnear : ∀ᶠ s : Set.Icc (0 : ℝ) 1 in 𝓝[≤] t, (m : ℝ) - 1 < (x.length : ℝ) * s :=
    ((hmul.tendsto t).eventually (lt_mem_nhds hk)).filter_mono nhdsWithin_le_nhds
  have hev : ∀ᶠ s in 𝓝[≤] t, f s ∈ Set.Ici (f t - M / B) := by
    filter_upwards [hnear, self_mem_nhdsWithin] with s hs hst
    have hst' : (s : ℝ) ≤ t := hst
    obtain ⟨j, hj⟩ : ∃ j, ⌊(x.length : ℝ) * (s : ℝ)⌋₊ = j := ⟨_, rfl⟩
    have hjm : j ≤ m := by
      rw [← hj, ← hm]
      exact Nat.floor_mono (mul_le_mul_of_nonneg_left hst' (Nat.cast_nonneg _))
    have hmj : m ≤ j + 1 := by
      have h1 := Nat.lt_floor_add_one ((x.length : ℝ) * s)
      rw [hj] at h1
      have h2 : (m : ℝ) < ((j + 2 : ℕ) : ℝ) := by push_cast; linarith
      have h3 : m < j + 2 := by exact_mod_cast h2
      omega
    have hsum : (((x.take m).sum : ℤ) : ℝ) - (((x.take j).sum : ℤ) : ℝ) ≤ M := by
      rcases Nat.eq_or_lt_of_le hjm with h | h
      · rw [h, sub_self]
        exact hM0
      · have hmj' : m = j + 1 := by omega
        have hget : ((x.getD j 0 : ℤ) : ℝ) ≤ M := by
          rcases lt_or_ge j x.length with hjx | hjx
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hjx, Option.getD_some]
            exact hM _ (List.getElem_mem hjx)
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hjx, Option.getD_none]
            simpa using hM0
        rw [hmj', sum_take_succ]
        push_cast
        linarith
    have hdiff : (((x.take m).sum : ℤ) : ℝ) / B - (((x.take j).sum : ℤ) : ℝ) / B ≤ M / B := by
      rw [← sub_div]
      exact div_le_div_of_nonneg_right hsum hB.le
    change f t - M / B ≤ f s
    rw [hf s, hf t, hj, hm]
    linarith
  have hl : Function.leftLim f t ∈ Set.Ici (f t - M / B) :=
    isClosed_Ici.mem_of_mapClusterPt (mapClusterPt_leftLim f t) hev
  have hl' : f t - M / B ≤ Function.leftLim f t := hl
  linarith

/-- The jump of the step path of a word at time `(i + 1)/k` is the `i`-th letter divided by `B`. -/
private theorem exists_jump_eq_of_word {x : List ℤ} {B : ℝ} {i : ℕ} (hi : i < x.length)
    (f : Skorokhod.D 1 ℝ)
    (hf : ∀ s : Set.Icc (0 : ℝ) 1, f s = (((x.take ⌊(x.length : ℝ) * s⌋₊).sum : ℤ) : ℝ) / B) :
    ∃ t : Set.Icc (0 : ℝ) 1, f t - Function.leftLim f t = ((x[i] : ℤ) : ℝ) / B := by
  have hk : (0 : ℝ) < x.length := by exact_mod_cast (show 0 < x.length by omega)
  have hmem : ((i + 1 : ℕ) : ℝ) / x.length ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, (div_le_one hk).mpr (by exact_mod_cast hi)⟩
  refine ⟨⟨_, hmem⟩, ?_⟩
  have hfloor : ⌊(x.length : ℝ) * (((i + 1 : ℕ) : ℝ) / x.length)⌋₊ = i + 1 := by
    rw [mul_div_cancel₀ _ hk.ne', Nat.floor_natCast]
  have hft : f ⟨_, hmem⟩ = (((x.take (i + 1)).sum : ℤ) : ℝ) / B := by
    rw [hf]
    exact congrArg (fun j => (((x.take j).sum : ℤ) : ℝ) / B) hfloor
  have hz : (⟨0, le_rfl, zero_le_one⟩ : Set.Icc (0 : ℝ) 1) < ⟨_, hmem⟩ := by
    change (0 : ℝ) < ((i + 1 : ℕ) : ℝ) / x.length
    positivity
  have : (𝓝[<] (⟨_, hmem⟩ : Set.Icc (0 : ℝ) 1)).NeBot := nhdsLT_neBot_of_exists_lt ⟨_, hz⟩
  have hleft : Function.leftLim f ⟨_, hmem⟩ = (((x.take i).sum : ℤ) : ℝ) / B := by
    apply leftLim_eq_of_tendsto
    apply tendsto_const_nhds.congr'
    have hmul : Continuous (fun s : Set.Icc (0 : ℝ) 1 => (x.length : ℝ) * (s : ℝ)) := by
      fun_prop
    have hgt : (i : ℝ) < (x.length : ℝ) * ((⟨_, hmem⟩ : Set.Icc (0 : ℝ) 1) : ℝ) := by
      change (i : ℝ) < (x.length : ℝ) * (((i + 1 : ℕ) : ℝ) / x.length)
      rw [mul_div_cancel₀ _ hk.ne']
      push_cast
      linarith
    have hnear : ∀ᶠ s : Set.Icc (0 : ℝ) 1 in 𝓝[<] (⟨_, hmem⟩ : Set.Icc (0 : ℝ) 1),
        (i : ℝ) < (x.length : ℝ) * (s : ℝ) :=
      ((hmul.tendsto _).eventually (lt_mem_nhds hgt)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hnear, self_mem_nhdsWithin] with s hs hst
    have hst' : (s : ℝ) < ((i + 1 : ℕ) : ℝ) / x.length := hst
    have hlt : (x.length : ℝ) * s < ((i + 1 : ℕ) : ℝ) := by
      rw [lt_div_iff₀ hk] at hst'
      linarith
    have hfl : ⌊(x.length : ℝ) * s⌋₊ = i := by
      rw [Nat.floor_eq_iff (mul_nonneg hk.le s.2.1)]
      push_cast at hlt
      exact ⟨hs.le, hlt⟩
    change _ = f s
    rw [hf s, hfl]
  rw [hft, hleft, sum_take_succ, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]
  push_cast
  ring

/-- The largest positive jump of the step path of a word whose largest letter is `M ≥ 0`. -/
private theorem maxJump_eq_of_word {x : List ℤ} {B M : ℝ} (hB : 0 < B) (hM0 : 0 ≤ M)
    (hM : ∀ a ∈ x, (a : ℝ) ≤ M) {i : ℕ} (hi : i < x.length) (hxi : ((x[i] : ℤ) : ℝ) = M)
    (f : Skorokhod.D 1 ℝ)
    (hf : ∀ s : Set.Icc (0 : ℝ) 1, f s = (((x.take ⌊(x.length : ℝ) * s⌋₊).sum : ℤ) : ℝ) / B) :
    Skorokhod.maxJump f = M / B := by
  have : Nonempty (Set.Icc (0 : ℝ) 1) := ⟨⟨0, le_rfl, zero_le_one⟩⟩
  apply le_antisymm
  · unfold Skorokhod.maxJump
    exact ciSup_le fun t =>
      max_le (sub_leftLim_le_of_word hB hM0 hM f hf t) (div_nonneg hM0 hB.le)
  · obtain ⟨t, ht⟩ := exists_jump_eq_of_word hi f hf
    calc M / B = f t - Function.leftLim f t := by rw [ht, hxi]
      _ ≤ max (f t - Function.leftLim f t) 0 := le_max_left _ _
      _ ≤ Skorokhod.maxJump f := le_ciSup (Skorokhod.bddAbove_maxJump f) t

/-! ## The largest letter of the increment word -/

private theorem le_foldr_max {l : List ℕ} {d : ℕ} (hd : d ∈ l) : d ≤ l.foldr max 0 := by
  induction l with
  | nil => simp at hd
  | cons a l ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.1 hd with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

private theorem foldr_max_mem {l : List ℕ} (hl : l ≠ []) : l.foldr max 0 ∈ l := by
  induction l with
  | nil => exact absurd rfl hl
  | cons a l ih =>
    rw [List.foldr_cons]
    by_cases hl' : l = []
    · subst hl'
      simp
    · rcases le_total a (l.foldr max 0) with h | h
      · rw [max_eq_right h]
        exact List.mem_cons_of_mem _ (ih hl')
      · rw [max_eq_left h]
        simp

private theorem le_maxDegree {t : PlaneTree} {d : ℕ} (hd : d ∈ t.degrees) : d ≤ maxDegree t :=
  le_foldr_max hd

private theorem one_le_maxDegree {t : PlaneTree} (h2 : 2 ≤ t.size) : 1 ≤ maxDegree t := by
  cases t with
  | node ts =>
    have hts : 1 ≤ ts.length := by
      cases ts with
      | nil => simp at h2
      | cons _ _ => simp
    have hmem : ts.length ∈ (PlaneTree.node ts).degrees := by
      rw [PlaneTree.degrees_node]
      simp
    exact hts.trans (le_maxDegree hmem)

/-! ## The largest jump of the Łukasiewicz path and the positivity of the limit -/

/-- **Largest jump of the Łukasiewicz path**: `Δ̄(W(τ)) = Δ(τ) - 1` for a finite tree with at least two vertices, at every positive
scale. -/
theorem maxJump_rescaledLuka (τ : LocallyFinite.Tree) (hτ : FiniteVertices τ)
    (h2 : 2 ≤ treeSize τ) {b : ℝ} (hb : 0 < b) :
    Skorokhod.maxJump (rescaledLuka (treeSize τ) b τ) = ((maxDegree (toPlaneTree τ) : ℝ) - 1) / b := by
  rw [rescaledLuka_eq_stepPath τ hτ b]
  obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff τ).2 hτ
  rw [treeIncrements_toLocallyFinite, toPlaneTree_toLocallyFinite]
  rw [treeSize_toLocallyFinite] at h2
  have hdeg_ne : t.degrees ≠ [] := by
    intro h
    have hl := PlaneTree.length_degrees t
    rw [h] at hl
    simp only [List.length_nil] at hl
    omega
  obtain ⟨i, hi, hdi⟩ := List.mem_iff_getElem.1 (foldr_max_mem hdeg_ne)
  have hi' : i < t.increments.length := by
    simpa [PlaneTree.increments] using hi
  have hget : t.increments[i] = ((t.degrees[i] : ℕ) : ℤ) - 1 := by
    simp [PlaneTree.increments]
  refine maxJump_eq_of_word hb ?_ ?_ hi' ?_ _ (fun s => rfl)
  · have h1 := one_le_maxDegree h2
    have h1' : (1 : ℝ) ≤ maxDegree t := by exact_mod_cast h1
    linarith
  · intro a ha
    simp only [PlaneTree.increments, List.mem_map] at ha
    obtain ⟨d, hd, rfl⟩ := ha
    have h1 : (d : ℝ) ≤ maxDegree t := by exact_mod_cast le_maxDegree hd
    push_cast
    linarith
  · rw [hget, hdi]
    simp [maxDegree]

/-- **Theorem 7.1(i), discussion (line 2349)**: the limit `Δ̄(X^exc)` is a.s. positive for `θ < 2`
(BGW `ae_maxJump_pos_levyExcLaw`). -/
theorem thm_max_i_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) :
    ∀ᵐ x : Skorokhod.D 1 ℝ ∂(levyExcLaw θ).toMeasure, 0 < Skorokhod.maxJump x :=
  ae_maxJump_pos_levyExcLaw hθ hθ2

/-! ## Theorem 7.1(i) and the `θ = 2` limit -/

private theorem mu0_toReal_pos {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    0 < (μ 0).toReal :=
  ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (PMF.apply_ne_top μ 0)

/-- Regular variation of the norming in probability: if `M/q_n → c > 0` in probability, then
`B_M/B_{q_n} → c^{1/θ}` in probability (BGW `IsRealStableAttracted.uniform_ratio`). -/
private theorem tendsto_norming_ratio_prob {Ω : Type*} [MeasurableSpace Ω]
    {ν : ProbabilityMeasure ℝ} {θ : ℝ} {B : ℕ → ℝ}
    (hB : IsRealStableAttracted ν θ B) {P : ℕ → ProbabilityMeasure Ω}
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) (M : Ω → ℕ) {c : ℝ} (hc : 0 < c)
    (hM : ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real {ω | ε < |(M ω : ℝ) / q n - c|})
      atTop (𝓝 0)) :
    ∀ ε > 0, Tendsto (fun n => (P n).toMeasure.real
      {ω | ε < |B (M ω) / B (q n) - c ^ (1 / θ)|}) atTop (𝓝 0) := by
  intro ε hε
  obtain ⟨δ, hδ, hlocal⟩ := Metric.continuousAt_iff.mp
    (Real.continuousAt_rpow_const c (1 / θ) (Or.inl hc.ne')) (ε / 2) (half_pos hε)
  let d := min (c / 2) (min 1 (δ / 2))
  have hd : 0 < d := lt_min (half_pos hc) (lt_min zero_lt_one (half_pos hδ))
  obtain ⟨N, hN⟩ := hB.uniform_ratio (show 0 < c / 2 by positivity)
    (show c / 2 ≤ c + 1 by linarith) (ε / 2) (half_pos hε)
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) _ (hM d hd)
  filter_upwards [hq.eventually_ge_atTop N] with n hn
  refine measureReal_mono ?_
  intro ω hω
  have hω' : ε < |B (M ω) / B (q n) - c ^ (1 / θ)| := hω
  change d < |(M ω : ℝ) / q n - c|
  by_contra h
  have habs : |(M ω : ℝ) / q n - c| ≤ d := not_lt.mp h
  have hlow : c / 2 * q n ≤ (M ω : ℝ) := by
    have h := (abs_le.mp habs).1
    have hdle : d ≤ c / 2 := min_le_left _ _
    by_cases hqzero : q n = 0
    · simp [hqzero]
    · have : (0 : ℝ) < q n := by exact_mod_cast Nat.pos_of_ne_zero hqzero
      apply (le_div_iff₀ this).mp
      linarith
  have hhigh : (M ω : ℝ) ≤ (c + 1) * q n := by
    have h := (abs_le.mp habs).2
    have hdle : d ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
    by_cases hqzero : q n = 0
    · have : c ≤ d := by simpa [hqzero, abs_of_pos hc] using habs
      have : d ≤ c / 2 := min_le_left _ _
      linarith
    · have : (0 : ℝ) < q n := by exact_mod_cast Nat.pos_of_ne_zero hqzero
      apply (div_le_iff₀ this).mp
      linarith
  have happrox := hN (q n) hn (M ω) hlow hhigh
  have hrpow : |((M ω : ℝ) / q n) ^ (1 / θ) - c ^ (1 / θ)| < ε / 2 := by
    apply hlocal
    exact habs.trans_lt (lt_of_le_of_lt ((min_le_right _ _).trans (min_le_right _ _))
      (half_lt_self hδ))
  have hh := abs_sub_le (B (M ω) / B (q n)) (((M ω : ℝ) / q n) ^ (1 / θ)) (c ^ (1 / θ))
  linarith

/-- **Theorem 7.1(i) for every index `θ`**: under `P_μ[· | λ = n]`, along admissible `q k`,
`μ₀^{1/θ} Δ(τ_n)/B_n → Δ̄(X^exc)` in law.  Route: see the module docstring (walk part of the coding
only: Theorem 6.1, `ζ/n → 1/μ₀`, regular variation of `B`, Slutsky). -/
theorem tendsto_scaledMaxDegree {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (fun τ => (μ 0).toReal ^ (1 / θ) * (maxDegree (toPlaneTree τ) : ℝ) / B (q k)))
      atTop (𝓝 ((levyExcLaw θ).map Skorokhod.maxJump)) := by
  have hp : 0 < (μ 0).toReal := mu0_toReal_pos hc hne
  have hcpos : 0 < (μ 0).toReal ^ (1 / θ) := Real.rpow_pos_of_pos hp _
  let P : ℕ → ProbabilityMeasure LocallyFinite.Tree := fun k => leafTreeLaw μ (q k)
  let X : LocallyFinite.Tree → Skorokhod.D 1 ℝ := fun τ =>
    rescaledLuka (treeSize τ) (B (treeSize τ)) τ
  have hX : Measurable X := measurable_rescaledLuka_treeSize B
  have hJ : Measurable (Skorokhod.maxJump (T := 1)) :=
    Skorokhod.lipschitzWith_two_maxJump.continuous.measurable
  let Y : LocallyFinite.Tree → ℝ := fun τ => Skorokhod.maxJump (X τ)
  have hY : Measurable Y := hJ.comp hX
  -- Theorem 6.1 and the continuous mapping theorem: `Δ̄(W/B_ζ) → Δ̄(X^exc)`.
  have hlimY : Tendsto (fun k => (P k).map Y) atTop
      (𝓝 ((levyExcLaw θ).map Skorokhod.maxJump)) := by
    have h := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _
      (LeafLimits.Walk.thm_cvW3 hc hne hap hB hnl hqtop hq)
      (Skorokhod.lipschitzWith_two_maxJump (T := 1)).continuous
    refine h.congr fun k => ?_
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map hJ hX]
    rfl
  -- `μ₀^{1/θ} B_ζ/B_n → 1` in probability.
  let R : ℕ → LocallyFinite.Tree → ℝ := fun k τ =>
    (μ 0).toReal ^ (1 / θ) * B (treeSize τ) / B (q k)
  have hR : ∀ k, Measurable (R k) := fun k =>
    (measurable_from_nat (f := fun m => (μ 0).toReal ^ (1 / θ) * B m / B (q k))).comp
      measurable_treeSize
  have hDA := (BGWLeaves.stableDomain_of_isRealStableAttracted hc hne hB).1
  have hratio := tendsto_norming_ratio_prob hB (P := P) hqtop treeSize (one_div_pos.mpr hp)
    (fun ε hε => LeafLimits.Helpers.tendsto_treeSize_div_leaf hc hne hap hDA hqtop hq hε)
  have hcc : (μ 0).toReal ^ (1 / θ) * (1 / (μ 0).toReal) ^ (1 / θ) = 1 := by
    rw [← Real.mul_rpow hp.le (one_div_pos.mpr hp).le, mul_one_div_cancel hp.ne', Real.one_rpow]
  have herrR : ∀ ε > 0, Tendsto (fun k => (P k : Measure LocallyFinite.Tree).real
      {τ | ε < dist (R k τ) 1}) atTop (𝓝 0) := by
    intro ε hε
    refine squeeze_zero (fun _ => measureReal_nonneg) (fun k => measureReal_mono ?_)
      (hratio (ε / (μ 0).toReal ^ (1 / θ)) (div_pos hε hcpos))
    intro τ hτ
    have hτ' : ε < dist (R k τ) 1 := hτ
    have heq : R k τ - 1 = (μ 0).toReal ^ (1 / θ) *
        (B (treeSize τ) / B (q k) - (1 / (μ 0).toReal) ^ (1 / θ)) := by
      rw [mul_sub, hcc]
      simp only [R]
      ring
    rw [Real.dist_eq, heq, abs_mul, abs_of_pos hcpos] at hτ'
    exact (div_lt_iff₀' hcpos).2 hτ'
  -- Slutsky: `(Δ̄(W/B_ζ), μ₀^{1/θ} B_ζ/B_n) → (Δ̄(X^exc), 1)`, then the product.
  have hprod := BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error
    (Ω := fun _ => LocallyFinite.Tree) P (X := fun _ => Y) (Y := R) (fun _ => hY) hR hlimY herrR
  have hmul : Continuous (fun z : ℝ × ℝ => z.2 * z.1) := continuous_snd.mul continuous_fst
  let G : ℕ → LocallyFinite.Tree → ℝ := fun k τ => R k τ * Y τ
  have hG : ∀ k, Measurable (G k) := fun k => (hR k).mul hY
  have hlimG : Tendsto (fun k => (P k).map (G k)) atTop
      (𝓝 ((levyExcLaw θ).map Skorokhod.maxJump)) := by
    have hL : (((levyExcLaw θ).map Skorokhod.maxJump).map (fun x : ℝ => (x, (1 : ℝ)))).map
        (fun z : ℝ × ℝ => z.2 * z.1) = (levyExcLaw θ).map Skorokhod.maxJump := by
      apply ProbabilityMeasure.toMeasure_injective
      simp only [ProbabilityMeasure.toMeasure_map]
      rw [Measure.map_map hmul.measurable
        (show Measurable fun x : ℝ => (x, (1 : ℝ)) from measurable_id.prodMk measurable_const)]
      have hid : ((fun z : ℝ × ℝ => z.2 * z.1) ∘ fun x : ℝ => (x, (1 : ℝ))) = id := by
        funext x
        simp
      rw [hid, Measure.map_id]
    rw [← hL]
    refine (ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hprod hmul).congr
      fun k => ?_
    apply ProbabilityMeasure.toMeasure_injective
    simp only [ProbabilityMeasure.toMeasure_map]
    rw [Measure.map_map hmul.measurable (hY.prodMk (hR k))]
    rfl
  -- The error `μ₀^{1/θ} Δ/B_n - G = μ₀^{1/θ}/B_n` holds almost surely for `n` large.
  refine BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (Ω := fun _ => LocallyFinite.Tree) P
    (F := fun k τ => (μ 0).toReal ^ (1 / θ) * (maxDegree (toPlaneTree τ) : ℝ) / B (q k)) (G := G)
    (fun k => measurable_scaledMaxDegree _ _) hG ?_ hlimG
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp hB.pos
  have hsmall : ∀ᶠ k in atTop, (μ 0).toReal ^ (1 / θ) / B (q k) < ε :=
    ((tendsto_const_nhds (x := (μ 0).toReal ^ (1 / θ))).div_atTop
      (hB.tendsto_norming_atTop.comp hqtop)).eventually (gt_mem_nhds hε)
  apply tendsto_const_nhds.congr'
  filter_upwards [hsmall, hqtop.eventually_ge_atTop (max N 2)] with k hk hkN
  have hzero : (leafTreeLaw μ (q k) : Measure LocallyFinite.Tree)
      {τ | ε < dist ((μ 0).toReal ^ (1 / θ) * (maxDegree (toPlaneTree τ) : ℝ) / B (q k))
        (G k τ)} = 0 := by
    rw [coe_leafTreeLaw (hq k), measure_eq_zero_iff_ae_notMem]
    filter_upwards [ae_cond_mem (measurableSet_leafCountEvent (q k))] with τ hτ
    obtain ⟨t, rfl, ht⟩ := hτ
    intro hmem
    have hmem' : ε < dist ((μ 0).toReal ^ (1 / θ) *
        (maxDegree (toPlaneTree t.toLocallyFinite) : ℝ) / B (q k)) (G k t.toLocallyFinite) := hmem
    have hsize : q k ≤ treeSize t.toLocallyFinite := by
      rw [treeSize_toLocallyFinite]
      exact ht ▸ t.degreeCount_le_size 0
    have h2 : 2 ≤ treeSize t.toLocallyFinite :=
      ((le_max_right N 2).trans hkN).trans hsize
    have hBζ : 0 < B (treeSize t.toLocallyFinite) :=
      hN _ (((le_max_left N 2).trans hkN).trans hsize)
    have hBn : 0 < B (q k) := hN _ ((le_max_left N 2).trans hkN)
    have hjump := maxJump_rescaledLuka t.toLocallyFinite
      (PlaneTree.finiteVertices_toLocallyFinite t) h2 hBζ
    have hdiff : (μ 0).toReal ^ (1 / θ) * (maxDegree (toPlaneTree t.toLocallyFinite) : ℝ) / B (q k)
        - G k t.toLocallyFinite = (μ 0).toReal ^ (1 / θ) / B (q k) := by
      have hG' : G k t.toLocallyFinite = (μ 0).toReal ^ (1 / θ) *
          B (treeSize t.toLocallyFinite) / B (q k) *
          (((maxDegree (toPlaneTree t.toLocallyFinite) : ℝ) - 1) /
            B (treeSize t.toLocallyFinite)) := by
        simp only [G, R, Y, X]
        rw [hjump]
      rw [hG']
      have h1 := hBζ.ne'
      have h3 := hBn.ne'
      field_simp
      ring
    rw [Real.dist_eq, hdiff, abs_of_pos (div_pos hcpos hBn)] at hmem'
    linarith
  change 0 = (leafTreeLaw μ (q k) : Measure LocallyFinite.Tree).real _
  rw [measureReal_def, hzero, ENNReal.toReal_zero]

/-- **Theorem 7.1(i) (`thm:max`, line 2357)**: for `1 < θ < 2`, `μ₀^{1/θ} Δ(τ_n)/B_n → Δ̄(X^exc)` in
law under `P_μ[· | λ = n]`.  (`hθ2` is not needed by the proof: `tendsto_scaledMaxDegree` holds for
every index.) -/
theorem thm_max_i {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) θ B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) (hθ2 : θ < 2) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (fun τ => (μ 0).toReal ^ (1 / θ) * (maxDegree (toPlaneTree τ) : ℝ) / B (q k)))
      atTop (𝓝 ((levyExcLaw θ).map Skorokhod.maxJump)) :=
  tendsto_scaledMaxDegree hc hne hap hB hnl hqtop hq

/-- For `θ = 2` the largest jump of the excursion vanishes almost surely, so its law is `δ_0`
(BGW `ae_maxJump_eq_zero_levyExcLaw_two`). -/
theorem map_maxJump_levyExcLaw_two :
    (levyExcLaw 2).map Skorokhod.maxJump = diracProba (0 : ℝ) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [ProbabilityMeasure.toMeasure_map]
  have hae : (Skorokhod.maxJump (T := 1)) =ᵐ[(levyExcLaw 2 : Measure (Skorokhod.D 1 ℝ))]
      fun _ => (0 : ℝ) := by
    filter_upwards [ae_maxJump_eq_zero_levyExcLaw_two] with x hx
    exact hx.1
  rw [Measure.map_congr hae, Measure.map_const, measure_univ, one_smul]
  rfl

/-- **Discussion before Theorem 7.1 (line 2351)**: for `θ = 2`, `μ₀^{1/2} Δ(τ_n)/B_n → 0` in law. -/
theorem thm_max_two_zero {μ : PMF ℕ} {B : ℕ → ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hB : IsRealStableAttracted (realOffspringStepLaw μ) 2 B)
    (hnl : ¬ IsLatticeLaw (etaLaw μ)) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, LeafAdmissible μ (q k)) :
    Tendsto (fun k => (leafTreeLaw μ (q k)).map
        (fun τ => (μ 0).toReal ^ (1 / 2 : ℝ) * (maxDegree (toPlaneTree τ) : ℝ) / B (q k)))
      atTop (𝓝 (diracProba 0)) := by
  rw [← map_maxJump_levyExcLaw_two]
  exact tendsto_scaledMaxDegree hc hne hap hB hnl hqtop hq

end BGWLeaves.MaxDegreeLimit.Jump
