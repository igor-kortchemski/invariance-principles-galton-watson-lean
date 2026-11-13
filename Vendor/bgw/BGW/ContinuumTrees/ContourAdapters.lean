/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.ContinuumTrees.ContourLawConvergence
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Adapters for paper contour conventions

The library contour uses duration `2(ζ - 1)`, while the paper uses duration
`2ζ` and sets the contour to zero after its tree has been explored. This
module proves the time-change and law-transfer bounds between these conventions,
measurability for random finite trees, and the divisor estimates from Remark 5.10.

The paper convention is that of I. Kortchemski, *Invariance principles for Galton–Watson trees
conditioned on the number of leaves* (arXiv:1110.2163), with the contour `C_{2ζ s}`; see also
J.-F. Le Gall, *Random trees and applications* (2005), §1. These adapters serve item C38 of
`CLASSICAL_THEORY_INPUTS.md`.
-/

open Filter MeasureTheory Set
open scoped Topology
open BGW.MetricMeasure
open BGW.ContinuumTrees

@[expose] public section

namespace BGW.PlaneTree

/-- The time change `s ↦ min 1 (s ζ/(ζ-1))` turning the library's time scale `2(ζ-1)` into the
paper's `2ζ` (for the singleton tree the factor is `0`, harmless since the contour is `0`). -/
noncomputable def paperTimeChange (t : PlaneTree) : C(unitInterval, unitInterval) where
  toFun s := Set.projIcc 0 1 zero_le_one
    ((s : ℝ) * ((t.size : ℝ) / ((t.size - 1 : ℕ) : ℝ)))
  continuous_toFun := by fun_prop

/-- The contour in the paper's time convention, `s ↦ C_{2ζ s}`. -/
noncomputable def paperContourFunction (t : PlaneTree) : C(unitInterval, ℝ) :=
  t.contourFunction.comp t.paperTimeChange

/-- The time change moves points by at most `1/ζ`. -/
theorem abs_paperTimeChange_sub_le (t : PlaneTree) (s : unitInterval) :
    |((t.paperTimeChange s : unitInterval) : ℝ) - (s : ℝ)| ≤ 1 / (t.size : ℝ) := by
  let z : ℝ := t.size
  have hz : 0 < z := by
    dsimp [z]
    exact_mod_cast size_pos t
  have hz1 : 1 ≤ z := by
    dsimp [z]
    exact_mod_cast (Nat.succ_le_of_lt (size_pos t))
  change |(t.paperTimeChange s : ℝ) - (s : ℝ)| ≤ 1 / z
  by_cases hn : t.size = 1
  · have hq : (t.paperTimeChange s : ℝ) = 0 := by
      simp [paperTimeChange, hn]
    rw [hq, abs_of_nonpos (by nlinarith [s.property.1])]
    simpa [z, hn] using s.property.2
  · have hn2 : 2 ≤ t.size := by
      have hp := size_pos t
      omega
    let m : ℝ := ((t.size - 1 : ℕ) : ℝ)
    have hmpos : 0 < m := by
      dsimp [m]
      exact_mod_cast (show 0 < t.size - 1 by omega)
    have hmadd : m + 1 = z := by
      dsimp [m, z]
      exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ t.size by omega))
    have hs0 : 0 ≤ (s : ℝ) := s.property.1
    have hs1 : (s : ℝ) ≤ 1 := s.property.2
    by_cases hsmall : (s : ℝ) ≤ m / z
    · have hsz : (s : ℝ) * z ≤ m := (le_div_iff₀ hz).mp hsmall
      have hx0 : 0 ≤ (s : ℝ) * (z / m) := by positivity
      have hx1 : (s : ℝ) * (z / m) ≤ 1 := by
        have h' : ((s : ℝ) * z) / m ≤ 1 := (div_le_iff₀ hmpos).2 (by nlinarith [hsz])
        simpa only [mul_div_assoc] using h'
      have hq : (t.paperTimeChange s : ℝ) = (s : ℝ) * (z / m) := by
        simp [paperTimeChange, Set.coe_projIcc, z, m, max_eq_right hx0, min_eq_right hx1]
      have hdiff : (s : ℝ) * (z / m) - (s : ℝ) = (s : ℝ) / m := by
        rw [← hmadd]
        field_simp [hmpos.ne']
        ring
      rw [hq, abs_of_nonneg (by rw [hdiff]; positivity)]
      calc
        (s : ℝ) * (z / m) - (s : ℝ) = (s : ℝ) / m := hdiff
        _ ≤ (m / z) / m := div_le_div_of_nonneg_right hsmall hmpos.le
        _ = 1 / z := by field_simp [hmpos.ne']
    · have hlarge : m / z ≤ (s : ℝ) := le_of_lt (lt_of_not_ge hsmall)
      have hsz : m ≤ (s : ℝ) * z := (div_le_iff₀ hz).mp hlarge
      have hx1 : 1 ≤ (s : ℝ) * (z / m) := by
        have h' : 1 ≤ ((s : ℝ) * z) / m := (le_div_iff₀ hmpos).2 (by nlinarith [hsz])
        simpa only [mul_div_assoc] using h'
      have hq : (t.paperTimeChange s : ℝ) = 1 := by
        change max 0 (min 1 ((s : ℝ) * ((t.size : ℝ) / ((t.size - 1 : ℕ) : ℝ)))) = 1
        have hx1' : 1 ≤ (s : ℝ) * ((t.size : ℝ) / ((t.size - 1 : ℕ) : ℝ)) := by
          simpa [z, m] using hx1
        rw [min_eq_left hx1']
        exact max_eq_right zero_le_one
      rw [hq, abs_of_nonneg (by linarith)]
      apply (le_div_iff₀ hz).2
      nlinarith [hmadd, hsz]

/-- The paper contour vanishes on the last `1/ζ` of the time interval. -/
theorem paperContourFunction_eq_zero (t : PlaneTree) (s : unitInterval)
    (hs : ((t.size - 1 : ℕ) : ℝ) / (t.size : ℝ) ≤ (s : ℝ)) :
    t.paperContourFunction s = 0 := by
  by_cases hn : t.size = 1
  · have hq : t.paperTimeChange s = 0 := by
      apply Subtype.ext
      simp [paperTimeChange, hn]
    rw [paperContourFunction, ContinuousMap.comp_apply, hq]
    exact contourFunction_zero t
  · have hn2 : 2 ≤ t.size := by
      have hp := size_pos t
      omega
    let z : ℝ := t.size
    let m : ℝ := ((t.size - 1 : ℕ) : ℝ)
    have hz : 0 < z := by dsimp [z]; exact_mod_cast size_pos t
    have hmpos : 0 < m := by
      dsimp [m]
      exact_mod_cast (show 0 < t.size - 1 by omega)
    have hsz : m ≤ (s : ℝ) * z := (div_le_iff₀ hz).mp (by
      simpa only [z, m] using hs)
    have hq : t.paperTimeChange s = 1 := by
      have hqv : (t.paperTimeChange s : ℝ) = 1 := by
        change max 0 (min 1 ((s : ℝ) * ((t.size : ℝ) / ((t.size - 1 : ℕ) : ℝ)))) = 1
        have h' : 1 ≤ ((s : ℝ) * z) / m := (le_div_iff₀ hmpos).2 (by nlinarith [hsz])
        have h'' : 1 ≤ (s : ℝ) * ((t.size : ℝ) / ((t.size - 1 : ℕ) : ℝ)) := by
          simpa [z, m, mul_div_assoc] using h'
        rw [min_eq_left h'']
        exact max_eq_right zero_le_one
      exact Subtype.ext hqv
    rw [paperContourFunction, ContinuousMap.comp_apply, hq]
    exact contourFunction_one t

/-- Deterministic uniform bound: if the divided library contour has oscillation `≤ ε` at
scale `1/ζ`, the two conventions are `ε`-close after division by `b`. -/
theorem norm_paperContourFunction_sub_le (t : PlaneTree) (b ε : ℝ)
    (hosc : ∀ s s' : unitInterval, |(s : ℝ) - (s' : ℝ)| ≤ 1 / (t.size : ℝ) →
      |(b⁻¹ • t.contourFunction) s - (b⁻¹ • t.contourFunction) s'| ≤ ε) :
    ‖b⁻¹ • t.paperContourFunction - b⁻¹ • t.contourFunction‖ ≤ ε := by
  rw [ContinuousMap.norm_le_of_nonempty]
  intro s
  rw [Real.norm_eq_abs]
  change |b⁻¹ * t.paperContourFunction s - b⁻¹ * t.contourFunction s| ≤ ε
  simpa only [paperContourFunction, ContinuousMap.comp_apply, ContinuousMap.smul_apply,
    smul_eq_mul] using hosc (t.paperTimeChange s) s
      (by simpa only [abs_sub_comm] using abs_paperTimeChange_sub_le t s)

/-- Deterministic form with the modulus of continuity of an arbitrary compact set `K` of
limit-candidate contours: on `K`, scaled contours with `1/ζ ≤ δ` are `ε`-close in the two
conventions. -/
theorem exists_size_bound_norm_paper_sub_le (K : Set C(unitInterval, ℝ)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ (t : PlaneTree) (b : ℝ), R ≤ (t.size : ℝ) → b⁻¹ • t.contourFunction ∈ K →
      ‖b⁻¹ • t.paperContourFunction - b⁻¹ • t.contourFunction‖ ≤ ε := by
  obtain ⟨δ, hδ, hosc⟩ := exists_uniform_oscillation_of_isCompact K hK hε
  refine ⟨1 / δ, ?_⟩
  intro t b hsize hg
  have hz : 0 < (t.size : ℝ) := by exact_mod_cast size_pos t
  have hscale : 1 / (t.size : ℝ) ≤ δ := by
    apply (div_le_iff₀ hz).2
    have hmul : (1 / δ) * δ ≤ (t.size : ℝ) * δ :=
      mul_le_mul_of_nonneg_right hsize hδ.le
    simpa [hδ.ne', mul_comm] using hmul
  exact norm_paperContourFunction_sub_le t b ε fun s s' hss =>
    hosc (b⁻¹ • t.contourFunction) hg s s' (hss.trans hscale)

/-- Symmetric form: the same bound when the paper contour lies in the compact
set; used by the transfer from the paper convention to the library convention. -/
theorem exists_size_bound_norm_paper_sub_le' (K : Set C(unitInterval, ℝ)) (hK : IsCompact K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ (t : PlaneTree) (b : ℝ), R ≤ (t.size : ℝ) → b⁻¹ • t.paperContourFunction ∈ K →
      ‖b⁻¹ • t.paperContourFunction - b⁻¹ • t.contourFunction‖ ≤ ε := by
  obtain ⟨δ, hδ, hosc⟩ := exists_uniform_oscillation_of_isCompact K hK hε
  refine ⟨max 2 (1 / δ), ?_⟩
  intro t b hsize hg
  have hz : 0 < (t.size : ℝ) := by exact_mod_cast size_pos t
  have hn2 : 2 ≤ t.size := by
    have : (2 : ℝ) ≤ (t.size : ℝ) := (le_max_left _ _).trans hsize
    exact_mod_cast this
  have hscale : 1 / (t.size : ℝ) ≤ δ := by
    apply (div_le_iff₀ hz).2
    have hmul : (1 / δ) * δ ≤ (t.size : ℝ) * δ :=
      mul_le_mul_of_nonneg_right (le_trans (le_max_right _ _) hsize) hδ.le
    simpa [hδ.ne', mul_comm] using hmul
  let z : ℝ := t.size
  let m : ℝ := ((t.size - 1 : ℕ) : ℝ)
  have hzpos : 0 < z := by dsimp [z]; exact_mod_cast size_pos t
  have hmpos : 0 < m := by
    dsimp [m]
    exact_mod_cast (show 0 < t.size - 1 by omega)
  have hmle : m ≤ z := by
    dsimp [m, z]
    exact_mod_cast Nat.sub_le t.size 1
  have hmadd : m + 1 = z := by
    dsimp [m, z]
    exact_mod_cast (Nat.sub_add_cancel (show 1 ≤ t.size by omega))
  have hmdiv : m / z ≤ 1 := (div_le_one hzpos).2 hmle
  rw [ContinuousMap.norm_le_of_nonempty]
  intro s
  rw [Real.norm_eq_abs]
  let u : unitInterval := ⟨(s : ℝ) * (m / z), by
    constructor
    · exact mul_nonneg s.property.1 (div_nonneg (le_of_lt hmpos) hzpos.le)
    · have hprod : (s : ℝ) * (m / z) ≤ 1 * 1 :=
        mul_le_mul s.property.2 hmdiv (by positivity) (by norm_num)
      simpa using hprod⟩
  have hchange : t.paperTimeChange u = s := by
    apply Subtype.ext
    have hmul : (s : ℝ) * (m / z) * (z / m) = (s : ℝ) := by
      field_simp [hmpos.ne', hzpos.ne']
    change Set.projIcc 0 1 zero_le_one ((u : ℝ) *
      ((t.size : ℝ) / ((t.size - 1 : ℕ) : ℝ))) = (s : ℝ)
    rw [show (u : ℝ) * ((t.size : ℝ) / ((t.size - 1 : ℕ) : ℝ)) = (s : ℝ) by
      simpa only [u, z, m] using hmul]
    exact congrArg Subtype.val (Set.projIcc_of_mem zero_le_one s.property)
  have hdist : |(u : ℝ) - (s : ℝ)| ≤ 1 / (t.size : ℝ) := by
    have hdiff : (u : ℝ) - (s : ℝ) = -((s : ℝ) / z) := by
      dsimp [u]
      rw [← hmadd]
      field_simp [hzpos.ne']
      ring
    rw [hdiff, abs_neg, abs_of_nonneg (div_nonneg s.property.1 hzpos.le)]
    exact div_le_div_of_nonneg_right s.property.2 hzpos.le
  have hosc' := hosc (b⁻¹ • t.paperContourFunction) hg s u
    (by simpa only [abs_sub_comm] using hdist.trans hscale)
  change |b⁻¹ * t.paperContourFunction s - b⁻¹ * t.contourFunction s| ≤ ε
  have hval : t.contourFunction s = t.paperContourFunction u := by
    rw [paperContourFunction, ContinuousMap.comp_apply, hchange]
  simpa only [ContinuousMap.smul_apply, smul_eq_mul, hval] using hosc'

end BGW.PlaneTree

namespace BGW.ContinuumTrees.FiniteTree

variable {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]

private theorem tendsto_map_of_tendsto_map_of_size
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (size : (n : ℕ) → Ω n → ℝ)
    (hsize : ∀ R : ℝ, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | size n ω < R}) atTop (𝓝 0))
    {E : Type*} [MeasurableSpace E] [PseudoMetricSpace E] [BorelSpace E]
      [SecondCountableTopology E] [CompleteSpace E] [T2Space E]
    {F G : (n : ℕ) → Ω n → E}
    (hF : ∀ n, Measurable (F n)) (hG : ∀ n, Measurable (G n))
    (hclose : ∀ K : Set E, IsCompact K → ∀ ε > 0, ∃ R : ℝ,
      ∀ n ω, R ≤ size n ω → G n ω ∈ K → dist (F n ω) (G n ω) ≤ ε)
    {ν : ProbabilityMeasure E}
    (hlim : Tendsto (fun n => (μ n).map (G n)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map (F n)) atTop (𝓝 ν) := by
  let P : ℕ → ProbabilityMeasure E := fun n => (μ n).map (G n)
  have hcompact : IsCompact (insert ν (range P)) := hlim.isCompact_insert_range
  have htight := isTightMeasureSet_of_isCompact_closure
    (S := insert ν (range P)) (by
      rw [hcompact.isClosed.closure_eq]
      exact hcompact)
  have herr : ∀ ε > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ε < dist (F n ω) (G n ω)}) atTop (𝓝 0) := by
    intro ε hε
    rw [Metric.tendsto_nhds]
    intro η hη
    obtain ⟨K, hK, hprob⟩ :=
      isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp htight
        (ENNReal.ofReal (η / 2)) (ENNReal.ofReal_pos.mpr (half_pos hη))
    have hKprob (n : ℕ) : (μ n : Measure (Ω n)).real {ω | G n ω ∉ K} ≤ η / 2 := by
      have hmem : (P n : Measure E) ∈
          {((γ : ProbabilityMeasure E) : Measure E) | γ ∈ insert ν (range P)} :=
        ⟨P n, mem_insert_of_mem _ (mem_range_self n), rfl⟩
      have hp := hprob (P n : Measure E) hmem
      change ((μ n : Measure (Ω n)).map (G n)) Kᶜ ≤ ENNReal.ofReal (η / 2) at hp
      rw [Measure.map_apply (hG n) hK.isClosed.measurableSet.compl] at hp
      have hp' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hp
      change ((μ n : Measure (Ω n)) ((G n) ⁻¹' Kᶜ)).toReal ≤ η / 2
      simpa only [ENNReal.toReal_ofReal (half_pos hη).le] using hp'
    obtain ⟨R, hgood⟩ := hclose K hK ε hε
    have htail : ∀ᶠ n in atTop,
        (μ n : Measure (Ω n)).real {ω | size n ω < R} < η / 2 :=
      (hsize R).eventually_lt_const (half_pos hη)
    filter_upwards [htail] with n htailn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
    have hsubset : {ω | ε < dist (F n ω) (G n ω)} ⊆
        {ω | G n ω ∉ K} ∪ {ω | size n ω < R} := by
      intro ω hω
      by_cases hg : G n ω ∈ K
      · right
        by_contra hs
        have h := hgood n ω (le_of_not_gt hs) hg
        exact (not_le_of_gt hω) h
      · exact Or.inl hg
    calc
      _ ≤ (μ n : Measure (Ω n)).real
          ({ω | G n ω ∉ K} ∪ {ω | size n ω < R}) := measureReal_mono hsubset
      _ ≤ (μ n : Measure (Ω n)).real {ω | G n ω ∉ K} +
          (μ n : Measure (Ω n)).real {ω | size n ω < R} := measureReal_union_le _ _
      _ < η := by linarith [hKprob n]
  exact tendsto_probabilityMap_of_error_probability μ hF hG herr hlim

section Measurability

variable {n : ℕ}

/-- Law-level transfer, library convention → paper convention: if the tree sizes tend to
infinity in probability and the divided library contours converge in law to `ν`, so do the
divided paper contours. (The converse, with the roles exchanged, holds by the same proof.) -/
theorem tendsto_map_paperContour_of_tendsto_map_contour
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hF : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).paperContourFunction))
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hsize : ∀ R : ℝ, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ((t n ω).size : ℝ) < R}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).paperContourFunction)) atTop (𝓝 ν) := by
  let _ := hb
  apply tendsto_map_of_tendsto_map_of_size μ (fun n ω => ((t n ω).size : ℝ)) hsize
    hF hG ?_ hlim
  intro K hK ε hε
  obtain ⟨R, hbound⟩ :=
    BGW.PlaneTree.exists_size_bound_norm_paper_sub_le K hK hε
  refine ⟨R, ?_⟩
  intro n ω hlarge hmem
  simpa only [dist_eq_norm] using hbound (t n ω) (b n) hlarge hmem

/-- Law-level transfer, paper convention → library convention: the form consumed by
`tendsto_rooted_laws_of_contour` when the contour input is stated as in the paper. -/
theorem tendsto_map_contour_of_tendsto_map_paperContour
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hF : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).paperContourFunction))
    (hG : ∀ n, Measurable (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction))
    (hsize : ∀ R : ℝ, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ((t n ω).size : ℝ) < R}) atTop (𝓝 0))
    {ν : ProbabilityMeasure C(unitInterval, ℝ)}
    (hlim : Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).paperContourFunction)) atTop (𝓝 ν)) :
    Tendsto (fun n => (μ n).map
      (fun ω : Ω n => (b n)⁻¹ • (t n ω).contourFunction)) atTop (𝓝 ν) := by
  let _ := hb
  apply tendsto_map_of_tendsto_map_of_size μ (fun n ω => ((t n ω).size : ℝ)) hsize
    hG hF ?_ hlim
  intro K hK ε hε
  obtain ⟨R, hbound⟩ :=
    BGW.PlaneTree.exists_size_bound_norm_paper_sub_le' K hK hε
  refine ⟨R, ?_⟩
  intro n ω hlarge hmem
  calc
    dist ((b n)⁻¹ • (t n ω).contourFunction)
        ((b n)⁻¹ • (t n ω).paperContourFunction) =
        dist ((b n)⁻¹ • (t n ω).paperContourFunction)
          ((b n)⁻¹ • (t n ω).contourFunction) := dist_comm _ _
    _ ≤ ε := by
      simpa only [dist_eq_norm] using hbound (t n ω) (b n) hlarge hmem

/-- The size-divergence hypothesis follows from the divisor-to-size tails of
`tendsto_rooted_laws_of_contour` once the divisor tends to infinity. -/
theorem tendsto_real_size_lt_of_ratio
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n))
    (t : (n : ℕ) → Ω n → PlaneTree) (b : ℕ → ℝ) (hb : ∀ n, 0 < b n)
    (hbinfty : Tendsto b atTop atTop)
    (hratio : ∀ r > 0, Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < b n / ((t n ω).size : ℝ)}) atTop (𝓝 0)) (R : ℝ) :
    Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ((t n ω).size : ℝ) < R}) atTop (𝓝 0) := by
  have hlow : ∀ᶠ n in atTop, R ≤ b n / 2 := by
    filter_upwards [hbinfty.eventually_ge_atTop (max R 0 * 2)] with n hn
    have hbn : 0 < b n := hb n
    have hR0 : R ≤ max R 0 := le_max_left _ _
    have hmax0 : 0 ≤ max R 0 := le_max_right _ _
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).2
    nlinarith [hn]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have htail := (hratio 1 (by norm_num : (0 : ℝ) < 1)).eventually_lt_const hε
  filter_upwards [hlow, htail] with n hlown htailn
  have hsubset : {ω | ((t n ω).size : ℝ) < R} ⊆
      {ω | 1 < b n / ((t n ω).size : ℝ)} := by
    intro ω hω
    have hsizepos : 0 < ((t n ω).size : ℝ) := by exact_mod_cast BGW.PlaneTree.size_pos _
    have hsizele : ((t n ω).size : ℝ) < b n / 2 := hω.trans_le hlown
    have hratio : 1 < b n / ((t n ω).size : ℝ) := by
      apply (lt_div_iff₀ hsizepos).2
      nlinarith [hsizele]
    exact hratio
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  calc
    _ ≤ (μ n : Measure (Ω n)).real {ω | 1 < b n / ((t n ω).size : ℝ)} :=
      measureReal_mono hsubset
    _ < ε := htailn

/-! ### measurability hypotheses `hF`, `hG`

`PlaneTree` is countable and carries no global `MeasurableSpace`; random trees are measurable
for the explicit `⊤` σ-algebra, equivalently when every fibre `t ⁻¹' {τ}` is measurable. -/

/-- Measurability for `⊤` on `PlaneTree` is measurability of the fibres of singletons. -/
theorem measurable_top_of_measurableSet_fibre {X : Type*} [MeasurableSpace X]
    (t : X → PlaneTree) (ht : ∀ τ : PlaneTree, MeasurableSet (t ⁻¹' {τ})) :
    @Measurable X PlaneTree _ ⊤ t := by
  classical
  intro s hs
  have hpre : t ⁻¹' s = ⋃ τ : PlaneTree, if τ ∈ s then t ⁻¹' {τ} else ∅ := by
    ext x
    simp
  rw [hpre]
  exact MeasurableSet.iUnion fun τ => by
    split_ifs
    · exact ht τ
    · exact MeasurableSet.empty

/-- Any function of a `⊤`-measurable random tree is measurable (so `hF`, `hG` hold for every
tree observable). -/
theorem measurable_comp_of_top {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (t : X → PlaneTree) (ht : @Measurable X PlaneTree _ ⊤ t) (f : PlaneTree → Y) :
    Measurable (fun x => f (t x)) := by
  intro s hs
  have hset : MeasurableSet[⊤] (f ⁻¹' s) := by simp
  change MeasurableSet (t ⁻¹' (f ⁻¹' s))
  exact ht hset

/-- Hypothesis `hG` of `tendsto_rooted_laws_of_contour`. -/
theorem measurable_contour_of_top (t : Ω n → PlaneTree) (b : ℝ)
    (ht : @Measurable (Ω n) PlaneTree _ ⊤ t) :
    Measurable (fun ω : Ω n => b⁻¹ • (t ω).contourFunction) :=
  measurable_comp_of_top t ht (fun τ => b⁻¹ • τ.contourFunction)

/-- Hypothesis `hG` in the paper's time convention. -/
theorem measurable_paperContour_of_top (t : Ω n → PlaneTree) (b : ℝ)
    (ht : @Measurable (Ω n) PlaneTree _ ⊤ t) :
    Measurable (fun ω : Ω n => b⁻¹ • (t ω).paperContourFunction) :=
  measurable_comp_of_top t ht (fun τ => b⁻¹ • τ.paperContourFunction)

/-- Hypothesis `hF` of `tendsto_rooted_laws_of_contour`. -/
theorem measurable_rootedMeasuredGHSpace_of_top (t : Ω n → PlaneTree) {b : ℝ} (hb : 0 < b)
    (ht : @Measurable (Ω n) PlaneTree _ ⊤ t) :
    Measurable (fun ω : Ω n =>
      RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
        (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace (t ω)))) :=
  measurable_comp_of_top t ht (fun τ =>
    RootedMeasuredGHSpace.scale b⁻¹ (inv_pos.mpr hb)
      (toRootedMeasuredGHSpace (rootedCompactMeasuredSpace τ)))

end Measurability

/-! ### the deterministic divisor of Remark 5.10

`N n` is the (deterministic) number of leaves, `B n` the stable normalizer, `μ₀ > 0` the offspring
mean parameter of the paper, `θ > 0` the stability index; `b n = N n / (μ₀^(1-1/θ) B n)`. -/

/-- The divisor of Remark 5.10. -/
noncomputable def remarkDivisor (μ₀ θ : ℝ) (N : ℕ → ℕ) (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  (N n : ℝ) / (μ₀ ^ (1 - 1 / θ) * B n)

/-- The divisor is positive. -/
theorem remarkDivisor_pos {μ₀ θ : ℝ} (hμ₀ : 0 < μ₀) {N : ℕ → ℕ} {B : ℕ → ℝ}
    (hN : ∀ n, 0 < N n) (hB : ∀ n, 0 < B n) (n : ℕ) :
    0 < remarkDivisor μ₀ θ N B n := by
  unfold remarkDivisor
  apply div_pos
  · exact_mod_cast hN n
  · exact mul_pos (Real.rpow_pos_of_pos hμ₀ _) (hB n)

/-- The divisor tends to infinity when `B n = o(N n)`. -/
theorem tendsto_remarkDivisor_atTop {μ₀ θ : ℝ} (hμ₀ : 0 < μ₀) {N : ℕ → ℕ} {B : ℕ → ℝ}
    (hN : ∀ n, 0 < N n) (hB : ∀ n, 0 < B n) (hNB : Tendsto (fun n => B n / (N n : ℝ)) atTop (𝓝 0)) :
    Tendsto (remarkDivisor μ₀ θ N B) atTop atTop := by
  let A : ℝ := μ₀ ^ (1 - 1 / θ)
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hratio_pos (n : ℕ) : 0 < B n / (N n : ℝ) :=
    div_pos (hB n) (by exact_mod_cast hN n)
  have hratio_within : Tendsto (fun n => B n / (N n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hNB, Filter.Eventually.of_forall hratio_pos⟩
  have hinv : Tendsto (fun n => (B n / (N n : ℝ))⁻¹) atTop atTop :=
    hratio_within.inv_tendsto_nhdsGT_zero
  have hmul : Tendsto (fun n => A⁻¹ * (B n / (N n : ℝ))⁻¹) atTop atTop :=
    hinv.const_mul_atTop (inv_pos.mpr hA)
  have heq (n : ℕ) : remarkDivisor μ₀ θ N B n = A⁻¹ * (B n / (N n : ℝ))⁻¹ := by
    dsimp [remarkDivisor, A]
    have hNn : (N n : ℝ) ≠ 0 := (by exact_mod_cast (hN n).ne')
    have hBn : B n ≠ 0 := (hB n).ne'
    have hAn : μ₀ ^ (1 - 1 / θ) ≠ 0 := (Real.rpow_pos_of_pos hμ₀ _).ne'
    field_simp [hNn, hBn, hAn]
  exact hmul.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)

/-- The ratio hypothesis of `tendsto_rooted_laws_of_contour` for the divisor of Remark 5.10:
if `B n → ∞` and the number of vertices is at least `c N n` with probability tending to one for
each `c < 1/μ₀` (law of large numbers for the vertex/leaf ratio), then
`P(r < b_n/ζ_n) → 0` for every `r > 0`, because `b_n/ζ ≈ μ₀^{1/θ}/B_n`. -/
theorem tendsto_ratio_remarkDivisor
    {μ₀ θ : ℝ} (hμ₀ : 0 < μ₀) {N : ℕ → ℕ} {B : ℕ → ℝ}
    (hN : ∀ n, 0 < N n) (hB : ∀ n, 0 < B n) (hBinfty : Tendsto B atTop atTop)
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) (t : (n : ℕ) → Ω n → PlaneTree)
    (hsize : ∀ c : ℝ, 0 < c → c < 1 / μ₀ → Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | ((t n ω).size : ℝ) < c * (N n : ℝ)}) atTop (𝓝 0)) (r : ℝ) (hr : 0 < r) :
    Tendsto (fun n => (μ n : Measure (Ω n)).real
      {ω | r < remarkDivisor μ₀ θ N B n / ((t n ω).size : ℝ)}) atTop (𝓝 0) := by
  let c : ℝ := 1 / (2 * μ₀)
  let A : ℝ := μ₀ ^ (1 - 1 / θ)
  have hc : 0 < c := by
    dsimp [c]
    positivity
  have hc' : c < 1 / μ₀ := by
    dsimp [c]
    rw [div_lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * μ₀) hμ₀]
    nlinarith [hμ₀]
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hsmallSize := hsize c hc hc'
  have hbound : Tendsto (fun n => (A * c)⁻¹ * (B n)⁻¹) atTop (𝓝 0) :=
    by simpa using tendsto_const_nhds.mul hBinfty.inv_tendsto_atTop
  have hratioBound : Tendsto (fun n => remarkDivisor μ₀ θ N B n /
      (c * (N n : ℝ))) atTop (𝓝 0) := by
    apply hbound.congr'
    filter_upwards with n
    dsimp [remarkDivisor, A]
    have hNn : (N n : ℝ) ≠ 0 := by exact_mod_cast (hN n).ne'
    have hBn : B n ≠ 0 := (hB n).ne'
    have hc0 : c ≠ 0 := hc.ne'
    have hA0 : μ₀ ^ (1 - 1 / θ) ≠ 0 := by
      dsimp [A] at hA
      exact hA.ne'
    field_simp [hNn, hBn, hc0, hA0]
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hratioSmall : ∀ᶠ n in atTop,
      remarkDivisor μ₀ θ N B n / (c * (N n : ℝ)) < r :=
    hratioBound.eventually_lt_const hr
  have hsizeSmall : ∀ᶠ n in atTop,
      (μ n : Measure (Ω n)).real
        {ω | ((t n ω).size : ℝ) < c * (N n : ℝ)} < ε :=
    hsmallSize.eventually_lt_const hε
  filter_upwards [hratioSmall, hsizeSmall] with n hratioSmalln hsizeSmalln
  have hsubset : {ω | r < remarkDivisor μ₀ θ N B n / ((t n ω).size : ℝ)} ⊆
      {ω | ((t n ω).size : ℝ) < c * (N n : ℝ)} := by
    intro ω hω
    by_contra hnot
    have hsize : c * (N n : ℝ) ≤ ((t n ω).size : ℝ) := le_of_not_gt hnot
    have hden : 0 < c * (N n : ℝ) := by
      exact mul_pos hc (by exact_mod_cast hN n)
    have hdiv : 0 ≤ remarkDivisor μ₀ θ N B n :=
      (remarkDivisor_pos hμ₀ hN hB n).le
    have hratioLe : remarkDivisor μ₀ θ N B n / ((t n ω).size : ℝ) ≤
        remarkDivisor μ₀ θ N B n / (c * (N n : ℝ)) :=
      div_le_div_of_nonneg_left hdiv hden hsize
    exact (not_lt_of_ge (le_of_lt (lt_of_le_of_lt hratioLe hratioSmalln))) hω
  rw [Real.dist_eq, sub_zero, abs_of_nonneg measureReal_nonneg]
  calc
    _ ≤ (μ n : Measure (Ω n)).real {ω | ((t n ω).size : ℝ) < c * (N n : ℝ)} :=
      measureReal_mono hsubset
    _ < ε := hsizeSmalln

end BGW.ContinuumTrees.FiniteTree
