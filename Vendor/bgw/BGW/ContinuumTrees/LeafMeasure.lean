/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module
public import BGW.ContinuumTrees.CodingMeasure
public import BGW.ContinuumTrees.ContourComparison
public import BGW.ContinuumTrees.ContourEmbedding
public import BGW.ContinuumTrees.UniformVertexSampling
public import BGW.MetricMeasure.ProkhorovBounds
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Vertex and leaf measures on coded trees

Uniform time is sent to empirical vertex and leaf measures by an explicit quantile map.
A coupling on time pairs controls the Lévy–Prokhorov distance after projection into a coded tree.
The quantile coupling gives discrete bounds, convergence under asymptotic equicontinuity, and a
common-source comparison for finite plane trees. The coded-tree bound is the deterministic core
of comparisons between vertex and leaf measures of large trees (J.-F. Le Gall, Random trees and
applications, Probab. Surveys 2 (2005), Lemma 2.4 for the coding distance; P. Billingsley,
*Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Section 6, for the Prokhorov
distance).
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped ENNReal Topology
open BGW.MetricMeasure BGW.ContinuumTrees.Coding

namespace BGW.ContinuumTrees.LeafMeasure

/-- Time `i / n` of the index `i` among `n` points, as a point of `[0,1]` (clamped). -/
noncomputable def idxTime (n i : ℕ) : unitInterval :=
  Set.projIcc 0 1 zero_le_one ((i : ℝ) / (n : ℝ))

/-- Quantile rank: the index in `{0, …, n-1}` selected by the uniform time `s`
(`⌊n s⌋`, with `s = 1` sent to `n - 1`). -/
noncomputable def rank (n : ℕ) (s : unitInterval) : ℕ :=
  min (Nat.floor ((n : ℝ) * (s : ℝ))) (n - 1)

/-- Uniform measure on the times `i/n`, `i < n` (vertex-time measure). -/
noncomputable def vertexTimeMeasure (n : ℕ) : Measure unitInterval :=
  (n : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range n, Measure.dirac (idxTime n i)

/-- Uniform measure on the times `ℓ k / n`, `k < N` (leaf-time measure). -/
noncomputable def leafTimeMeasure (n N : ℕ) (ℓ : ℕ → ℕ) : Measure unitInterval :=
  (N : ℝ≥0∞)⁻¹ • ∑ k ∈ Finset.range N, Measure.dirac (idxTime n (ℓ k))

instance (n : ℕ) [NeZero n] : IsProbabilityMeasure (vertexTimeMeasure n) := by
  constructor
  simp only [vertexTimeMeasure, Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul,
    mul_one]
  rw [mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_self (by exact_mod_cast NeZero.ne n) (ENNReal.natCast_ne_top n)

instance (n N : ℕ) [NeZero N] (ℓ : ℕ → ℕ) :
    IsProbabilityMeasure (leafTimeMeasure n N ℓ) := by
  constructor
  simp only [leafTimeMeasure, Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul,
    mul_one]
  rw [mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_self (by exact_mod_cast NeZero.ne N) (ENNReal.natCast_ne_top N)

/-- The quantile rank is measurable. -/
theorem measurable_rank (n : ℕ) : Measurable (rank n) := by
  have h : Measurable (fun s : unitInterval => (n : ℝ) * (s : ℝ)) :=
    (continuous_const.mul continuous_subtype_val).measurable
  exact h.nat_floor.min measurable_const

private theorem measurable_idxTime (n : ℕ) : Measurable (idxTime n) :=
  measurable_of_countable _

/-- Quantile ranks of `n` points lie below `n`. -/
theorem rank_lt (n : ℕ) (hn : 0 < n) (s : unitInterval) : rank n s < n := by
  have h := min_le_right (Nat.floor ((n : ℝ) * (s : ℝ))) (n - 1)
  dsimp only [rank]
  omega

/-- Except for the last rank, a quantile fiber is the corresponding half-open cell. -/
theorem rank_fiber_Ico (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i < n - 1) :
    {s : unitInterval | rank n s = i} = Set.Ico (idxTime n i) (idxTime n (i + 1)) := by
  ext s
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ (n : ℝ) * (s : ℝ) := mul_nonneg hnR.le s.property.1
  have hm : rank n s = i ↔ Nat.floor ((n : ℝ) * (s : ℝ)) = i := by
    dsimp only [rank]
    omega
  change rank n s = i ↔
    (idxTime n i : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) < (idxTime n (i + 1) : ℝ)
  have hi0 : 0 ≤ (i : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg _) hnR.le
  have hi1 : (i : ℝ) / (n : ℝ) ≤ 1 := by
    apply (div_le_one₀ hnR).mpr
    exact_mod_cast (show i ≤ n by omega)
  have hj0 : 0 ≤ ((i + 1 : ℕ) : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hnR.le
  have hj1 : ((i + 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
    apply (div_le_one₀ hnR).mpr
    exact_mod_cast (show i + 1 ≤ n by omega)
  simp only [idxTime, Set.coe_projIcc, min_eq_right hi1, max_eq_right hi0,
    min_eq_right hj1, max_eq_right hj0]
  rw [hm, Nat.floor_eq_iff hx0, div_le_iff₀ hnR, lt_div_iff₀ hnR]
  simp only [Nat.cast_add, Nat.cast_one, mul_comm]

/-- The last quantile fiber is the closed final cell. -/
theorem rank_fiber_last (n : ℕ) (hn : 0 < n) :
    {s : unitInterval | rank n s = n - 1} = Set.Icc (idxTime n (n - 1)) 1 := by
  ext s
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ (n : ℝ) * (s : ℝ) := mul_nonneg hnR.le s.property.1
  have hm : rank n s = n - 1 ↔ n - 1 ≤ Nat.floor ((n : ℝ) * (s : ℝ)) := by
    exact min_eq_right_iff
  change rank n s = n - 1 ↔
    (idxTime n (n - 1) : ℝ) ≤ (s : ℝ) ∧ (s : ℝ) ≤ 1
  have hi0 : 0 ≤ ((n - 1 : ℕ) : ℝ) / (n : ℝ) :=
    div_nonneg (Nat.cast_nonneg _) hnR.le
  have hi1 : ((n - 1 : ℕ) : ℝ) / (n : ℝ) ≤ 1 := by
    apply (div_le_one₀ hnR).mpr
    exact_mod_cast Nat.sub_le n 1
  simp only [idxTime, Set.coe_projIcc, min_eq_right hi1, max_eq_right hi0]
  rw [hm, Nat.le_floor_iff hx0, div_le_iff₀ hnR]
  constructor
  · intro h
    exact ⟨by simpa only [mul_comm] using h, s.property.2⟩
  · intro h
    simpa only [mul_comm] using h.1

private theorem idxTime_coe_of_lt (n i : ℕ) (hn : 0 < n) (hi : i < n) :
    (idxTime n i : ℝ) = (i : ℝ) / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hi0 : 0 ≤ (i : ℝ) / (n : ℝ) := div_nonneg (Nat.cast_nonneg _) hnR.le
  have hi1 : (i : ℝ) / (n : ℝ) ≤ 1 := by
    apply (div_le_one₀ hnR).mpr
    exact_mod_cast hi.le
  simp only [idxTime, Set.coe_projIcc, min_eq_right hi1, max_eq_right hi0]

/-- Every quantile fiber has volume `1 / n`. -/
theorem volume_rank_fiber (n : ℕ) (hn : 0 < n) (i : ℕ) (hi : i < n) :
    volume {s : unitInterval | rank n s = i} = (n : ℝ≥0∞)⁻¹ := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  by_cases hlast : i = n - 1
  · subst i
    rw [rank_fiber_last n hn, unitInterval.volume_Icc,
      idxTime_coe_of_lt n (n - 1) hn (by omega)]
    change ENNReal.ofReal (1 - ((n - 1 : ℕ) : ℝ) / (n : ℝ)) = _
    have hm : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
      exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n from hn)
    have hlen : (1 : ℝ) - ((n - 1 : ℕ) : ℝ) / (n : ℝ) = 1 / (n : ℝ) := by
      field_simp
      linarith
    rw [hlen, ENNReal.ofReal_div_of_pos hnR, ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]
  · have hi' : i < n - 1 := by omega
    rw [rank_fiber_Ico n hn i hi', unitInterval.volume_Ico,
      idxTime_coe_of_lt n i hn hi, idxTime_coe_of_lt n (i + 1) hn (by omega)]
    change ENNReal.ofReal (((i + 1 : ℕ) : ℝ) / (n : ℝ) - (i : ℝ) / (n : ℝ)) = _
    have hlen : ((i + 1 : ℕ) : ℝ) / (n : ℝ) - (i : ℝ) / (n : ℝ) =
        1 / (n : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one]
      ring
    rw [hlen, ENNReal.ofReal_div_of_pos hnR, ENNReal.ofReal_one,
      ENNReal.ofReal_natCast, one_div]

/-- Pushing uniform time through `rank n` gives the empirical measure on `Fin n`. -/
theorem map_rank_volume_nat (n : ℕ) (hn : 0 < n) :
    (volume : Measure unitInterval).map (rank n) =
      ∑ i ∈ Finset.range n, (n : ℝ≥0∞)⁻¹ • Measure.dirac i := by
  have he : ∀ᵐ s ∂(volume : Measure unitInterval), rank n s ∈ Finset.range n := by
    filter_upwards with s
    exact Finset.mem_range.mpr (rank_lt n hn s)
  calc
    (volume : Measure unitInterval).map (rank n) =
        ∑ i ∈ Finset.range n, volume (rank n ⁻¹' {i}) • Measure.dirac i :=
      (Measure.ae_mem_finset_iff_map_eq_sum_dirac (measurable_rank n).aemeasurable).mp he
    _ = ∑ i ∈ Finset.range n, (n : ℝ≥0∞)⁻¹ • Measure.dirac i := by
      apply Finset.sum_congr rfl
      intro i hi
      have hvol := volume_rank_fiber n hn i (Finset.mem_range.mp hi)
      change volume {s : unitInterval | rank n s = i} • Measure.dirac i = _
      rw [hvol]

private theorem map_idxTime_sum (n m : ℕ) (f : ℕ → ℕ) :
    (∑ i ∈ Finset.range m, (m : ℝ≥0∞)⁻¹ • Measure.dirac i).map (idxTime n ∘ f) =
      (m : ℝ≥0∞)⁻¹ • ∑ i ∈ Finset.range m, Measure.dirac (idxTime n (f i)) := by
  have hf : Measurable f := measurable_of_countable f
  have hcomp : Measurable (idxTime n ∘ f) := (measurable_idxTime n).comp hf
  calc
    (∑ i ∈ Finset.range m, (m : ℝ≥0∞)⁻¹ • Measure.dirac i).map (idxTime n ∘ f) =
        ∑ i ∈ Finset.range m, (m : ℝ≥0∞)⁻¹ • Measure.dirac (idxTime n (f i)) := by
      rw [Measure.map_finset_sum hcomp.aemeasurable]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Measure.map_smul _ hcomp.aemeasurable, Measure.map_dirac]
      rfl
    _ = _ := by rw [Finset.smul_sum]

/-- The vertex-time measure is the pushforward of Lebesgue measure under the quantile map. -/
theorem map_rank_volume (n : ℕ) (hn : 0 < n) :
    (volume : Measure unitInterval).map (fun s => idxTime n (rank n s)) =
      vertexTimeMeasure n := by
  change (volume : Measure unitInterval).map (idxTime n ∘ rank n) = _
  rw [← Measure.map_map (measurable_idxTime n) (measurable_rank n), map_rank_volume_nat n hn]
  simpa only [Function.comp_id, Function.id_comp, Function.comp_apply, id_eq,
    vertexTimeMeasure] using map_idxTime_sum n n id

/-- The leaf-time measure is the pushforward of Lebesgue measure under the leaf quantile map. -/
theorem map_leafRank_volume (n N : ℕ) (hN : 0 < N) (ℓ : ℕ → ℕ) :
    (volume : Measure unitInterval).map (fun s => idxTime n (ℓ (rank N s))) =
      leafTimeMeasure n N ℓ := by
  change (volume : Measure unitInterval).map ((idxTime n ∘ ℓ) ∘ rank N) = _
  have hℓ : Measurable (idxTime n ∘ ℓ) :=
    (measurable_idxTime n).comp (measurable_of_countable ℓ)
  rw [← Measure.map_map hℓ (measurable_rank N), map_rank_volume_nat N hN]
  simpa only [leafTimeMeasure] using map_idxTime_sum n N ℓ

/-- The selected rank lies within one unit of the unrounded scaled time. -/
theorem rank_cell_bounds (n : ℕ) (hn : 0 < n) (s : unitInterval) :
    (rank n s : ℝ) ≤ (n : ℝ) * (s : ℝ) ∧
      (n : ℝ) * (s : ℝ) ≤ (rank n s : ℝ) + 1 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hx0 : 0 ≤ (n : ℝ) * (s : ℝ) := mul_nonneg hnR.le s.property.1
  have hfloor : rank n s ≤ Nat.floor ((n : ℝ) * (s : ℝ)) := min_le_left _ _
  constructor
  · exact (Nat.cast_le.mpr hfloor).trans (Nat.floor_le hx0)
  · by_cases hcap : Nat.floor ((n : ℝ) * (s : ℝ)) ≤ n - 1
    · have hr : rank n s = Nat.floor ((n : ℝ) * (s : ℝ)) := min_eq_left hcap
      rw [hr]
      exact (Nat.lt_floor_add_one _).le
    · have hr : rank n s = n - 1 := min_eq_right (by omega)
      rw [hr]
      have hm : ((n - 1 : ℕ) : ℝ) + 1 = (n : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel (show 1 ≤ n from hn)
      rw [hm]
      have h := mul_le_mul_of_nonneg_left s.property.2 hnR.le
      simpa only [mul_one] using h

/-- Normalized quantile time differs from the input time by at most `1 / n`. -/
theorem abs_rank_div_sub_time_le (n : ℕ) (hn : 0 < n) (s : unitInterval) :
    |(rank n s : ℝ) / (n : ℝ) - (s : ℝ)| ≤ 1 / (n : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hlo, hhi⟩ := rank_cell_bounds n hn s
  have hleft : (rank n s : ℝ) / (n : ℝ) ≤ (s : ℝ) := by
    apply (div_le_iff₀ hnR).mpr
    simpa only [mul_comm] using hlo
  have hright : (s : ℝ) ≤ (rank n s : ℝ) / (n : ℝ) + 1 / (n : ℝ) := by
    rw [← add_div]
    apply (le_div_iff₀ hnR).mpr
    simpa only [mul_comm] using hhi
  rw [abs_of_nonpos (sub_nonpos.mpr hleft)]
  linarith

/-- Quantile coupling bound: the leaf and vertex quantile times differ by at most
`D + 1/N + 1/n`. -/
theorem abs_idxTime_leaf_sub_vertex_le (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (ℓ : ℕ → ℕ)
    (hℓ : ∀ k < N, ℓ k < n) {D : ℝ}
    (hD : ∀ k < N, |(ℓ k : ℝ) / (n : ℝ) - (k : ℝ) / (N : ℝ)| ≤ D) (s : unitInterval) :
    |(idxTime n (ℓ (rank N s)) : ℝ) - (idxTime n (rank n s) : ℝ)| ≤
      D + 1 / N + 1 / n := by
  have hk := rank_lt N hN s
  have hi := rank_lt n hn s
  rw [idxTime_coe_of_lt n _ hn (hℓ _ hk), idxTime_coe_of_lt n _ hn hi]
  have hfirst : |(ℓ (rank N s) : ℝ) / (n : ℝ) - (s : ℝ)| ≤ D + 1 / N := by
    calc
      |(ℓ (rank N s) : ℝ) / (n : ℝ) - (s : ℝ)| ≤
          |(ℓ (rank N s) : ℝ) / (n : ℝ) - (rank N s : ℝ) / (N : ℝ)| +
            |(rank N s : ℝ) / (N : ℝ) - (s : ℝ)| := abs_sub_le _ _ _
      _ ≤ D + 1 / N := add_le_add (hD _ hk) (abs_rank_div_sub_time_le N hN s)
  have hsecond := abs_rank_div_sub_time_le n hn s
  calc
    |(ℓ (rank N s) : ℝ) / (n : ℝ) - (rank n s : ℝ) / (n : ℝ)| ≤
        |(ℓ (rank N s) : ℝ) / (n : ℝ) - (s : ℝ)| +
          |(rank n s : ℝ) / (n : ℝ) - (s : ℝ)| := by
      rw [abs_sub_comm ((rank n s : ℝ) / (n : ℝ)) (s : ℝ)]
      exact abs_sub_le _ _ _
    _ ≤ D + 1 / N + 1 / n := add_le_add hfirst hsecond

/-- Deterministic coupling estimate. If `π` is a coupling of `μ` and `ν` on `[0,1]²`
giving mass `≤ δ'` to the set `{|s - t| > δ}`, and `g` oscillates by at most `ω` at time scale
`δ`, then the Prokhorov distance of the images in the coded tree is at most `max δ' (2 ω)`. -/
theorem levyProkhorovDist_map_projection_le_of_coupling
    (g : C(unitInterval, ℝ)) (μ ν : Measure unitInterval)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (π : Measure (unitInterval × unitInterval)) (hπ₁ : π.map Prod.fst = μ)
    (hπ₂ : π.map Prod.snd = ν) {δ δ' ω : ℝ} (hδ : 0 ≤ δ) (hδ' : 0 ≤ δ')
    (hbad : π {p | δ < |(p.1 : ℝ) - (p.2 : ℝ)|} ≤ ENNReal.ofReal δ')
    (hω : ∀ u v : unitInterval, |(u : ℝ) - (v : ℝ)| ≤ δ → |g u - g v| ≤ ω) :
    levyProkhorovDist (μ.map (projection g)) (ν.map (projection g)) ≤ max δ' (2 * ω) := by
  let F : unitInterval × unitInterval → Space g := projection g ∘ Prod.fst
  let G : unitInterval × unitInterval → Space g := projection g ∘ Prod.snd
  have hF : Measurable F := (measurable_projection g).comp measurable_fst
  have hG : Measurable G := (measurable_projection g).comp measurable_snd
  have hmapF : π.map F = μ.map (projection g) := by
    change π.map (projection g ∘ Prod.fst) = _
    rw [← hπ₁, Measure.map_map (measurable_projection g) measurable_fst]
  have hmapG : π.map G = ν.map (projection g) := by
    change π.map (projection g ∘ Prod.snd) = _
    rw [← hπ₂, Measure.map_map (measurable_projection g) measurable_snd]
  have hω0 : 0 ≤ ω := by
    have h := hω 0 0 (by simpa using hδ)
    simpa using h
  apply levyProkhorovDist_le_of_forall_le _ _ (hδ'.trans (le_max_left _ _))
  intro ε B hε hB
  rw [← hmapF, ← hmapG, Measure.map_apply hF hB,
    Measure.map_apply hG Metric.isOpen_thickening.measurableSet]
  let T := G ⁻¹' Metric.thickening ε B
  let E := {p : unitInterval × unitInterval | δ < |(p.1 : ℝ) - (p.2 : ℝ)|}
  have hsub : F ⁻¹' B ⊆ T ∪ E := by
    intro p hp
    by_cases hbadp : p ∈ E
    · exact Or.inr hbadp
    · apply Or.inl
      apply Metric.mem_thickening_iff.mpr
      refine ⟨F p, hp, ?_⟩
      have hnear : |(p.1 : ℝ) - (p.2 : ℝ)| ≤ δ := le_of_not_gt hbadp
      have hdist : dist (F p) (G p) ≤ 2 * ω := by
        change dist (projection g p.1) (projection g p.2) ≤ 2 * ω
        rw [dist_projection]
        exact codingDist_le_of_oscillation g hnear hω
      rw [dist_comm]
      exact hdist.trans_lt (lt_of_le_of_lt (le_max_right _ _) hε)
  calc
    π (F ⁻¹' B) ≤ π (T ∪ E) := measure_mono hsub
    _ ≤ π T + π E := measure_union_le _ _
    _ ≤ π T + ENNReal.ofReal δ' := add_le_add_right hbad _
    _ ≤ π T + ENNReal.ofReal ε := add_le_add_right (ENNReal.ofReal_le_ofReal
      ((le_max_left _ _).trans_lt hε).le) _

/-- Discrete estimate: for every continuous coding function `g`, the vertex-time and leaf-time
measures on the coded tree are within `2 ω` in Prokhorov distance, where `ω` bounds the
oscillation
of `g` at time scale `D + 1/N + 1/n`. -/
theorem levyProkhorovDist_vertex_leaf_le (g : C(unitInterval, ℝ)) (n N : ℕ) (hn : 0 < n)
    (hN : 0 < N) (ℓ : ℕ → ℕ) (hℓ : ∀ k < N, ℓ k < n) {D ω : ℝ}
    (hD : ∀ k < N, |(ℓ k : ℝ) / (n : ℝ) - (k : ℝ) / (N : ℝ)| ≤ D)
    (hω : ∀ u v : unitInterval, |(u : ℝ) - (v : ℝ)| ≤ D + 1 / N + 1 / n →
      |g u - g v| ≤ ω) :
    levyProkhorovDist ((vertexTimeMeasure n).map (projection g))
      ((leafTimeMeasure n N ℓ).map (projection g)) ≤ 2 * ω := by
  let F : unitInterval → Space g := fun s => projection g (idxTime n (rank n s))
  let G : unitInterval → Space g := fun s => projection g (idxTime n (ℓ (rank N s)))
  have hF : Measurable F := (measurable_projection g).comp <|
    (measurable_of_countable (idxTime n)).comp (measurable_rank n)
  have hG : Measurable G := (measurable_projection g).comp <|
    (measurable_of_countable (fun k => idxTime n (ℓ k))).comp (measurable_rank N)
  have hmapF : (volume : Measure unitInterval).map F =
      (vertexTimeMeasure n).map (projection g) := by
    change (volume : Measure unitInterval).map
      (projection g ∘ (idxTime n ∘ rank n)) = _
    rw [← Measure.map_map (measurable_projection g)
      ((measurable_of_countable (idxTime n)).comp (measurable_rank n))]
    change Measure.map (projection g)
      (Measure.map (fun s => idxTime n (rank n s)) (volume : Measure unitInterval)) = _
    rw [map_rank_volume n hn]
  have hmapG : (volume : Measure unitInterval).map G =
      (leafTimeMeasure n N ℓ).map (projection g) := by
    change (volume : Measure unitInterval).map
      (projection g ∘ ((fun k => idxTime n (ℓ k)) ∘ rank N)) = _
    rw [← Measure.map_map (measurable_projection g)
      ((measurable_of_countable (fun k => idxTime n (ℓ k))).comp (measurable_rank N))]
    change Measure.map (projection g) (Measure.map
      (fun s => idxTime n (ℓ (rank N s))) (volume : Measure unitInterval)) = _
    rw [map_leafRank_volume n N hN ℓ]
  have hD0 : 0 ≤ D := by
    have h := hD 0 hN
    exact (abs_nonneg _).trans h
  have hscale : 0 ≤ D + 1 / (N : ℝ) + 1 / (n : ℝ) := by positivity
  have hω0 : 0 ≤ ω := by
    have h := hω 0 0 (by simpa using hscale)
    simpa using h
  rw [← hmapF, ← hmapG]
  apply levyProkhorovDist_map_le_of_dist_le volume hF hG (mul_nonneg (by norm_num) hω0)
  intro s
  change dist (projection g (idxTime n (rank n s)))
    (projection g (idxTime n (ℓ (rank N s)))) ≤ 2 * ω
  rw [dist_projection]
  apply codingDist_le_of_oscillation g _ hω
  simpa only [abs_sub_comm] using abs_idxTime_leaf_sub_vertex_le n N hn hN ℓ hℓ hD s

/-- A leaf-index discrepancy bound forces the vertex spacing below the combined scale. -/
theorem one_div_n_le (n N : ℕ) (hn : 0 < n) (hN : 0 < N) (ℓ : ℕ → ℕ)
    (hℓ : ∀ k < N, ℓ k < n) {D : ℝ}
    (hD : ∀ k < N, |(ℓ k : ℝ) / (n : ℝ) - (k : ℝ) / (N : ℝ)| ≤ D) :
    1 / (n : ℝ) ≤ D + 1 / (N : ℝ) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : N - 1 < N := by omega
  have habs := (abs_le.mp (hD (N - 1) hk)).1
  have ha : (ℓ (N - 1) : ℝ) / (n : ℝ) + 1 / (n : ℝ) ≤ 1 := by
    rw [← add_div]
    apply (div_le_one₀ hnR).mpr
    exact_mod_cast (show ℓ (N - 1) + 1 ≤ n from hℓ (N - 1) hk)
  have hNcast : ((N - 1 : ℕ) : ℝ) + 1 = (N : ℝ) := by
    exact_mod_cast Nat.sub_add_cancel hN
  have hb : ((N - 1 : ℕ) : ℝ) / (N : ℝ) + 1 / (N : ℝ) = 1 := by
    rw [← add_div, hNcast]
    exact div_self hNR.ne'
  linarith

/-- Convergence consequence under asymptotic equicontinuity of the coding functions, explicit
leaf-index discrepancy `D j → 0`, and `N j → ∞`. -/
theorem tendsto_levyProkhorovDist_vertex_leaf (g : ℕ → C(unitInterval, ℝ)) (n N : ℕ → ℕ)
    (hn : ∀ j, 0 < n j) (hN : ∀ j, 0 < N j) (ℓ : ℕ → ℕ → ℕ)
    (hℓ : ∀ j, ∀ k < N j, ℓ j k < n j) (D : ℕ → ℝ)
    (hD : ∀ j, ∀ k < N j, |(ℓ j k : ℝ) / (n j : ℝ) - (k : ℝ) / (N j : ℝ)| ≤ D j)
    (hD0 : Tendsto D atTop (𝓝 0)) (hNTop : Tendsto N atTop atTop)
    (hmod : ∀ ε > 0, ∃ δ > 0, ∀ᶠ j in atTop, ∀ u v : unitInterval,
      |(u : ℝ) - (v : ℝ)| ≤ δ → |g j u - g j v| ≤ ε) :
    Tendsto (fun j =>
      levyProkhorovDist ((vertexTimeMeasure (n j)).map (projection (g j)))
        ((leafTimeMeasure (n j) (N j) (ℓ j)).map (projection (g j)))) atTop (𝓝 0) := by
  have hInvN : Tendsto (fun j => 1 / (N j : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ).comp hNTop)
  have hinv_le (j : ℕ) : 1 / (n j : ℝ) ≤ D j + 1 / (N j : ℝ) :=
    one_div_n_le (n j) (N j) (hn j) (hN j) (ℓ j) (hℓ j) (hD j)
  have hInvn : Tendsto (fun j => 1 / (n j : ℝ)) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => by positivity) hinv_le
    simpa using hD0.add hInvN
  have hscale : Tendsto (fun j => D j + 1 / (N j : ℝ) + 1 / (n j : ℝ)) atTop (𝓝 0) := by
    simpa using (hD0.add hInvN).add hInvn
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨δ, hδ, hjmod⟩ := hmod (ε / 3) (by positivity)
  have hsmall : ∀ᶠ j in atTop, D j + 1 / (N j : ℝ) + 1 / (n j : ℝ) < δ :=
    (tendsto_order.1 hscale).2 _ hδ
  obtain ⟨J, hJ⟩ := (hjmod.and hsmall).exists_forall_of_atTop
  refine ⟨J, fun j hj => ?_⟩
  obtain ⟨hj, hjs⟩ := hJ j hj
  have hbound := levyProkhorovDist_vertex_leaf_le (g j) (n j) (N j) (hn j) (hN j)
    (ℓ j) (hℓ j) (hD j) (fun u v huv => hj u v (huv.trans hjs.le))
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (show 0 ≤ levyProkhorovDist
    ((vertexTimeMeasure (n j)).map (projection (g j)))
      ((leafTimeMeasure (n j) (N j) (ℓ j)).map (projection (g j))) from
    ENNReal.toReal_nonneg)]
  exact hbound.trans_lt (by linarith)

/-- The case of uniform convergence of the coding functions `g j → g₀` in `C([0,1])`. -/
theorem tendsto_levyProkhorovDist_vertex_leaf_of_tendsto (g : ℕ → C(unitInterval, ℝ))
    (g₀ : C(unitInterval, ℝ)) (hg : Tendsto g atTop (𝓝 g₀)) (n N : ℕ → ℕ)
    (hn : ∀ j, 0 < n j) (hN : ∀ j, 0 < N j) (ℓ : ℕ → ℕ → ℕ)
    (hℓ : ∀ j, ∀ k < N j, ℓ j k < n j) (D : ℕ → ℝ)
    (hD : ∀ j, ∀ k < N j, |(ℓ j k : ℝ) / (n j : ℝ) - (k : ℝ) / (N j : ℝ)| ≤ D j)
    (hD0 : Tendsto D atTop (𝓝 0)) (hNTop : Tendsto N atTop atTop) :
    Tendsto (fun j =>
      levyProkhorovDist ((vertexTimeMeasure (n j)).map (projection (g j)))
        ((leafTimeMeasure (n j) (N j) (ℓ j)).map (projection (g j)))) atTop (𝓝 0) := by
  apply tendsto_levyProkhorovDist_vertex_leaf g n N hn hN ℓ hℓ D hD hD0 hNTop
  intro ε hε
  obtain ⟨δ, hδ, hg₀⟩ := g₀.uniform_continuity (ε / 3) (by positivity)
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  have hev : ∀ᶠ j in atTop, dist (g j) g₀ < ε / 3 :=
    hg.eventually (Metric.ball_mem_nhds _ (by positivity))
  filter_upwards [hev] with j hj u v huv
  have hu : dist (g j u) (g₀ u) < ε / 3 :=
    (ContinuousMap.dist_apply_le_dist _).trans_lt hj
  have hv : dist (g j v) (g₀ v) < ε / 3 :=
    (ContinuousMap.dist_apply_le_dist _).trans_lt hj
  have h₀uv : dist (g₀ u) (g₀ v) < ε / 3 := by
    apply hg₀
    rw [Subtype.dist_eq, Real.dist_eq]
    exact huv.trans_lt (half_lt_self hδ)
  apply le_of_lt
  calc
    |g j u - g j v| = dist (g j u) (g j v) := (Real.dist_eq _ _).symm
    _ ≤ dist (g j u) (g₀ u) + dist (g₀ u) (g₀ v) + dist (g₀ v) (g j v) := by
      calc
        dist (g j u) (g j v) ≤ dist (g j u) (g₀ u) + dist (g₀ u) (g j v) :=
          dist_triangle _ _ _
        _ ≤ dist (g j u) (g₀ u) + (dist (g₀ u) (g₀ v) + dist (g₀ v) (g j v)) :=
          add_le_add_right (dist_triangle _ _ _) _
        _ = _ := by rw [add_assoc]
    _ < ε / 3 + ε / 3 + ε / 3 := by
      apply add_lt_add (add_lt_add hu h₀uv)
      simpa only [dist_comm] using hv
    _ = ε := by ring

section PlaneTreeAdapter

open BGW.PlaneTree BGW.ContinuumTrees.FiniteTree

/-- A vertex address is a leaf when it has no first child. -/
def IsLeafAddr (t : PlaneTree) (u : List ℕ) : Prop := ¬ t.IsVertex (u ++ [0])

/-- Leaf addresses, in the DFS order of `t.vertices`. -/
noncomputable def leafAddrs (t : PlaneTree) : List (List ℕ) :=
  haveI := Classical.propDecidable
  t.vertices.filter (fun u => decide (IsLeafAddr t u))

/-- Number of leaves (vertices without children). -/
noncomputable def numLeaves (t : PlaneTree) : ℕ := (leafAddrs t).length

/-- The `k`-th leaf in DFS order; junk value `root t` for `k ≥ numLeaves t`. -/
noncomputable def leafVertex (t : PlaneTree) (k : ℕ) : Vertex t :=
  haveI := Classical.propDecidable
  if h : k < numLeaves t then
    ⟨(leafAddrs t)[k]'h, (mem_vertices_iff t _).mp (List.mem_filter.mp (List.getElem_mem h)).1⟩
  else root t

/-- DFS index (position in `t.vertices`) of the `k`-th leaf; junk value `0` (the root's index)
for `k ≥ numLeaves t`. -/
noncomputable def leafIndex (t : PlaneTree) (k : ℕ) : ℕ := t.vertices.idxOf (leafVertex t k).val

/-- Uniform probability on the leaves (`0` if there were no leaf; see `numLeaves_pos`). -/
noncomputable def leafMass (t : PlaneTree) : Measure (Vertex t) :=
  (numLeaves t : ℝ≥0∞)⁻¹ •
    ∑ k ∈ Finset.range (numLeaves t), Measure.dirac (leafVertex t k)

private theorem exists_leaf_mem (t : PlaneTree) :
    ∃ u, u ∈ t.vertices ∧ IsLeafAddr t u := by
  induction t with
  | node ts ih =>
    cases ts with
    | nil => exact ⟨[], by simp, by simp [IsLeafAddr]⟩
    | cons s ss =>
      obtain ⟨u, hu, hleaf⟩ := ih s (by simp)
      refine ⟨0 :: u, ?_, ?_⟩
      · rw [mem_vertices_iff] at hu ⊢
        obtain ⟨r, hr⟩ := hu
        exact ⟨r, by simpa using hr⟩
      · intro hbad
        apply hleaf
        obtain ⟨r, hr⟩ := hbad
        exact ⟨r, by simpa using hr⟩

/-- Every finite plane tree has a leaf. -/
theorem numLeaves_pos (t : PlaneTree) : 0 < numLeaves t := by
  classical
  obtain ⟨u, hu, hleaf⟩ := exists_leaf_mem t
  apply List.length_pos_of_mem (l := leafAddrs t)
  rw [leafAddrs, List.mem_filter]
  exact ⟨hu, decide_eq_true hleaf⟩

/-- A valid leaf index selects the corresponding address in `leafAddrs`. -/
theorem leafVertex_val (t : PlaneTree) {k : ℕ} (hk : k < numLeaves t) :
    (leafVertex t k).val = (leafAddrs t)[k]'hk := by
  classical
  unfold leafVertex
  exact congrArg Subtype.val (dite_eq_left hk)

/-- A valid leaf index selects an address with no first child. -/
theorem leafVertex_isLeaf (t : PlaneTree) {k : ℕ} (hk : k < numLeaves t) :
    IsLeafAddr t (leafVertex t k).val := by
  classical
  rw [leafVertex_val t hk]
  exact of_decide_eq_true (List.mem_filter.mp (List.getElem_mem hk)).2

/-- Every leaf index, including the junk value, is within the finite vertex enumeration. -/
theorem leafIndex_lt_size (t : PlaneTree) (k : ℕ) : leafIndex t k < t.size := by
  rw [← length_vertices]
  exact List.idxOf_lt_length_of_mem ((mem_vertices_iff t _).mpr (leafVertex t k).property)

/-- Valid leaf indices are strictly increasing in DFS order. -/
theorem leafIndex_strictMonoOn (t : PlaneTree) :
    StrictMonoOn (leafIndex t) (Set.Iio (numLeaves t)) := by
  classical
  have hl : t.vertices.Pairwise (fun a b => t.vertices.idxOf a < t.vertices.idxOf b) := by
    rw [List.pairwise_iff_getElem]
    intro i j hi hj hij
    rw [(nodup_vertices t).idxOf_getElem i hi, (nodup_vertices t).idxOf_getElem j hj]
    exact hij
  have hf := hl.filter (fun u => decide (IsLeafAddr t u))
  change (leafAddrs t).Pairwise (fun a b => t.vertices.idxOf a < t.vertices.idxOf b) at hf
  rw [List.pairwise_iff_getElem] at hf
  intro k hk m hm hkm
  change k < numLeaves t at hk
  change m < numLeaves t at hm
  change t.vertices.idxOf (leafVertex t k).val < t.vertices.idxOf (leafVertex t m).val
  rw [leafVertex_val t hk, leafVertex_val t hm]
  exact hf k m hk hm hkm

instance (t : PlaneTree) : IsProbabilityMeasure (leafMass t) := by
  have : NeZero (numLeaves t) := ⟨(numLeaves_pos t).ne'⟩
  constructor
  simp only [leafMass, Measure.smul_apply, smul_eq_mul, Measure.coe_finsetSum,
    Finset.sum_apply, Measure.dirac_apply_of_mem (Set.mem_univ _), Finset.sum_const,
    Finset.card_range, nsmul_eq_mul, mul_one]
  rw [mul_comm, ← div_eq_mul_inv]
  exact ENNReal.div_self (by exact_mod_cast NeZero.ne (numLeaves t))
    (ENNReal.natCast_ne_top (numLeaves t))

/-- Quantile sampling pushes uniform time to the uniform leaf measure. -/
theorem map_leafVertex_rank (t : PlaneTree) :
    (volume : Measure unitInterval).map (fun s => leafVertex t (rank (numLeaves t) s)) =
      leafMass t := by
  have hm : Measurable (leafVertex t) := measurable_of_countable _
  change (volume : Measure unitInterval).map (leafVertex t ∘ rank (numLeaves t)) = _
  rw [← Measure.map_map hm (measurable_rank (numLeaves t)),
    map_rank_volume_nat (numLeaves t) (numLeaves_pos t),
    Measure.map_finset_sum hm.aemeasurable]
  simp_rw [Measure.map_smul _ hm.aemeasurable, Measure.map_dirac]
  rw [leafMass, Finset.smul_sum]

/-- Transfer to a plane tree. The metric of `Vertex t` is the graph metric, for which
`vertexEmbedding t` is an isometry into `Coding.Space t.contourFunction`. The time scale is
`D + 1/N + 2A + 3/n` with `A = ‖c‖ / (2 (n-1))` (`c` the contour function, `n = t.size`,
`N = numLeaves t`), hence at most the threshold in `hω`. -/
theorem levyProkhorovDist_mass_leafMass_le (t : PlaneTree) (hn : 2 ≤ t.size)
    {D ω : ℝ} (hD : ∀ k < numLeaves t,
      |(leafIndex t k : ℝ) / t.size - k / numLeaves t| ≤ D)
    (hω : ∀ u v : unitInterval, |(u : ℝ) - v| ≤ D + 1 / numLeaves t
          + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / t.size →
          |t.contourFunction u - t.contourFunction v| ≤ ω) :
    levyProkhorovDist (mass t : Measure (Vertex t)) (leafMass t) ≤ 2 * ω := by
  have hN : 0 < numLeaves t := numLeaves_pos t
  have hm : Measurable (fun s => leafVertex t (rank (numLeaves t) s)) := by
    exact (measurable_of_countable (leafVertex t)).comp (measurable_rank (numLeaves t))
  have hD0 : 0 ≤ D := by
    have h := hD 0 hN
    exact (abs_nonneg _).trans h
  have hscale : 0 ≤ D + 1 / (numLeaves t : ℝ)
      + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / t.size := by
    positivity
  have hω0 : 0 ≤ ω := by
    have h := hω 0 0 (by simpa using hscale)
    simpa using h
  rw [← map_sampleVertex_volume t, ← map_leafVertex_rank t]
  apply levyProkhorovDist_map_le_of_dist_le volume (measurable_sampleVertex t) hm
    (mul_nonneg (by norm_num) hω0)
  intro s
  let k := rank (numLeaves t) s
  have hk : k < numLeaves t := rank_lt (numLeaves t) hN s
  have hsample := abs_vertexTime_sampleVertex_sub_le t hn s
  have hcell : |(s : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| ≤ 1 / (numLeaves t : ℝ) := by
    simpa only [abs_sub_comm] using abs_rank_div_sub_time_le (numLeaves t) hN s
  have hdepth := t.contourFunction.apply_le_norm (vertexTime t (leafVertex t k))
  rw [contourFunction_vertexTime] at hdepth
  have hden : (0 : ℝ) ≤ 2 * ((t.size - 1 : ℕ) : ℝ) :=
    mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hdepthBound := div_le_div_of_nonneg_right hdepth hden
  have hleaf := abs_vertexTime_sub_dfsTime_le t hn (leafVertex t k)
  change |(vertexTime t (leafVertex t k) : ℝ) -
    (leafIndex t k : ℝ) / (t.size : ℝ)| ≤ _ at hleaf
  have hleafBound : |(leafIndex t k : ℝ) / (t.size : ℝ) -
      (vertexTime t (leafVertex t k) : ℝ)| ≤
      ‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) + 1 / (t.size : ℝ) := by
    rw [abs_sub_comm]
    exact hleaf.trans (add_le_add_left hdepthBound _)
  have htri : |(vertexTime t (sampleVertex t s) : ℝ) -
      (vertexTime t (leafVertex t k) : ℝ)| ≤
      |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| +
        |(s : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| +
        |(k : ℝ) / (numLeaves t : ℝ) - (leafIndex t k : ℝ) / (t.size : ℝ)| +
        |(leafIndex t k : ℝ) / (t.size : ℝ) - (vertexTime t (leafVertex t k) : ℝ)| := by
    calc
      |(vertexTime t (sampleVertex t s) : ℝ) - (vertexTime t (leafVertex t k) : ℝ)| ≤
          |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| +
            |(s : ℝ) - (vertexTime t (leafVertex t k) : ℝ)| := abs_sub_le _ _ _
      _ ≤ |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| +
          (|(s : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| +
            |(k : ℝ) / (numLeaves t : ℝ) - (vertexTime t (leafVertex t k) : ℝ)|) :=
        add_le_add_right (abs_sub_le _ _ _) _
      _ ≤ |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| +
          (|(s : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| +
            (|(k : ℝ) / (numLeaves t : ℝ) - (leafIndex t k : ℝ) / (t.size : ℝ)| +
              |(leafIndex t k : ℝ) / (t.size : ℝ) -
                (vertexTime t (leafVertex t k) : ℝ)|)) := by
        apply add_le_add_right
        apply add_le_add_right
        exact abs_sub_le _ _ _
      _ = _ := by ring
  have hdiscrep : |(k : ℝ) / (numLeaves t : ℝ) -
      (leafIndex t k : ℝ) / (t.size : ℝ)| ≤ D := by
    simpa only [abs_sub_comm] using hD k hk
  have htime : |(vertexTime t (sampleVertex t s) : ℝ) -
      (vertexTime t (leafVertex t k) : ℝ)| ≤ D + 1 / (numLeaves t : ℝ)
      + 2 * (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ))) + 3 / t.size := by
    calc
      _ ≤ |(vertexTime t (sampleVertex t s) : ℝ) - (s : ℝ)| +
          |(s : ℝ) - (k : ℝ) / (numLeaves t : ℝ)| +
          |(k : ℝ) / (numLeaves t : ℝ) - (leafIndex t k : ℝ) / (t.size : ℝ)| +
          |(leafIndex t k : ℝ) / (t.size : ℝ) - (vertexTime t (leafVertex t k) : ℝ)| := htri
      _ ≤ (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) + 2 / (t.size : ℝ)) +
          1 / (numLeaves t : ℝ) + D +
          (‖t.contourFunction‖ / (2 * ((t.size - 1 : ℕ) : ℝ)) + 1 / (t.size : ℝ)) :=
        add_le_add (add_le_add (add_le_add hsample hcell) hdiscrep) hleafBound
      _ = _ := by ring
  have he := (isometry_vertexEmbedding t).dist_eq (sampleVertex t s) (leafVertex t k)
  change codingDist t.contourFunction (vertexTime t (sampleVertex t s))
    (vertexTime t (leafVertex t k)) = dist (sampleVertex t s) (leafVertex t k) at he
  rw [← he]
  exact codingDist_le_of_oscillation t.contourFunction htime hω

end PlaneTreeAdapter

end BGW.ContinuumTrees.LeafMeasure
