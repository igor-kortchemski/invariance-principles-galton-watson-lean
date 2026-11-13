/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForest
public import BGW.StableTrees.SurvivalBasic
import BGW.StableTrees.DiscreteForestBlockLaw

/-!
# Survival bound for the first height upcrossing

A height reached before the end of the first `l` trees occurs in a block surviving
to the same generation. The block laws and a finite union bound give the unscaled
first-upcrossing estimate used in the discrete regeneration argument.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.HeightTightness

/-- A height in a decoded block forces survival of that block to the same generation. -/
theorem blockLF_not_extinctBy_of_le_height {ω : ℕ → ℕ} (hω : LadderFinite ω)
    {k r q : ℕ} (hr : ladderTime ω r ≤ k) (hk : k < ladderTime ω (r + 1))
    (hq : q ≤ forestHeight ω k) : blockLF ω r ∉ BGW.LocallyFinite.extinctBy q := by
  let t := blockTree ω r
  have hi : k - ladderTime ω r < t.size := by
    dsimp [t]
    rw [size_blockTree hω]
    omega
  have he := forestHeight_eq_treeHeight hω r (k - ladderTime ω r) hi
  rw [Nat.add_sub_of_le hr] at he
  let u := t.vertices[k - ladderTime ω r]'(by simpa only [BGW.PlaneTree.length_vertices]
    using hi)
  have hu : t.IsVertex u := (BGW.PlaneTree.mem_vertices_iff t u).mp
    (List.getElem_mem (by simpa only [BGW.PlaneTree.length_vertices] using hi))
  intro h
  have hb := h (BGW.PlaneTree.positiveAddress u)
    ((BGW.PlaneTree.present_toLocallyFinite t u).mpr hu)
  have hlen : (BGW.PlaneTree.positiveAddress u).length = t.height ⟨_, hi⟩ := by
    simp only [BGW.PlaneTree.positiveAddress, List.length_map, BGW.PlaneTree.height, u]
  rw [hlen, ← he] at hb
  omega

/-- Before the end of the first `l` trees, every height above `q` occurs in a surviving block. -/
theorem exists_surviving_block_of_height {ω : ℕ → ℕ} (hω : LadderFinite ω)
    {k l q : ℕ} (hk : k < ladderTime ω l) (hq : q ≤ forestHeight ω k) :
    ∃ r < l, blockLF ω r ∉ BGW.LocallyFinite.extinctBy q := by
  obtain ⟨r, hr, hr'⟩ := exists_ladderTime_le_lt hω k
  have hm : StrictMono (ladderTime ω) := strictMono_nat_of_lt_succ (ladderTime_lt_succ hω)
  refine ⟨r, ?_, blockLF_not_extinctBy_of_le_height hω hr hr' hq⟩
  exact hm.lt_iff_lt.mp (hr.trans_lt hk)

/-- Every block has the unconditioned BGW survival probability. -/
theorem block_survival_real (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (r q : ℕ) :
    (offspringSeqLaw μ).toMeasure.real
      {ω | blockLF ω r ∉ BGW.LocallyFinite.extinctBy q} = Survival.survivalProb μ q := by
  have he : (offspringSeqLaw μ).toMeasure.map (fun ω => blockLF ω r) =
      BGW.LocallyFinite.bienaymeLaw μ.toMeasure := by
    rw [show (fun ω => blockLF ω r) = (fun a : ℕ → BGW.LocallyFinite.Tree => a r) ∘
      (fun ω i => blockLF ω i) from rfl,
      ← Measure.map_map (measurable_pi_apply r) measurable_blockLF,
      blockTrees_law μ hc hne, Measure.infinitePi_map_eval]
  rw [Survival.survivalProb, ← he]
  simp only [Measure.real]
  rw [Measure.map_apply
    (measurable_blockLF.eval) (BGW.LocallyFinite.measurableSet_extinctBy q).compl]
  rfl

/-- The first height upcrossing is bounded by survival among the first `l` trees and
passage beyond those trees. This is the finite, unscaled regeneration estimate. -/
theorem height_hit_probability_le (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (q m l : ℕ) :
    (offspringSeqLaw μ).toMeasure.real {ω | ∃ k ≤ m, q ≤ forestHeight ω k} ≤
      (l : ℝ) * Survival.survivalProb μ q +
        (offspringSeqLaw μ).toMeasure.real {ω | ladderTime ω l ≤ m} := by
  let P := (offspringSeqLaw μ).toMeasure
  let A : Set (ℕ → ℕ) := ⋃ r ∈ Finset.range l,
    {ω | blockLF ω r ∉ BGW.LocallyFinite.extinctBy q}
  have hsub : ∀ᵐ ω ∂P, ω ∈ {ω | ∃ k ≤ m, q ≤ forestHeight ω k} →
      ω ∈ A ∪ {ω | ladderTime ω l ≤ m} := by
    filter_upwards [ae_ladderFinite μ hc hne] with ω hω hh
    obtain ⟨k, hkm, hq⟩ := hh
    by_cases hl : ladderTime ω l ≤ m
    · exact Or.inr hl
    · obtain ⟨r, hr, hsurv⟩ := exists_surviving_block_of_height hω (l := l) (by omega) hq
      exact Or.inl (Set.mem_iUnion.mpr ⟨r, Set.mem_iUnion.mpr
        ⟨Finset.mem_range.mpr hr, hsurv⟩⟩)
  have hA : P.real A ≤ (l : ℝ) * Survival.survivalProb μ q := by
    calc
      P.real A ≤ ∑ r ∈ Finset.range l,
          P.real {ω | blockLF ω r ∉ BGW.LocallyFinite.extinctBy q} :=
        measureReal_biUnion_finset_le _ _
      _ = _ := by simp only [P, block_survival_real μ hc hne, Finset.sum_const,
        Finset.card_range, nsmul_eq_mul]
  exact (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hsub)).trans
    ((measureReal_union_le _ _).trans (add_le_add hA le_rfl))

end BGW.StableTrees.HeightTightness
