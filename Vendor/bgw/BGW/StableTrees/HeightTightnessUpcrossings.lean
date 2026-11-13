/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessRegeneration
import BGW.StableTrees.DiscreteForestFirstSuccess
import BGW.StableTrees.SurvivalDynamics

/-!
# First height upcrossings as integer stopping times

The first integer time at which the forest height reaches a level is determined by
the offspring coordinates strictly before it, and it is almost surely finite for a
critical nondegenerate offspring law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.HeightTightness

/-- First integer time at which the forest height reaches `q`, with value infinity if absent. -/
noncomputable def heightUpcrossingStop (q : ℕ) (ω : ℕ → ℕ) : ℕ∞ :=
  ⨅ k : {k : ℕ // q ≤ forestHeight ω k}, (k.val : ℕ∞)

/-- A finite first upcrossing is characterized by the height at that time and its past. -/
theorem heightUpcrossingStop_eq_natCast_iff (q n : ℕ) (ω : ℕ → ℕ) :
    heightUpcrossingStop q ω = n ↔
      q ≤ forestHeight ω n ∧ ∀ k < n, forestHeight ω k < q := by
  rw [heightUpcrossingStop, ENat.iInf_eq_natCast_iff]
  constructor
  · rintro ⟨⟨⟨k, hk⟩, he⟩, hlo⟩
    have hkn : k = n := ENat.natCast_inj.mp he
    subst k
    refine ⟨hk, fun k hkn => ?_⟩
    by_contra h
    have hh := hlo ⟨k, by omega⟩
    have : n ≤ k := ENat.natCast_le_natCast.mp hh
    omega
  · rintro ⟨hn, hpre⟩
    refine ⟨⟨⟨n, hn⟩, rfl⟩, ?_⟩
    intro k
    apply ENat.natCast_le_natCast.mpr
    by_contra h
    have hh := hpre k.val (by omega)
    exact (not_lt_of_ge k.property) hh

private theorem forestHeight_eq_of_agree {ω ξ : ℕ → ℕ} {n k : ℕ}
    (he : ∀ i < n, ω i = ξ i) (hk : k ≤ n) : forestHeight ω k = forestHeight ξ k := by
  have hw (i : ℕ) (hi : i ≤ n) : walk ω i = walk ξ i := by
    apply Finset.sum_congr rfl
    intro j hj
    rw [he j (by have := Finset.mem_range.mp hj; omega)]
  unfold forestHeight
  congr 1
  apply Finset.filter_congr
  intro j hj
  have hjk := Finset.mem_range.mp hj
  constructor <;> intro hh l hjl hlk
  · rw [← hw j (by omega), ← hw l (by omega)]
    exact hh l hjl hlk
  · rw [hw j (by omega), hw l (by omega)]
    exact hh l hjl hlk

/-- First upcrossings use only the offspring coordinates strictly before the crossing time. -/
theorem isSeqStoppingTime_heightUpcrossingStop (q : ℕ) :
    IsSeqStoppingTime (heightUpcrossingStop q) := by
  intro n ω ξ hn he
  refine ⟨?_, Iff.rfl⟩
  apply (heightUpcrossingStop_eq_natCast_iff q n ξ).mpr
  obtain ⟨hq, hpre⟩ := (heightUpcrossingStop_eq_natCast_iff q n ω).mp hn
  exact ⟨by rwa [← forestHeight_eq_of_agree he le_rfl], fun k hk => by
    rw [← forestHeight_eq_of_agree he hk.le]
    exact hpre k hk⟩

private theorem exists_block_height_of_survival {ω : ℕ → ℕ} (hω : LadderFinite ω)
    {r q : ℕ} (hr : blockLF ω r ∉ BGW.LocallyFinite.extinctBy q) :
    ∃ k, q ≤ forestHeight ω k := by
  change ¬∀ u, BGW.LocallyFinite.Present (blockLF ω r) u → u.length < q at hr
  push Not at hr
  obtain ⟨u, hu, hqu⟩ := hr
  obtain ⟨v, rfl⟩ := BGW.PlaneTree.exists_positiveAddress_of_present hu
  have hv := (BGW.PlaneTree.present_toLocallyFinite (blockTree ω r) v).mp hu
  obtain ⟨i, hi⟩ := List.getElem?_of_mem ((BGW.PlaneTree.mem_vertices_iff _ _).mpr hv)
  have hi' : i < (blockTree ω r).size := by
    simpa only [BGW.PlaneTree.length_vertices] using (List.getElem?_eq_some_iff.mp hi).1
  refine ⟨ladderTime ω r + i, ?_⟩
  rw [forestHeight_eq_treeHeight hω r i hi']
  have he : (blockTree ω r).height ⟨i, hi'⟩ = v.length :=
    congrArg List.length (List.getElem?_eq_some_iff.mp hi).2
  rw [he]
  simpa only [BGW.PlaneTree.positiveAddress, List.length_map] using hqu

/-- Every fixed height is eventually reached almost surely in a critical nondegenerate forest. -/
theorem ae_heightUpcrossingStop_ne_top (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (q : ℕ) : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, heightUpcrossingStop q ω ≠ ⊤ := by
  have hpos : BGW.LocallyFinite.bienaymeLaw μ.toMeasure (BGW.LocallyFinite.extinctBy q)ᶜ ≠ 0 := by
    intro hz
    have hp := Survival.survivalProb_pos hc hne q
    simp only [Survival.survivalProb, Measure.real, hz, ENNReal.toReal_zero] at hp
    exact lt_irrefl _ hp
  have ha := infinitePi_ae_exists_success (BGW.LocallyFinite.bienaymeLaw μ.toMeasure)
    (BGW.LocallyFinite.measurableSet_extinctBy q).compl hpos
  rw [← blockTrees_law μ hc hne] at ha
  have hb := ae_of_ae_map measurable_blockLF.aemeasurable ha
  filter_upwards [ae_ladderFinite μ hc hne, hb] with ω hω hh
  obtain ⟨r, hr⟩ := hh
  obtain ⟨k, hk⟩ := exists_block_height_of_survival hω hr
  have hle : heightUpcrossingStop q ω ≤ (k : ℕ∞) :=
    iInf_le_of_le ⟨k, hk⟩ le_rfl
  exact ne_top_of_le_ne_top (by simp) hle

end BGW.StableTrees.HeightTightness
