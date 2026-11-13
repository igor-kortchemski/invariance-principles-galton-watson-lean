/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestBlockLaw
public import BGW.StableTrees.DiscreteForestFirstSuccess
public import BGW.StableTrees.DiscreteForestTreeLaws

/-!
# The first long tree

The iid block law and a finite first-success decomposition identify the first
block with size at least the cutoff. Its selection uses the whole block.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- The inclusive size-tail event, including infinite trees, is measurable. -/
theorem measurableSet_sizeGeEvent (n : ℕ) : MeasurableSet (Attraction.sizeGeEvent n) := by
  have heq : Attraction.sizeGeEvent n = (⋃ k : Fin n, BGW.LocallyFinite.sizeEvent k)ᶜ := by
    ext T
    change (¬BGW.LocallyFinite.FiniteVertices T ∨
      n ≤ {u | BGW.LocallyFinite.Present T u}.ncard) ↔
      T ∉ ⋃ k : Fin n, BGW.LocallyFinite.sizeEvent k
    simp only [mem_iUnion, BGW.LocallyFinite.sizeEvent, mem_ofPred_eq, not_exists]
    constructor
    · rintro (hinf | hn) k hk
      · exact hinf hk.1
      · have hkn := k.isLt
        omega
    · intro h
      by_cases hf : BGW.LocallyFinite.FiniteVertices T
      · right
        by_contra hn
        let k : Fin n := ⟨{u | BGW.LocallyFinite.Present T u}.ncard, by omega⟩
        exact h k ⟨hf, rfl⟩
      · exact Or.inl hf
  rw [heq]
  exact (MeasurableSet.iUnion fun k : Fin n => BGW.LocallyFinite.measurableSet_sizeEvent k).compl

/-- On a finite tree, the inclusive tail event is the ordinary size inequality. -/
theorem toLocallyFinite_mem_sizeGe (t : PlaneTree) (n : ℕ) :
    t.toLocallyFinite ∈ Attraction.sizeGeEvent n ↔ n ≤ t.size := by
  change (¬BGW.LocallyFinite.FiniteVertices t.toLocallyFinite ∨
    n ≤ {u | BGW.LocallyFinite.Present t.toLocallyFinite u}.ncard) ↔ _
  rw [BGW.LocallyFinite.ncard_present_toLocallyFinite]
  exact or_iff_right (not_not_intro t.finiteVertices_toLocallyFinite)

private theorem blockLF_mem_tail {ω : ℕ → ℕ} (hω : LadderFinite ω) (n r : ℕ) :
    blockLF ω r ∈ Attraction.sizeGeEvent n ↔
      n ≤ ladderTime ω (r + 1) - ladderTime ω r := by
  rw [blockLF, toLocallyFinite_mem_sizeGe, size_blockTree hω]

/-- Existence of a long block a.s. (block sizes are iid with unbounded support). -/
theorem ae_exists_long_block (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, ∃ r, n ≤ ladderTime ω (r + 1) - ladderTime ω r := by
  have ha := infinitePi_ae_exists_success (BGW.LocallyFinite.bienaymeLaw μ.toMeasure)
    (measurableSet_sizeGeEvent n) (bienaymeLaw_sizeGeEvent_ne_zero μ hc hne n)
  rw [← blockTrees_law μ hc hne] at ha
  have hb := ae_of_ae_map measurable_blockLF.aemeasurable ha
  filter_upwards [ae_ladderFinite μ hc hne, hb] with ω hω hhit
  obtain ⟨r, hr⟩ := hhit
  exact ⟨r, (blockLF_mem_tail hω n r).mp hr⟩

/-- The first long block is a BGW tree conditioned on size `≥ n`. -/
theorem firstLongTree_law (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    (offspringSeqLaw μ).map (firstLongTree n) = tailTreeLaw μ n := by
  have hQ := measurableSet_sizeGeEvent n
  have hq := bienaymeLaw_sizeGeEvent_ne_zero μ hc hne n
  apply ProbabilityMeasure.toMeasure_injective
  ext A hA
  change ((offspringSeqLaw μ).toMeasure.map (firstLongTree n)) A =
    (tailTreeLaw μ n).toMeasure A
  rw [Measure.map_apply (measurable_firstLongTree n) hA]
  have heq : firstLongTree n ⁻¹' A =ᵐ[(offspringSeqLaw μ).toMeasure]
      (fun ω r => blockLF ω r) ⁻¹' (⋃ r, firstSuccess (Attraction.sizeGeEvent n) A r) := by
    filter_upwards [ae_ladderFinite μ hc hne, ae_exists_long_block μ hc hne n]
      with ω hω hex
    have hhit : n ≤ ladderTime ω (firstLongIndex n ω + 1) -
        ladderTime ω (firstLongIndex n ω) := Nat.sInf_mem hex
    have hbefore (i : ℕ) (hi : i < firstLongIndex n ω) :
        ¬n ≤ ladderTime ω (i + 1) - ladderTime ω i :=
      Nat.notMem_of_lt_sInf
        (s := {r | n ≤ ladderTime ω (r + 1) - ladderTime ω r}) hi
    apply propext
    change blockLF ω (firstLongIndex n ω) ∈ A ↔
      (fun r => blockLF ω r) ∈ ⋃ r, firstSuccess (Attraction.sizeGeEvent n) A r
    constructor
    · intro ha
      apply mem_iUnion.mpr
      refine ⟨firstLongIndex n ω, ⟨?_, ?_⟩⟩
      · exact ⟨(blockLF_mem_tail hω n _).mpr hhit, ha⟩
      · intro i hi hlong
        exact hbefore i hi ((blockLF_mem_tail hω n i).mp hlong)
    · intro ha
      obtain ⟨r, hr⟩ := mem_iUnion.mp ha
      have hlong : n ≤ ladderTime ω (r + 1) - ladderTime ω r :=
        (blockLF_mem_tail hω n r).mp hr.1.1
      have hle : firstLongIndex n ω ≤ r := Nat.sInf_le hlong
      have he : firstLongIndex n ω = r := by
        by_contra hn
        have hlt : firstLongIndex n ω < r := by omega
        exact hr.2 _ hlt ((blockLF_mem_tail hω n _).mpr hhit)
      rw [he]
      exact hr.1.2
  rw [measure_congr heq, ← Measure.map_apply measurable_blockLF
    (MeasurableSet.iUnion (measurableSet_firstSuccess hQ hA)), blockTrees_law μ hc hne,
    infinitePi_firstSuccess_mass _ hQ hA]
  have htail : tailTreeLaw μ n =
      (⟨(BGW.LocallyFinite.bienaymeLaw μ.toMeasure)[|Attraction.sizeGeEvent n],
        cond_isProbabilityMeasure hq⟩ : ProbabilityMeasure BGW.LocallyFinite.Tree) :=
    dite_eq_left hq
  rw [htail]
  exact (cond_apply hQ (BGW.LocallyFinite.bienaymeLaw μ.toMeasure) A).symm

end BGW.StableTrees.DiscreteForest
