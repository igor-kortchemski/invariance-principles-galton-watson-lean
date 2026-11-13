/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestBlockWords
public import BGW.StableTrees.DiscreteForestMeasurable
import Mathlib.MeasureTheory.Measure.Dirac.Basic

/-!
# The iid law of ladder blocks

Work first on finite plane trees with a module-local discrete measurable
structure. Finite word cylinders give every finite initial joint law, and
projective-limit uniqueness gives the sequence law. Transport then uses the
existing embedding into locally finite trees.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- A discrete structure used only for the countable finite-tree transport. -/
local instance blockLawTreeMeasurable : MeasurableSpace PlaneTree := ⊤
/-- Finite tree singletons are measurable for the local discrete structure. -/
local instance blockLawTreeSingleton : MeasurableSingletonClass PlaneTree := ⟨fun _ => trivial⟩
/-- Degree words also use a local discrete measurable structure. -/
local instance blockLawWordMeasurable : MeasurableSpace (List ℕ) := ⊤
/-- Degree-word singletons are measurable in the local structure. -/
local instance blockLawWordSingleton : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

private noncomputable def finiteTreeMeasure (μ : PMF ℕ) : Measure PlaneTree :=
  Measure.sum fun t => PlaneTree.weight μ t • Measure.dirac t

private theorem finiteTreeMeasure_atom (μ : PMF ℕ) (t : PlaneTree) :
    finiteTreeMeasure μ {t} = PlaneTree.weight μ t := by
  rw [finiteTreeMeasure, Measure.sum_apply _ (measurableSet_singleton _)]
  rw [tsum_eq_single t]
  · simp
  · intro s hs
    simp [hs, Measure.smul_apply]

private theorem finiteTreeMeasure_prob (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    IsProbabilityMeasure (finiteTreeMeasure μ) := by
  constructor
  have h := Scalar.tsum_forestWeight_eq_one hc hne 1
  rw [Scalar.tsum_forestWeight, pow_one] at h
  simpa [finiteTreeMeasure, Measure.sum_apply, Measure.smul_apply] using h

private theorem measurable_blockTree_sequence : Measurable (fun ω r => blockTree ω r) := by
  apply Measurable.of_eval
  intro r
  exact (measurable_of_countable (fun a : List ℕ =>
    (PlaneTree.ofDegrees? a).getD (PlaneTree.node []))).comp (measurable_blockDegrees r)

private theorem block_initial_law (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (r : ℕ) :
    (offspringSeqLaw μ).toMeasure.map (fun ω (i : Fin r) => blockTree ω i) =
      Measure.pi (fun _ : Fin r => finiteTreeMeasure μ) := by
  let := finiteTreeMeasure_prob μ hc hne
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (Measurable.of_eval fun i =>
    measurable_blockTree_sequence.eval) (measurableSet_singleton _), Measure.pi_singleton]
  have heq : {ω | (fun i : Fin r => blockTree ω i) = a} =
      {ω | blockPrefix r ω = List.ofFn a} := by
    ext ω
    change (fun i : Fin r => blockTree ω i) = a ↔
      List.ofFn (fun i : Fin r => blockTree ω i) = List.ofFn a
    exact ⟨congrArg List.ofFn, fun h => List.ofFn_injective h⟩
  change (offspringSeqLaw μ).toMeasure {ω | (fun i : Fin r => blockTree ω i) = a} = _
  rw [heq]
  simp_rw [finiteTreeMeasure_atom]
  simpa only [List.length_ofFn, List.map_ofFn, List.prod_ofFn, Function.comp_def] using
    blockPrefix_mass μ hc hne (List.ofFn a)

private theorem block_sequence_law (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    (offspringSeqLaw μ).toMeasure.map (fun ω r => blockTree ω r) =
      Measure.infinitePi (fun _ : ℕ => finiteTreeMeasure μ) := by
  let := finiteTreeMeasure_prob μ hc hne
  apply IsProjectiveLimit.unique _ (Measure.isProjectiveLimit_infinitePi _)
  intro s
  let N := s.sup id + 1
  have hb (i : s) : i.val < N := by
    have hle : i.val ≤ s.sup id := Finset.le_sup (f := id) i.property
    exact Nat.lt_succ_of_le hle
  let proj (a : Fin N → PlaneTree) (i : s) := a ⟨i.val, hb i⟩
  have hm : Measurable proj := by unfold proj; fun_prop
  have hleft : (Measure.map (fun ω r => blockTree ω r) (offspringSeqLaw μ).toMeasure).map
      s.restrict = ((offspringSeqLaw μ).toMeasure.map
        (fun ω (i : Fin N) => blockTree ω i)).map proj := by
    rw [Measure.map_map (by fun_prop) measurable_blockTree_sequence,
      Measure.map_map hm (Measurable.of_eval fun i =>
        measurable_blockTree_sequence.eval)]
    rfl
  rw [hleft, block_initial_law μ hc hne]
  have hmap := Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : Fin N => finiteTreeMeasure μ)
    (f := fun i : s => (⟨i.val, hb i⟩ : Fin N)) (by
      intro i j hij
      exact Subtype.ext (congrArg Fin.val hij))
  simpa only [Measure.infinitePi_eq_pi] using hmap

private theorem finiteTreeMeasure_map (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    (finiteTreeMeasure μ).map PlaneTree.toLocallyFinite =
      BGW.LocallyFinite.bienaymeLaw μ.toMeasure := by
  let := finiteTreeMeasure_prob μ hc hne
  have hm : Measurable PlaneTree.toLocallyFinite :=
    BGW.LocallyFinite.measurableEmbedding_toLocallyFinite.measurable
  have hmass : BGW.LocallyFinite.bienaymeLaw μ.toMeasure
      {T | BGW.LocallyFinite.FiniteVertices T} = 1 := by
    rw [BGW.LocallyFinite.bienaymeLaw_finiteVertices]
    have h := Scalar.tsum_forestWeight_eq_one hc hne 1
    rw [Scalar.tsum_forestWeight, pow_one] at h
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using h
  have hae := (mem_ae_iff_prob_eq_one BGW.LocallyFinite.measurableSet_finiteVertices).mpr hmass
  have hr := Measure.restrict_eq_self_of_ae_mem
    (s := {T | BGW.LocallyFinite.FiniteVertices T}) hae
  ext A hA
  rw [Measure.map_apply hm hA,
    ← Measure.tsum_indicator_apply_singleton (finiteTreeMeasure μ) _ (hA.preimage hm)]
  conv_rhs => rw [← hr, BGW.LocallyFinite.bienaymeLaw_restrict_finiteVertices,
    Measure.sum_apply _ hA]
  apply tsum_congr
  intro t
  rw [Measure.smul_apply, Measure.dirac_apply' _ hA]
  simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _), smul_eq_mul]
  by_cases ht : t.toLocallyFinite ∈ A
  · rw [Set.indicator_of_mem (show t ∈ PlaneTree.toLocallyFinite ⁻¹' A from ht),
      finiteTreeMeasure_atom, Set.indicator_of_mem ht, Pi.one_apply, mul_one]
  · rw [Set.indicator_of_notMem (show t ∉ PlaneTree.toLocallyFinite ⁻¹' A from ht),
      Set.indicator_of_notMem ht, mul_zero]

/-- The blocks of the walk are iid BGW trees:
`(blockLF ω r)_r ~ (bienaymeLaw μ)^{⊗ ℕ}`. Finite degree-word cylinders and the
finite-tree atom formula identify all finite-dimensional laws. -/
theorem blockTrees_law (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ((offspringSeqLaw μ).toMeasure).map (fun ω r => blockLF ω r) =
      Measure.infinitePi (fun _ : ℕ => BGW.LocallyFinite.bienaymeLaw μ.toMeasure) := by
  let := finiteTreeMeasure_prob μ hc hne
  have hm : Measurable (fun a : ℕ → PlaneTree => fun r => (a r).toLocallyFinite) :=
    Measurable.of_eval fun r =>
      BGW.LocallyFinite.measurableEmbedding_toLocallyFinite.measurable.comp
        (measurable_pi_apply r)
  rw [show (fun ω r => blockLF ω r) =
    (fun a : ℕ → PlaneTree => fun r => (a r).toLocallyFinite) ∘
      (fun ω r => blockTree ω r) from rfl,
    ← Measure.map_map hm measurable_blockTree_sequence, block_sequence_law μ hc hne,
    Measure.infinitePi_map_pi]
  · simp_rw [finiteTreeMeasure_map μ hc hne]
  · exact fun _ => BGW.LocallyFinite.measurableEmbedding_toLocallyFinite.measurable

end BGW.StableTrees.DiscreteForest
