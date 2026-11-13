module

public import BGWLeaves.GeneralAFunctional.TreePrefixMeasure

/-! Almost-sure support of finite deterministic degree prefixes. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreePrefixSupport

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.GeneralAFunctional.TreePrefixMeasure
open scoped ENNReal Classical

local instance : MeasurableSpace (List ℕ) := ⊤
local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

theorem ae_tail_good_prefix (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {r m : ℕ} (hmr : m < r) :
    ∀ᵐ T ∂(tailTreeLaw μ r).toMeasure, treePrefix m T ∈ goodWords m := by
  have hs : ∀ᵐ T ∂(tailTreeLaw μ r).toMeasure, T ∈ Attraction.sizeGeEvent r := by
    rw [tailTreeLaw_toMeasure μ r (bienaymeLaw_sizeGeEvent_ne_zero μ hc hne r)]
    exact ae_cond_mem (measurableSet_sizeGeEvent r)
  filter_upwards [ae_tail_finite μ hc hne r, hs] with T hT hsT
  obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff T).mpr hT
  have hrt : r ≤ t.size := (toLocallyFinite_mem_sizeGe t r).mp hsT
  exact good_prefix_of_lt_size t (hmr.trans_le hrt)

theorem ae_prefix_supported (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (m : ℕ) :
    ∀ᵐ T ∂bienaymeLaw μ.toMeasure, ∀ d ∈ treePrefix m T, μ d ≠ 0 := by
  have hdeg : ∀ᵐ d ∂μ.toMeasure, μ d ≠ 0 := by
    apply ae_iff_of_countable.mpr
    intro d hd
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hd
  have hall : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, ∀ i, μ (ω i) ≠ 0 := by
    apply ae_all_iff.mpr
    intro i
    exact (measurePreserving_eval_infinitePi (μ := fun _ : ℕ => μ.toMeasure) i).quasiMeasurePreserving.ae hdeg
  have hmeas : MeasurableSet {T : LocallyFinite.Tree | ∀ d ∈ treePrefix m T, μ d ≠ 0} :=
    (measurable_treePrefix m) (Set.to_countable {a : List ℕ | ∀ d ∈ a, μ d ≠ 0}).measurableSet
  rw [← first_block_law μ hc hne]
  apply (ae_map_iff measurable_blockLF.eval.aemeasurable hmeas).mpr
  filter_upwards [ae_ladderFinite μ hc hne, hall] with ω hω hsupport
  intro d hd
  rw [blockLF, treePrefix_toLocallyFinite, degrees_blockTree hω] at hd
  have hd' := List.mem_of_mem_take hd
  simp only [blockDegrees, DiscreteForest.ladderTime_zero, Nat.sub_zero, zero_add] at hd'
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd'
  exact hsupport i

theorem ae_tail_prefix_supported (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (r m : ℕ) : ∀ᵐ T ∂(tailTreeLaw μ r).toMeasure, ∀ d ∈ treePrefix m T, μ d ≠ 0 := by
  rw [tailTreeLaw_toMeasure μ r (bienaymeLaw_sizeGeEvent_ne_zero μ hc hne r)]
  exact cond_absolutelyContinuous.ae_le (ae_prefix_supported μ hc hne m)

end BGWLeaves.GeneralAFunctional.TreePrefixSupport
