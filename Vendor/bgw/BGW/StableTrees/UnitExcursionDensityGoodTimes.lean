/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.UnitExcursionLaw
import BGW.StableTrees.ExcursionMarkov
import BGW.Skorokhod.MeasurableJumps
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Dense good times for the unit excursion law

Fixed jumps of a probability law on càdlàg paths form a countable set.
Removing them yields a countable set meeting every open subinterval of `(0,1)`.

## References

* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- The law of the unit-excursion prefix. -/
noncomputable def unitPrefix (θ : ℝ) (a : ℝ≥0) : Measure (D (a : ℝ) ℝ) :=
  (unitExcursionLaw θ : Measure Excursion).map (excursionRestrict a)

/-- Absence of a fixed jump under the unit law. -/
def NoFixedJumpUnit (θ : ℝ) (t : ℝ≥0) : Prop :=
  ∀ᵐ e ∂(unitExcursionLaw θ : Measure Excursion), Function.leftLim e.path.1 t = e.path.1 t

private theorem measurable_unit_leftLim (t : ℝ≥0) :
    Measurable (fun e : Excursion => Function.leftLim e.path.1 t) := by
  by_cases ht : t = 0
  · subst t
    simpa only [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ => zero_le)] using
      measurable_excursion_eval 0
  · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
    apply measurable_of_tendsto_metrizable (fun n : ℕ =>
      measurable_excursion_eval (t - 1 / (n + 1 : ℝ≥0)))
    apply tendsto_pi_nhds.mpr
    intro e
    have hu : Tendsto (fun n : ℕ => t - 1 / (n + 1 : ℝ≥0)) atTop (𝓝[<] t) := by
      refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
      · simpa only [tsub_zero] using (tendsto_const_nhds (x := t)).sub
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
      · exact Eventually.of_forall fun n => tsub_lt_self htpos (by positivity)
    exact (e.path.2.tendsto_nhdsLT_leftLim t).comp hu

private theorem countable_bad_unit (θ : ℝ) :
    {t : ℝ≥0 | t ≤ 1 ∧ ¬NoFixedJumpUnit θ t}.Countable := by
  classical
  let μ := (unitExcursionLaw θ : Measure Excursion)
  let A : ℕ → ℝ≥0 → Set Excursion := fun n t =>
    {e | t ≤ 1 ∧ 1 / (n + 1 : ℝ) < jumpSize e.path.1 t}
  have hA (n : ℕ) (t : ℝ≥0) : MeasurableSet (A n t) := by
    apply MeasurableSet.inter (MeasurableSet.const _)
    exact measurableSet_lt measurable_const
      (continuous_abs.measurable.comp
        ((measurable_excursion_eval t).sub (measurable_unit_leftLim t)))
  have hfin (n : ℕ) (e : Excursion) : {t | e ∈ A n t}.Finite :=
    finite_setOf_jump_gt_cadlag e.path.2 (by positivity) 1
  have hc (n : ℕ) : {t | μ (A n t) ≠ 0}.Countable :=
    countable_measure_ne_zero_of_point_finite μ (A n) (hA n) (hfin n)
  apply (countable_iUnion hc).mono
  intro t ht
  by_contra hn
  have hzero (n : ℕ) : μ (A n t) = 0 := by
    by_contra hne
    exact hn (mem_iUnion.mpr ⟨n, hne⟩)
  have hbad : {e : Excursion | Function.leftLim e.path.1 t ≠ e.path.1 t} =
      ⋃ n, A n t := by
    ext e
    simp only [mem_ofPred_eq, mem_iUnion, A]
    constructor
    · intro he
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show 0 < jumpSize e.path.1 t from by
        simpa only [jumpSize, abs_pos, sub_ne_zero] using Ne.symm he)
      exact ⟨n, ht.1, hn⟩
    · rintro ⟨n, _, hn⟩ he
      simp [jumpSize, he] at hn
      linarith [show 0 < 1 / (n + 1 : ℝ) by positivity]
  apply ht.2
  rw [NoFixedJumpUnit, ae_iff]
  simpa only [hbad] using measure_iUnion_null hzero

/-- Countably many dense good times. -/
theorem exists_goodTimes_unit {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ G : Set ℝ≥0, G.Countable ∧ G ⊆ Ioo 0 1 ∧
      (∀ x y : ℝ≥0, x < y → y ≤ 1 → ∃ t ∈ G, x < t ∧ t < y) ∧
      ∀ t ∈ G, NoFixedJumpUnit θ t := by
  -- This uses only that the law is a probability measure on càdlàg excursions.
  -- `hθ` is part of the stated interface; the argument does not use it.
  have _hθ := hθ
  let J : Set ℝ≥0 := {t | t ≤ 1 ∧ ¬NoFixedJumpUnit θ t}
  have hJ : (Subtype.val '' J : Set ℝ).Countable := (countable_bad_unit θ).image _
  obtain ⟨H, hHsub, hHc, hHd⟩ := hJ.dense_compl ℝ |>.exists_countable_dense_subset
  let G : Set ℝ≥0 := Real.toNNReal '' (H ∩ Ioo 0 1)
  refine ⟨G, (hHc.mono inter_subset_left).image _, ?_, ?_, ?_⟩
  · rintro t ⟨r, ⟨_, hr⟩, rfl⟩
    exact ⟨Real.toNNReal_pos.mpr hr.1, NNReal.coe_lt_coe.mp (by
      simpa only [Real.coe_toNNReal r hr.1.le, NNReal.coe_one] using hr.2)⟩
  · intro x y hxy hy
    obtain ⟨r, hrH, hr⟩ := hHd.exists_mem_open isOpen_Ioo
      (nonempty_Ioo.mpr (show (x : ℝ) < y from hxy))
    have hr0 : 0 < r := x.2.trans_lt hr.1
    have hr1 : r < 1 := hr.2.trans_le (by exact_mod_cast hy)
    refine ⟨r.toNNReal, ⟨r, ⟨hrH, hr0, hr1⟩, rfl⟩, ?_, ?_⟩
    · apply NNReal.coe_lt_coe.mp
      simpa only [Real.coe_toNNReal r hr0.le] using hr.1
    · apply NNReal.coe_lt_coe.mp
      simpa only [Real.coe_toNNReal r hr0.le] using hr.2
  · rintro t ⟨r, ⟨hrH, hr⟩, rfl⟩
    by_contra hn
    have hrJ : r ∈ Subtype.val '' J := by
      refine ⟨r.toNNReal, ⟨?_, hn⟩, Real.coe_toNNReal r hr.1.le⟩
      apply NNReal.coe_le_coe.mp
      simpa only [Real.coe_toNNReal r hr.1.le, NNReal.coe_one] using hr.2.le
    exact hHsub hrH hrJ

end BGW.StableTrees
