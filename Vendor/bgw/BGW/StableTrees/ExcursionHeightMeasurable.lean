/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightBasic
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Borel reconstruction from almost every age

The version relation is Borel and has at most one continuous version in every section.
Projection of its graph is a measurable embedding, giving a measurable inverse on its image.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A Borel relation with unique sections has a Borel existence event and totalized choice. -/
theorem measurable_unique_version {Ω X : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    [MeasurableSpace X] [StandardBorelSpace X] [MeasurableSpace.CountablySeparated Ω]
    (R : Ω → X → Prop) (hR : MeasurableSet {p : Ω × X | R p.1 p.2})
    (huniq : ∀ ω x y, R ω x → R ω y → x = y) (z : X) :
    MeasurableSet {ω | ∃ x, R ω x} ∧
      Measurable (fun ω => if h : ∃ x, R ω x then Classical.choose h else z) := by
  let S : Set (Ω × X) := {p | R p.1 p.2}
  let : StandardBorelSpace S := hR.standardBorel
  let E (p : S) : Ω := p.1.1
  have hE : MeasurableEmbedding E :=
    (measurable_fst.comp measurable_subtype_coe).measurableEmbedding (by
      intro p q hpq
      apply Subtype.ext
      have he : p.1.1 = q.1.1 := hpq
      have hq : R p.1.1 q.1.2 := by rw [he]; exact q.2
      exact Prod.ext he (huniq p.1.1 p.1.2 q.1.2 p.2 hq))
  have hrange : range E = {ω | ∃ x, R ω x} := by
    ext ω
    constructor
    · rintro ⟨p, rfl⟩
      exact ⟨p.1.2, p.2⟩
    · rintro ⟨x, hx⟩
      exact ⟨⟨(ω, x), hx⟩, rfl⟩
  have hex : MeasurableSet {ω | ∃ x, R ω x} := hrange ▸ hE.measurableSet_range
  refine ⟨hex, ?_⟩
  by_cases hS : Nonempty S
  · let : Nonempty S := hS
    have hm : Measurable (fun ω =>
        if ω ∈ range E then (hE.invFun ω).1.2 else z) :=
      Measurable.ite hE.measurableSet_range
        (measurable_snd.comp (measurable_subtype_coe.comp hE.measurable_invFun)) measurable_const
    convert hm using 1
    funext ω
    by_cases h : ∃ x, R ω x
    · rw [dite_eq_left h, ite_eq_left (hrange.symm ▸ h)]
      have hleft := hE.leftInverse_invFun (⟨(ω, Classical.choose h), Classical.choose_spec h⟩ : S)
      exact (congrArg (fun p : S => p.1.2) hleft).symm
    · rw [dite_eq_right h, ite_eq_right (by rwa [hrange])]
  · have hnone (ω : Ω) : ¬ ∃ x, R ω x := by
      rintro ⟨x, hx⟩
      exact hS ⟨⟨(ω, x), hx⟩⟩
    simpa only [dite_eq_right (hnone _)] using (measurable_const : Measurable (fun _ : Ω => z))

/-- Almost-everywhere membership in a Borel section is a measurable condition. -/
theorem measurableSet_ae_real_section {Ω : Type*} [MeasurableSpace Ω]
    {S : Set (Ω × ℝ)} (hS : MeasurableSet S) :
    MeasurableSet {ω | ∀ᵐ s : ℝ ∂volume, (ω, s) ∈ S} := by
  change MeasurableSet {ω | volume {s : ℝ | ¬ (ω, s) ∈ S} = 0}
  exact measurableSet_eq_fun (measurable_measure_prodMk_left hS.compl) measurable_const

private theorem continuous_zero_on_tail (g : C(ℝ≥0, ℝ)) (a : ℝ≥0)
    (hg : ∀ t : ℝ≥0, a ≤ t → IsRationalTime t → g t = 0) :
    ∀ t : ℝ≥0, a ≤ t → g t = 0 := by
  have hd : Dense {t : Set.Ici a | IsRationalTime t} := by
    apply dense_iff_exists_between.mpr
    intro b c hbc
    obtain ⟨q, hbq, hqc⟩ := exists_rat_btwn (show (b.1 : ℝ) < c.1 from hbc)
    have hq : 0 ≤ (q : ℝ) := b.1.2.trans hbq.le
    exact ⟨⟨⟨q, hq⟩, b.2.trans hbq.le⟩, ⟨q, rfl⟩, hbq, hqc⟩
  have he : (fun t : Set.Ici a => g t) = fun _ => (0 : ℝ) :=
    Continuous.ext_on hd (g.continuous.comp continuous_subtype_val) continuous_const
      (fun t ht => hg t t.2 ht)
  intro t ht
  exact congrFun he ⟨t, ht⟩

private theorem tail_zero_iff (e : Excursion) (g : C(ℝ≥0, ℝ)) :
    (∀ t : ℝ≥0, e.lifetime ≤ t → g t = 0) ↔
      ∀ q : ℚ, e.lifetime ≤ (q : ℝ).toNNReal → g (q : ℝ).toNNReal = 0 := by
  constructor
  · exact fun h q hq => h _ hq
  · intro h
    apply continuous_zero_on_tail
    intro t ht hqt
    obtain ⟨q, hq⟩ := hqt
    simpa only [hq, Real.toNNReal_coe] using h q (by simpa only [hq, Real.toNNReal_coe])

/-- The relation between an excursion and its a.e.-age version is Borel. -/
theorem measurableSet_isExcursionHeightVersion (θ : ℝ) :
    MeasurableSet {p : Excursion × C(ℝ≥0, ℝ) | IsExcursionHeightVersion θ p.1 p.2} := by
  have hzero : MeasurableSet {p : Excursion × C(ℝ≥0, ℝ) | p.2 0 = 0} :=
    measurableSet_eq_fun ((ContinuousMap.measurable_eval 0).comp measurable_snd) measurable_const
  have htail : MeasurableSet {p : Excursion × C(ℝ≥0, ℝ) |
      ∀ q : ℚ, p.1.lifetime ≤ (q : ℝ).toNNReal → p.2 (q : ℝ).toNNReal = 0} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro q
    have hA : MeasurableSet {p : Excursion × C(ℝ≥0, ℝ) |
        p.1.lifetime ≤ (q : ℝ).toNNReal} :=
      measurableSet_le (measurable_excursion_lifetime.comp measurable_fst) measurable_const
    have hB : MeasurableSet {p : Excursion × C(ℝ≥0, ℝ) |
        p.2 (q : ℝ).toNNReal = 0} :=
      measurableSet_eq_fun ((ContinuousMap.measurable_eval _).comp measurable_snd)
        measurable_const
    convert hA.compl.union hB using 1
    ext p
    exact imp_iff_not_or
  have hraw : Measurable (fun p : (Excursion × C(ℝ≥0, ℝ)) × ℝ =>
      heightUniv θ p.1.1.path p.2.toNNReal) :=
    Measurable.comp (g := fun p : ℝ≥0 × DLoc => heightUniv θ p.2 p.1)
      (f := fun p : (Excursion × C(ℝ≥0, ℝ)) × ℝ => (p.2.toNNReal, p.1.1.path))
      (measurable_heightUniv_uncurry θ)
      ((measurable_real_toNNReal.comp measurable_snd).prodMk
        (measurable_excursion_path.comp (measurable_fst.comp measurable_fst)))
  have heval : Measurable (fun p : (Excursion × C(ℝ≥0, ℝ)) × ℝ =>
      p.1.2 p.2.toNNReal) := by
    have hm : Measurable (fun p : ℝ × (Excursion × C(ℝ≥0, ℝ)) =>
        p.2.2 p.1.toNNReal) := measurable_uncurry_of_continuous_of_measurable
      (fun p : Excursion × C(ℝ≥0, ℝ) =>
        p.2.continuous.comp continuous_real_toNNReal)
      (fun s : ℝ => (ContinuousMap.measurable_eval s.toNNReal).comp measurable_snd)
    exact hm.comp measurable_swap
  have hage := measurableSet_ae_real_section
    ((measurableSet_lt (measurable_const (a := (0 : ℝ))) measurable_snd).inter
      (measurableSet_lt measurable_snd
        ((measurable_excursion_lifetime.comp (measurable_fst.comp measurable_fst)).coe_nnreal_real))
      |>.compl.union (measurableSet_eq_fun heval hraw))
  have hm := hzero.inter (htail.inter hage)
  convert hm using 1
  ext p
  simp only [mem_ofPred_eq, IsExcursionHeightVersion, tail_zero_iff,
    ae_restrict_iff' measurableSet_Ioo, mem_Ioo, mem_inter_iff, mem_union,
    mem_compl_iff, Function.comp_def, ← imp_iff_not_or]

private theorem excursion_version_measurable (θ : ℝ) :
    MeasurableSet {e : Excursion | ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g} ∧
      Measurable (excursionHeight θ) := by
  let : TopologicalSpace.MetrizableSpace C(ℝ≥0, ℝ) := UniformSpace.metrizableSpace
  let : PolishSpace C(ℝ≥0, ℝ) := inferInstance
  exact measurable_unique_version (IsExcursionHeightVersion θ)
    (measurableSet_isExcursionHeightVersion θ) (fun _ _ _ hg hh => hg.unique hh) 0

/-- The non-junk event of `excursionHeight` is Borel (the compensation transfer needs it). -/
theorem measurableSet_exists_isExcursionHeightVersion (θ : ℝ) :
    MeasurableSet {e : Excursion | ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g} :=
  (excursion_version_measurable θ).1

/-- The excursion height is a Borel measurable function of the excursion. -/
theorem measurable_excursionHeight (θ : ℝ) : Measurable (excursionHeight θ) :=
  (excursion_version_measurable θ).2

/-- Joint measurability of `(t, e) ↦ excursionHeight θ e t` (Fubini arguments in J01). -/
theorem measurable_excursionHeight_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × Excursion => excursionHeight θ p.2 p.1) := by
  exact measurable_uncurry_of_continuous_of_measurable (fun e => (excursionHeight θ e).continuous)
    (fun t => (ContinuousMap.measurable_eval t).comp (measurable_excursionHeight θ))

/-- The a.e.-time prefix height map is Borel measurable. -/
theorem measurable_heightPrefixAE (θ : ℝ) (T : ℝ≥0) : Measurable (heightPrefixAE θ T) := by
  have hzero : MeasurableSet {p : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ) |
      p.2 ⟨0, le_rfl, T.2⟩ = 0} :=
    measurableSet_eq_fun ((ContinuousMap.measurable_eval _).comp measurable_snd) measurable_const
  have hraw : Measurable (fun p : (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) × ℝ =>
      heightUniv θ (extendConst T p.1.1) p.2.toNNReal) :=
    Measurable.comp (g := fun p : ℝ≥0 × DLoc => heightUniv θ p.2 p.1)
      (f := fun p : (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) × ℝ =>
        (p.2.toNNReal, extendConst T p.1.1))
      (measurable_heightUniv_uncurry θ)
      ((measurable_real_toNNReal.comp measurable_snd).prodMk
        ((measurable_extendConst T).comp (measurable_fst.comp measurable_fst)))
  have heval : Measurable (fun p : (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) × ℝ =>
      p.1.2 (Set.projIcc 0 (T : ℝ) T.2 p.2)) := by
    have hm : Measurable (fun p : ℝ × (D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ)) =>
        p.2.2 (Set.projIcc 0 (T : ℝ) T.2 p.1)) :=
      measurable_uncurry_of_continuous_of_measurable
      (fun p => p.2.continuous.comp continuous_projIcc)
      (fun s => (ContinuousMap.measurable_eval (Set.projIcc 0 (T : ℝ) T.2 s)).comp
        measurable_snd)
    exact hm.comp measurable_swap
  have hage := measurableSet_ae_real_section
    (((measurable_snd (measurableSet_Ioo (a := (0 : ℝ)) (b := (T : ℝ)))).compl).union
      (measurableSet_eq_fun heval hraw))
  have hrel : MeasurableSet {p : D (T : ℝ) ℝ × C(Set.Icc (0 : ℝ) T, ℝ) |
      IsPrefixHeightVersion θ T p.1 p.2} := by
    convert hzero.inter hage using 1
    ext p
    simp only [mem_ofPred_eq, IsPrefixHeightVersion, ae_restrict_iff' measurableSet_Ioo,
      mem_inter_iff, mem_union, mem_compl_iff,
      mem_preimage, ← imp_iff_not_or]
  exact (measurable_unique_version (IsPrefixHeightVersion θ T) hrel
    (fun _ _ _ hc hd => hc.unique hd) 0).2

end BGW.StableTrees
