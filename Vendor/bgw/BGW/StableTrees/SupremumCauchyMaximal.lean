/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumCauchyBasic
import BGW.Probability.DoobL2ResolventMoment
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Conditional expectations of discounted occupation differences

Identify the explicit resolvent martingale with its integrable terminal variable.

## References

* [J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV]
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

private theorem kernel_abs_le {ε : ℝ} (hε : 0 < ε) (y : ℝ) :
    |supOccKernel ε y| ≤ ε⁻¹ := by
  rw [abs_of_nonneg (supOccKernel_mem_Icc hε y).1]
  exact (supOccKernel_mem_Icc hε y).2

private theorem discounted_integrable_bound {k : ℝ → ℝ} (hk : Measurable k) {C : ℝ}
    (hC : ∀ s, |k s| ≤ C) (a : ℝ) :
    IntegrableOn (fun s => Real.exp (-s) * k s) (Ioi a) ∧
      |∫ s in Ioi a, Real.exp (-s) * k s| ≤ C * Real.exp (-a) := by
  have hi : IntegrableOn (fun s => Real.exp (-s) * k s) (Ioi a) :=
    (integrableOn_exp_neg_Ioi a).mul_bdd hk.aestronglyMeasurable
      (ae_of_all _ (fun s => by simpa only [Real.norm_eq_abs] using hC s))
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ s in Ioi a, ‖Real.exp (-s) * k s‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ s in Ioi a, Real.exp (-s) * C := by
      apply integral_mono_ae hi.norm ((integrableOn_exp_neg_Ioi a).mul_const C)
      exact ae_of_all _ (fun s => by
        simpa only [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using
          mul_le_mul_of_nonneg_left (hC s) (Real.exp_pos (-s)).le)
    _ = C * Real.exp (-a) := by
      rw [integral_mul_const]
      have he := integral_exp_mul_Ioi (by norm_num : (-1 : ℝ) < 0) a
      simp only [neg_one_mul, div_neg, div_one, neg_neg] at he
      rw [he, mul_comm]

/-- The explicit martingale is the conditional expectation of the full discounted difference. -/
theorem occupationDiffMartingale_eq_condExp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {ε η : ℝ}
    (hε : 0 < ε) (hη : 0 < η) (t : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc)[discountedOccupation
      (fun s f => supReflectedFrom 0 f s)
      (fun r => supOccKernel ε r - supOccKernel η r) | DLoc.filtration t] =ᵐ[
        (stableLocalLaw θ : Measure DLoc)] occupationDiffMartingale θ ε η t := by
  let k := fun r => supOccKernel ε r - supOccKernel η r
  let Z := fun (s : ℝ≥0) (f : DLoc) => supReflectedFrom 0 f s
  let B := discountedOccupation Z k
  let past := fun f => ∫ s in Ioc (0 : ℝ) t, Real.exp (-s) * k (Z s.toNNReal f)
  let future := fun f => ∫ s in Ioi (t : ℝ), Real.exp (-s) * k (Z s.toNNReal f)
  have hk : Measurable k := (measurable_supOccKernel ε).sub (measurable_supOccKernel η)
  have hb (r : ℝ) : |k r| ≤ ε⁻¹ + η⁻¹ :=
    (abs_sub _ _).trans (add_le_add (kernel_abs_le hε r) (kernel_abs_le hη r))
  have hZ : Measurable (fun p : ℝ × DLoc => Z p.1.toNNReal p.2) :=
    measurable_supReflectedFrom_uncurry.comp
      (measurable_const.prodMk
        (measurable_snd.prodMk (measurable_real_toNNReal.comp measurable_fst)))
  have hint (a : ℝ) : Integrable (fun p : ℝ × DLoc => Real.exp (-p.1) * k (Z p.1.toNNReal p.2))
      ((volume.restrict (Ioi a)).prod (stableLocalLaw θ : Measure DLoc)) := by
    simpa only [neg_one_mul, Function.comp_apply] using integrable_exp_mul_bounded_prod
      (hk.comp hZ) (by norm_num : (-1 : ℝ) < 0) (fun p => hb _)
  have hB : Integrable B (stableLocalLaw θ : Measure DLoc) := (hint 0).integral_prod_right
  have hfuture : Integrable future (stableLocalLaw θ : Measure DLoc) :=
    (hint t).integral_prod_right
  have hsplit (f : DLoc) : B f = past f + future f := by
    have hpath (a : ℝ) := (discounted_integrable_bound
      (hk.comp (hZ.comp (measurable_id.prodMk (measurable_const (a := f)))))
        (fun s => hb _) a).1
    change (∫ s in Ioi (0 : ℝ), Real.exp (-s) * k (Z s.toNNReal f)) = _
    rw [← Ioc_union_Ioi_eq_Ioi t.coe_nonneg]
    exact setIntegral_union Ioc_disjoint_Ioi_same measurableSet_Ioi
      ((hpath 0).mono_set Ioc_subset_Ioi_self) (hpath t)
  have hpast : Integrable past (stableLocalLaw θ : Measure DLoc) := by
    apply (hB.sub hfuture).congr
    exact ae_of_all _ fun f => by
      simpa only [Pi.sub_apply] using (eq_sub_iff_add_eq.mpr (hsplit f).symm).symm
  have hVp : StronglyMeasurable[DLoc.filtration t] (fun f =>
      Real.exp (-(t : ℝ)) * (supOccupationResolvent θ 1 ε (Z t f) -
        supOccupationResolvent θ 1 η (Z t f))) := by
    have hm : Measurable (fun y => supOccupationResolvent θ 1 ε y -
        supOccupationResolvent θ 1 η y) :=
      (measurable_reflectedResolvent hθ 1 (measurable_supOccKernel ε)
        ⟨ε⁻¹, kernel_abs_le hε⟩).sub
      (measurable_reflectedResolvent hθ 1 (measurable_supOccKernel η)
        ⟨η⁻¹, kernel_abs_le hη⟩)
    exact ((hm.comp ((isStronglyProgressive_supReflectedFrom 0).stronglyAdapted
      t).measurable).stronglyMeasurable).const_mul _
  have hpm : StronglyMeasurable[DLoc.filtration t] past := by
    convert ((martingale_occupationDiffMartingale hθ hε hη).stronglyMeasurable t).sub hVp using 1
    funext f
    exact (add_sub_cancel_right _ _).symm
  have hcond := resolventMarkov_supReflectedFrom_sub hθ 0 hε hη t
  have he : B = past + future := funext hsplit
  change (stableLocalLaw θ : Measure DLoc)[B | DLoc.filtration t] =ᵐ[_] _
  rw [he]
  filter_upwards [condExp_add hpast hfuture (DLoc.filtration t), hcond] with f hf hc
  rw [hf]
  simp only [Pi.add_apply]
  rw [condExp_of_stronglyMeasurable (DLoc.filtration.le t) hpm hpast, hc]
  rfl

/-- The extended compact supremum of a measurable right-continuous process is measurable. -/
theorem measurable_sup_Icc_enorm {Ω : Type*} [MeasurableSpace Ω]
    {M : ℝ≥0 → Ω → ℝ} (hM : ∀ t, Measurable (M t))
    (hrc : ∀ ω t, ContinuousWithinAt (fun s => M s ω) (Ici t) t) (T : ℝ≥0) :
    Measurable (fun ω => ⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ) := by
  let Q : Set ℝ≥0 := Set.range (fun q : ℚ => Real.toNNReal (q : ℝ)) ∪ {T}
  let D : Set ℝ≥0 := Icc 0 T ∩ Q
  let tT : D := ⟨T, ⟨by simp, by simp [Q]⟩⟩
  have hQ : Q.Countable := (countable_range _).union (countable_singleton T)
  have hD : D.Countable := hQ.mono inter_subset_right
  let _ : Countable D := hD.to_subtype
  have hsupD (ω : Ω) : (⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ) =
      ⨆ d : D, ‖M d.1 ω‖ₑ := by
    apply le_antisymm
    · refine iSup_le fun t => iSup_le fun ht => ?_
      by_cases htT : t = T
      · subst t
        exact le_iSup_of_le tT (le_refl _)
      obtain ⟨q, hqanti, hqt, hqtop⟩ := Real.exists_seq_rat_strictAnti_tendsto (t : ℝ)
      let u : ℕ → ℝ≥0 := fun n => min (Real.toNNReal (q n : ℝ)) T
      have hq0 (n : ℕ) : 0 ≤ (q n : ℝ) := (hqt n).le.trans' t.coe_nonneg
      have huD (n : ℕ) : u n ∈ D := by
        have h0q : 0 ≤ Real.toNNReal (q n : ℝ) := by positivity
        refine ⟨⟨le_min h0q T.2, min_le_right _ _⟩, ?_⟩
        by_cases hqT : Real.toNNReal (q n : ℝ) ≤ T
        · refine Or.inl ?_
          simp only [u, min_eq_left hqT]
          exact ⟨q n, rfl⟩
        · refine Or.inr ?_
          simp only [u, min_eq_right (le_of_not_ge hqT)]
          exact rfl
      have hut (n : ℕ) : t ≤ u n := by
        apply le_min _ ht.2
        exact NNReal.le_toNNReal_of_coe_le (hqt n).le
      have hucoe (n : ℕ) : (u n : ℝ) = min (q n : ℝ) (T : ℝ) := by
        simp [u, Real.coe_toNNReal _ (hq0 n)]
      have hutop : Tendsto u atTop (𝓝 t) := by
        rw [← NNReal.tendsto_coe]
        simp only [hucoe]
        convert hqtop.min (tendsto_const_nhds (x := (T : ℝ))) using 1
        have htTR : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht.2
        rw [min_eq_left htTR]
      have hutop' : Tendsto u atTop (nhdsWithin t (Ici t)) :=
        tendsto_nhdsWithin_iff.2 ⟨hutop, Eventually.of_forall hut⟩
      have hm := (hrc ω t).tendsto.comp hutop'
      have he : Tendsto (fun n => ‖M (u n) ω‖ₑ) atTop (𝓝 ‖M t ω‖ₑ) :=
        (continuous_enorm.tendsto _).comp hm
      apply le_of_tendsto he
      exact Eventually.of_forall fun n => le_iSup_of_le ⟨u n, huD n⟩ (le_refl _)
    · refine iSup_le fun d => ?_
      exact le_iSup_of_le d.1 (le_iSup_of_le d.2.1 (le_refl _))
  simp_rw [hsupD]
  exact Measurable.iSup fun d => (hM d.1).enorm

/-- A bounded kernel has a square integrable discounted occupation. -/
theorem integrable_sq_discountedOccupation_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {Z : ℝ≥0 → Ω → ℝ} {k : ℝ → ℝ}
    (hZ : Measurable (fun p : ℝ≥0 × Ω => Z p.1 p.2)) (hk : Measurable k)
    {C : ℝ} (hC : ∀ r, |k r| ≤ C) :
    Integrable (fun ω => (discountedOccupation Z k ω) ^ 2) μ := by
  have hm : Measurable (fun p : ℝ × Ω => k (Z p.1.toNNReal p.2)) :=
    hk.comp (hZ.comp (measurable_real_toNNReal.prodMap measurable_id))
  have hF : Measurable (fun p : ℝ × Ω => Real.exp (-p.1) * k (Z p.1.toNNReal p.2)) :=
    (Real.continuous_exp.measurable.comp measurable_fst.neg).mul hm
  have hB : Measurable (discountedOccupation Z k) := by
    exact hF.stronglyMeasurable.integral_prod_left'.measurable
  apply Integrable.of_bound (hB.aestronglyMeasurable.pow 2) (C ^ 2)
  apply ae_of_all
  intro ω
  have hp : Measurable (fun s : ℝ => k (Z s.toNNReal ω)) :=
    hm.comp (measurable_id.prodMk measurable_const)
  have hb := (discounted_integrable_bound hp (fun s => hC _) 0).2
  simp only [neg_zero, Real.exp_zero, mul_one] at hb
  change ‖(discountedOccupation Z k ω) ^ 2‖ ≤ C ^ 2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs, discountedOccupation] using pow_le_pow_left₀ (abs_nonneg _) hb 2

end BGW.StableTrees
