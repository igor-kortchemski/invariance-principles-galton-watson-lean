/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureLaplaceBasic

/-! Exponential transforms of finite disjoint measurable partitions inside finite-rate boxes.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

private theorem expNeg_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ≥0∞) :
    expNeg (∑ i ∈ s, f i) = ∏ i ∈ s, expNeg (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp only [Finset.sum_insert hi, Finset.prod_insert hi, expNeg_add, ih]

private theorem real_pgf {ι : Type*} [Fintype ι] {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    (T ε : ℝ≥0) (hε : 0 < ε) (B : ι → Set (ℝ≥0 × Excursion))
    (hB : ∀ i, MeasurableSet (B i))
    (hsub : ∀ i, B i ⊆ Ioc 0 T ×ˢ {e : Excursion | ε < e.lifetime})
    (hd : Pairwise (Function.onFun Disjoint B)) (z : ι → ℝ)
    (hz0 : ∀ i, 0 ≤ z i) (hz1 : ∀ i, z i ≤ 1) :
    (∫ f, ∏ i, z i ^ natCount (ξ f) (B i) ∂(stableLocalLaw θ : Measure DLoc)) =
      Real.exp (∑ i, ((lebNN.prod (excursionMeasure θ)) (B i)).toReal * (z i - 1)) := by
  let e := Fintype.equivFin ι
  have hh := excursion_pgf_subsets hθ hξ hae T ε hε (fun i => B (e.symm i))
    (fun i => hB (e.symm i)) (fun i => hsub (e.symm i))
    (fun i j hij => hd (fun heq => hij (e.symm.injective heq)) )
    (fun i => z (e.symm i)) (fun i => hz0 (e.symm i)) (fun i => hz1 (e.symm i))
  have hp (f : DLoc) : (∏ i, z (e.symm i) ^ natCount (ξ f) (B (e.symm i))) =
      ∏ i, z i ^ natCount (ξ f) (B i) :=
    e.symm.prod_comp (fun i => z i ^ natCount (ξ f) (B i))
  have hs : (∑ i, ((lebNN.prod (excursionMeasure θ)) (B (e.symm i))).toReal *
      (z (e.symm i) - 1)) =
      ∑ i, ((lebNN.prod (excursionMeasure θ)) (B i)).toReal * (z i - 1) :=
    e.symm.sum_comp (fun i => ((lebNN.prod (excursionMeasure θ)) (B i)).toReal * (z i - 1))
  simpa only [hp, hs] using hh

/-- Finite disjoint measurable partitions in a lifetime-slab box have the Poisson
exponential transform, including infinite coefficients. -/
theorem excursion_laplace_partition {ι : Type*} [Fintype ι] {θ : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    (T ε : ℝ≥0) (hε : 0 < ε) (B : ι → Set (ℝ≥0 × Excursion))
    (hB : ∀ i, MeasurableSet (B i))
    (hsub : ∀ i, B i ⊆ Ioc 0 T ×ˢ {e : Excursion | ε < e.lifetime})
    (hd : Pairwise (Function.onFun Disjoint B)) (c : ι → ℝ≥0∞) :
    (∫⁻ f, expNeg (∑ i, c i * ξ f (B i)) ∂(stableLocalLaw θ : Measure DLoc)) =
      expNeg (∑ i, (1 - expNeg (c i)) * (lebNN.prod (excursionMeasure θ)) (B i)) := by
  classical
  let P : Measure DLoc := stableLocalLaw θ
  let μ := lebNN.prod (excursionMeasure θ)
  let := sigmaFinite_excursionMeasure hθ
  obtain ⟨hlevy, hslab⟩ := isTimeSimpleLevy_of_ae_eq_excursionPointMeasure hθ hξ hae
  have hfinite (i : ι) : μ (B i) ≠ ⊤ := by
    apply ne_top_of_le_ne_top _ (measure_mono (hsub i))
    rw [Measure.prod_prod, lebNN_Ioc, tsub_zero]
    exact (ENNReal.mul_lt_top ENNReal.coe_lt_top
      (excursionMeasure_lifetime_slab_lt_top hθ hε)).ne
  have hcount (i : ι) : ∀ᵐ f ∂P, (natCount (ξ f) (B i) : ℝ≥0∞) = ξ f (B i) := by
    apply ae_natCount_cast hlevy (hB i)
    filter_upwards [(hslab ε hε).2.2 T] with f hf
    exact lt_of_le_of_lt (measure_mono (hsub i)) hf
  let z : ι → ℝ := fun i => (expNeg (c i)).toReal
  have hztop (i : ι) : expNeg (c i) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top
    (expNeg_le_one _)
  have hz0 (i : ι) : 0 ≤ z i := ENNReal.toReal_nonneg
  have hz1 (i : ι) : z i ≤ 1 := by
    exact (ENNReal.toReal_le_toReal (hztop i) ENNReal.one_ne_top).mpr (expNeg_le_one _)
  let V : DLoc → ℝ := fun f => ∏ i, z i ^ natCount (ξ f) (B i)
  have hNm (i : ι) : Measurable (fun f => natCount (ξ f) (B i)) :=
    measurable_natCount hξ (hB i)
  have hVm : Measurable V := by fun_prop
  have hV0 (f : DLoc) : 0 ≤ V f := Finset.prod_nonneg fun i _ => pow_nonneg (hz0 i) _
  have hV1 (f : DLoc) : V f ≤ 1 :=
    Finset.prod_le_one₀ (fun i _ => pow_nonneg (hz0 i) _)
      (fun i _ => pow_le_one₀ (hz0 i) (hz1 i))
  have hVi : Integrable V P := by
    apply Integrable.of_bound hVm.aestronglyMeasurable 1
    filter_upwards [] with f
    rw [Real.norm_eq_abs, abs_of_nonneg (hV0 f)]
    exact hV1 f
  have hpoint : (fun f => expNeg (∑ i, c i * ξ f (B i))) =ᵐ[P]
      (fun f => ENNReal.ofReal (V f)) := by
    filter_upwards [ae_all_iff.mpr hcount] with f hf
    rw [expNeg_sum]
    simp_rw [← hf, expNeg_mul_nat]
    simp only [V, ENNReal.ofReal_prod_of_nonneg (fun i _ => pow_nonneg (hz0 i) _),
      ENNReal.ofReal_pow (hz0 _), z, ENNReal.ofReal_toReal (hztop _)]
  have hsumtop : (∑ i, (1 - expNeg (c i)) * μ (B i)) ≠ ⊤ := by
    apply ENNReal.sum_ne_top.mpr
    intro i _
    exact ENNReal.mul_ne_top (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) (hfinite i)
  have hexponent : (∑ i, (μ (B i)).toReal * (z i - 1)) =
      -(∑ i, (1 - expNeg (c i)) * μ (B i)).toReal := by
    rw [ENNReal.toReal_sum (fun i _ => ENNReal.mul_ne_top
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self) (hfinite i)), ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [ENNReal.toReal_mul, ENNReal.toReal_sub_of_le (expNeg_le_one _) ENNReal.one_ne_top,
      ENNReal.toReal_one]
    dsimp [z]
    ring
  calc
    _ = ∫⁻ f, ENNReal.ofReal (V f) ∂P := lintegral_congr_ae hpoint
    _ = ENNReal.ofReal (∫ f, V f ∂P) :=
      (ofReal_integral_eq_lintegral_ofReal hVi (Eventually.of_forall hV0)).symm
    _ = ENNReal.ofReal (Real.exp (∑ i, (μ (B i)).toReal * (z i - 1))) := by
      rw [real_pgf hθ hξ hae T ε hε B hB hsub hd z hz0 hz1]
    _ = _ := by rw [hexponent, expNeg, ite_eq_right hsumtop]

end BGW.StableTrees
