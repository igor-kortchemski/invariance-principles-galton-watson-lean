/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Probability.DoobL2Resolvent
import BGW.StableTrees.SupremumCauchyDoob

/-!
# Doob estimates with almost surely right-continuous paths

The countable dense-time argument is performed on one event of full measure. No change
of the adapted representatives or completion of the filtration is necessary.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Probability

namespace BGW.StableTrees

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- The compact extended supremum is measurable up to a null set. -/
theorem aemeasurable_sup_Icc_enorm_of_ae_rightContinuous {Ω : Type*}
    [MeasurableSpace Ω] {μ : Measure Ω}
    {M : ℝ≥0 → Ω → ℝ} (hM : ∀ t, Measurable (M t))
    (hrc : ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt (fun s => M s ω) (Ici t) t) (T : ℝ≥0) :
    AEMeasurable (fun ω => ⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ) μ := by
  let Q : Set ℝ≥0 := Set.range (fun q : ℚ => Real.toNNReal (q : ℝ)) ∪ {T}
  let D : Set ℝ≥0 := Icc 0 T ∩ Q
  let tT : D := ⟨T, ⟨by simp, by simp [Q]⟩⟩
  have hQ : Q.Countable := (countable_range _).union (countable_singleton T)
  have hD : D.Countable := hQ.mono inter_subset_right
  let _ : Countable D := hD.to_subtype
  have hsupD : ∀ᵐ ω ∂μ, (⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ) =
      ⨆ d : D, ‖M d.1 ω‖ₑ := by
    filter_upwards [hrc] with ω hω
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
      have hm := (hω t).tendsto.comp hutop'
      have he : Tendsto (fun n => ‖M (u n) ω‖ₑ) atTop (𝓝 ‖M t ω‖ₑ) :=
        (continuous_enorm.tendsto _).comp hm
      apply le_of_tendsto he
      exact Eventually.of_forall fun n => le_iSup_of_le ⟨u n, huD n⟩ (le_refl _)
    · refine iSup_le fun d => ?_
      exact le_iSup_of_le d.1 (le_iSup_of_le d.2.1 (le_refl _))
  exact (Measurable.iSup fun d : D => (hM d.1).enorm).aemeasurable.congr
    (hsupD.mono fun _ h => h.symm)

/-- Compact-time extended Doob inequality with almost sure right continuity. -/
theorem lintegral_sq_sup_Icc_le_four_mul_of_ae_rightContinuous
    {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›} {M : ℝ≥0 → Ω → ℝ}
    (hM : Martingale M ℱ μ) (hrc : ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt (fun s => M s ω) (Ici t) t)
    (T : ℝ≥0) :
    ∫⁻ ω, (⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ) ^ 2 ∂μ ≤
      4 * ∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ := by
  let Q : Set ℝ≥0 := Set.range (fun q : ℚ => Real.toNNReal (q : ℝ)) ∪ {T}
  let D : Set ℝ≥0 := Icc 0 T ∩ Q
  let tT : D := ⟨T, ⟨by simp, by simp [Q]⟩⟩
  have hQ : Q.Countable := (countable_range _).union (countable_singleton T)
  have hD : D.Countable := hQ.mono inter_subset_right
  let _ : Countable D := hD.to_subtype
  have hsupD : ∀ᵐ ω ∂μ, (⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ) =
      ⨆ d : D, ‖M d.1 ω‖ₑ := by
    filter_upwards [hrc] with ω hω
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
      have hm := (hω t).tendsto.comp hutop'
      have he : Tendsto (fun n => ‖M (u n) ω‖ₑ) atTop (𝓝 ‖M t ω‖ₑ) :=
        (continuous_enorm.tendsto _).comp hm
      apply le_of_tendsto he
      exact Eventually.of_forall fun n => le_iSup_of_le ⟨u n, huD n⟩ (le_refl _)
    · refine iSup_le fun d => ?_
      exact le_iSup_of_le d.1 (le_iSup_of_le d.2.1 (le_refl _))
  let F := {s : Finset D // tT ∈ s}
  let B : F → Ω → ℝ≥0∞ := fun s ω => s.1.sup fun d => ‖M d.1 ω‖ₑ
  have hFB (ω : Ω) : (⨆ d : D, ‖M d.1 ω‖ₑ) = ⨆ s : F, B s ω := by
    rw [iSup_eq_iSup_finset]
    apply le_antisymm
    · refine iSup_le fun s => ?_
      let s' : F := ⟨insert tT s, Finset.mem_insert_self _ _⟩
      apply le_iSup_of_le s'
      simpa only [B, Finset.sup_eq_iSup] using
        Finset.sup_mono (f := fun d : D => ‖M d.1 ω‖ₑ) (Finset.subset_insert _ _)
    · refine iSup_le fun s => ?_
      change (s.1.sup fun d : D => ‖M d.1 ω‖ₑ) ≤
        ⨆ t : Finset D, ⨆ d : D, ⨆ _ : d ∈ t, ‖M d.1 ω‖ₑ
      apply Finset.sup_le
      intro d hd
      exact le_iSup_of_le {d} (le_iSup_of_le d
        (le_iSup_of_le (Finset.mem_singleton_self d) (le_refl _)))
  have hpow (ω : Ω) : (⨆ s : F, B s ω) ^ 2 = ⨆ s : F, (B s ω) ^ 2 := by
    apply le_antisymm
    · rw [pow_two, ENNReal.iSup_mul]
      refine iSup_le fun s => ?_
      rw [ENNReal.mul_iSup]
      refine iSup_le fun u => ?_
      let v : F := ⟨s.1 ∪ u.1, Finset.mem_union_left _ s.2⟩
      calc
        B s ω * B u ω ≤ B v ω * B v ω := by
          apply mul_le_mul' <;> apply Finset.sup_mono
          · exact Finset.subset_union_left
          · exact Finset.subset_union_right
        _ = B v ω ^ 2 := (pow_two _).symm
        _ ≤ ⨆ s : F, B s ω ^ 2 := le_iSup_of_le v (le_refl _)
    · refine iSup_le fun s => ?_
      exact pow_le_pow_left' (le_iSup (fun u : F => B u ω) s) 2
  have hmeas_sup (s : Finset D) : Measurable (fun ω => s.sup fun d => ‖M d.1 ω‖ₑ) := by
    classical
    induction s using Finset.induction_on with
    | empty => simp
    | @insert d s hd ih =>
      simp only [Finset.sup_insert]
      exact ((hM.stronglyMeasurable d.1).measurable.le (ℱ.le d.1)).enorm.sup ih
  have hdir : Directed (· ≤ ·) (fun s ω => (B s ω) ^ 2) := by
    intro s u
    let v : F := ⟨s.1 ∪ u.1, Finset.mem_union_left _ s.2⟩
    refine ⟨v, ?_, ?_⟩ <;> intro ω <;> dsimp only <;> gcongr
    · exact Finset.sup_mono Finset.subset_union_left
    · exact Finset.sup_mono Finset.subset_union_right
  have hbound (s : F) : (∫⁻ ω, (B s ω) ^ 2 ∂μ) ≤
      4 * ∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ := by
    have hTmem : T ∈ s.1.image Subtype.val := Finset.mem_image.2 ⟨tT, s.2, rfl⟩
    have hmax : ∀ t ∈ s.1.image Subtype.val, t ≤ T := by
      intro t ht
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.1 ht
      exact d.2.1.2
    have h := lintegral_sq_sup_finset_le_four_mul_of_martingale hM T
      (s.1.image Subtype.val) hTmem hmax
    simpa only [B, Finset.sup_image, Function.comp_def] using h
  calc
    _ = ∫⁻ ω, ⨆ s : F, (B s ω) ^ 2 ∂μ := by
      apply lintegral_congr_ae
      filter_upwards [hsupD] with ω hω
      rw [hω, hFB, hpow]
    _ = ⨆ s : F, ∫⁻ ω, (B s ω) ^ 2 ∂μ := by
      apply lintegral_iSup_directed
      · intro s
        exact ((hmeas_sup s.1).pow_const 2).aemeasurable
      · exact hdir
    _ ≤ _ := iSup_le hbound

/-- Real compact Doob inequality with almost sure right continuity. -/
theorem integral_sq_sup_Iic_le_four_mul_of_ae_rightContinuous {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {M : ℝ≥0 → Ω → ℝ} (hM : Martingale M ℱ μ)
    (hrc : ∀ᵐ ω ∂μ, ∀ t, ContinuousWithinAt (fun s => M s ω) (Ici t) t)
    (T : ℝ≥0) (h2 : Integrable (fun ω => M T ω ^ 2) μ) :
    Integrable (fun ω => (⨆ t : Set.Iic T, |M t ω|) ^ 2) μ ∧
      ∫ ω, (⨆ t : Set.Iic T, |M t ω|) ^ 2 ∂μ ≤ 4 * ∫ ω, M T ω ^ 2 ∂μ := by
  let S := fun ω => ⨆ t ∈ Icc (0 : ℝ≥0) T, ‖M t ω‖ₑ
  let A := fun ω => ⨆ t : Set.Iic T, |M t ω|
  have hS : AEMeasurable S μ := aemeasurable_sup_Icc_enorm_of_ae_rightContinuous
    (fun t => (hM.stronglyMeasurable t).measurable.mono (ℱ.le t) le_rfl) hrc T
  have he (ω : Ω) : S ω = ⨆ t : Set.Iic T, ‖M t ω‖ₑ := by
    simp only [S, mem_Icc, zero_le, true_and, iSup_subtype, mem_Iic]
  have hA (ω : Ω) : A ω = (S ω).toReal := by
    rw [he, ENNReal.toReal_iSup (fun _ => enorm_ne_top)]
    simp only [toReal_enorm, Real.norm_eq_abs, A]
  have hAm : AEMeasurable A μ := by
    have heq : A = fun ω => (S ω).toReal := funext hA
    rw [heq]
    exact hS.ennreal_toReal
  have hbound := lintegral_sq_sup_Icc_le_four_mul_of_ae_rightContinuous hM hrc T
  have hfin : (∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ) < ∞ := by
    have hf := h2.hasFiniteIntegral
    rw [hasFiniteIntegral_iff_enorm] at hf
    simpa only [enorm_pow] using hf
  have hfinite : 4 * (∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ) < ∞ :=
    ENNReal.mul_lt_top (by norm_num) hfin
  have hle : (∫⁻ ω, ENNReal.ofReal (A ω ^ 2) ∂μ) ≤
      4 * ∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ := by
    apply le_trans (lintegral_mono (fun ω => ?_)) hbound
    change ENNReal.ofReal (A ω ^ 2) ≤ S ω ^ 2
    rw [hA, ← ENNReal.toReal_pow]
    exact ENNReal.ofReal_toReal_le
  have hi : Integrable (fun ω => A ω ^ 2) μ :=
    ⟨hAm.aestronglyMeasurable.pow 2,
      (hasFiniteIntegral_iff_ofReal (ae_of_all _ (fun ω => sq_nonneg (A ω)))).2
        (hle.trans_lt hfinite)⟩
  refine ⟨hi, ?_⟩
  have hr := ENNReal.toReal_mono hfinite.ne hle
  rw [← integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => sq_nonneg (A ω)))
    hi.aestronglyMeasurable] at hr
  have hterminal : ∫ ω, M T ω ^ 2 ∂μ = (∫⁻ ω, ‖M T ω‖ₑ ^ 2 ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (fun ω => sq_nonneg _))
      h2.aestronglyMeasurable]
    congr 1
    apply lintegral_congr
    intro ω
    rw [← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _) 2, Real.norm_eq_abs, sq_abs]
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofNat, ← hterminal] using hr

end BGW.StableTrees
