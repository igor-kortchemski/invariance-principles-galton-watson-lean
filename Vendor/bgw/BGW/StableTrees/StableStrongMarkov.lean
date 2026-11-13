/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableLocalMarkov
public import BGW.Skorokhod.DLocShiftAt

import BGW.Skorokhod.MeasurableLaws
import Mathlib.Algebra.Order.Floor.Extended

/-!
# Strong Markov property of the stable process on local càdlàg paths

This module proves the strong Markov property of `stableLocalLaw` at stopping times of the
right-continuous natural filtration. Countably valued upper grid approximations reduce the
argument to deterministic times, and càdlàg sample paths give convergence of finite-dimensional
future laws (J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter I,
Proposition 6; O. Kallenberg, *Foundations of Modern Probability*, 2nd ed., Springer, 2002,
Theorem 13.11).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private noncomputable def dyadicApprox (n : ℕ) (τ : DLoc → ℝ≥0∞) (f : DLoc) : ℝ≥0∞ :=
  ((⌈((n + 1 : ℕ) : ℝ≥0∞) * τ f⌉ₑ : ℕ∞) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞)

private noncomputable def dyadicFloor (n : ℕ) (t : ℝ≥0) : ℝ≥0∞ :=
  ((⌊((n + 1 : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)⌋ₑ : ℕ∞) : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞)

private theorem le_dyadicApprox (n : ℕ) (τ : DLoc → ℝ≥0∞) (f : DLoc) :
    τ f ≤ dyadicApprox n τ f := by
  unfold dyadicApprox
  rw [ENNReal.le_div_iff_mul_le]
  · simpa [mul_comm] using
      (ENat.le_ceil_self (r := ((n + 1 : ℕ) : ℝ≥0∞) * τ f))
  · simp
  · simp

private theorem dyadicApprox_le_iff (n : ℕ) (τ : DLoc → ℝ≥0∞) (f : DLoc) (t : ℝ≥0) :
    dyadicApprox n τ f ≤ t ↔ τ f ≤ dyadicFloor n t := by
  unfold dyadicApprox dyadicFloor
  rw [ENNReal.div_le_iff_le_mul]
  · calc
      _ ↔ (⌈((n + 1 : ℕ) : ℝ≥0∞) * τ f⌉ₑ : ℝ≥0∞) ≤
          ((⌊((n + 1 : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)⌋ₑ : ℕ∞) : ℝ≥0∞) :=
        by
          constructor
          · intro h
            have hi : ⌈((n + 1 : ℕ) : ℝ≥0∞) * τ f⌉ₑ ≤
                ⌊((n + 1 : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)⌋ₑ :=
              ENat.le_floor.mpr (by simpa only [mul_comm] using h)
            exact_mod_cast hi
          · intro h
            have hi : ⌈((n + 1 : ℕ) : ℝ≥0∞) * τ f⌉ₑ ≤
                ⌊((n + 1 : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)⌋ₑ := by
              exact_mod_cast h
            have hr := ENat.le_floor.mp hi
            simpa only [mul_comm] using hr
      _ ↔ ((n + 1 : ℕ) : ℝ≥0∞) * τ f ≤
          ((⌊((n + 1 : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)⌋ₑ : ℕ∞) : ℝ≥0∞) := by
        norm_cast
        exact ENat.ceil_le
      _ ↔ _ := by
        rw [ENNReal.le_div_iff_mul_le]
        · simp [mul_comm]
        · simp
        · simp
  · simp
  · simp

private theorem dyadicFloor_le (n : ℕ) (t : ℝ≥0) :
    ∃ s : ℝ≥0, dyadicFloor n t = s ∧ s ≤ t := by
  let s : ℝ≥0 := (dyadicFloor n t).toNNReal
  have hfin : dyadicFloor n t < ⊤ := by
    unfold dyadicFloor
    apply ENNReal.div_lt_top
    · have hmul : ((n + 1 : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞) ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp) (by simp)
      exact ENat.toENNReal_ne_top.mpr (ENat.floor_lt_top.mpr (lt_top_iff_ne_top.mpr hmul)).ne
    · simp
  refine ⟨s, (ENNReal.coe_toNNReal (ne_of_lt hfin)).symm, ?_⟩
  rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal (ne_of_lt hfin)]
  unfold dyadicFloor
  calc
    _ ≤ (((n + 1 : ℕ) : ℝ≥0∞) * (t : ℝ≥0∞)) / ((n + 1 : ℕ) : ℝ≥0∞) :=
      ENNReal.div_le_div_right ENat.floor_le_self _
    _ = t := by rw [mul_div_assoc, ENNReal.mul_div_cancel] <;> simp

private theorem isStoppingTime_dyadicApprox {τ : DLoc → ℝ≥0∞}
    (hτ : IsStoppingTime DLoc.filtration τ) (n : ℕ) :
    IsStoppingTime DLoc.filtration (dyadicApprox n τ) := by
  intro t
  obtain ⟨s, hs, hst⟩ := dyadicFloor_le n t
  have heq : {f | dyadicApprox n τ f ≤ (t : ℝ≥0∞)} = {f | τ f ≤ (s : ℝ≥0∞)} := by
    ext f
    change dyadicApprox n τ f ≤ (t : ℝ≥0∞) ↔ τ f ≤ (s : ℝ≥0∞)
    rw [dyadicApprox_le_iff, hs]
  change MeasurableSet[DLoc.filtration t] {f | dyadicApprox n τ f ≤ (t : ℝ≥0∞)}
  rw [heq]
  exact DLoc.filtration.mono hst _ (hτ s)

private theorem countable_range_dyadicApprox (n : ℕ) (τ : DLoc → ℝ≥0∞) :
    (Set.range (dyadicApprox n τ)).Countable := by
  apply Set.Countable.mono (show Set.range (dyadicApprox n τ) ⊆
    Set.range (fun k : ℕ∞ => ((k : ℝ≥0∞) / ((n + 1 : ℕ) : ℝ≥0∞))) from ?_)
  · exact Set.countable_range _
  · rintro _ ⟨f, rfl⟩
    exact ⟨⌈((n + 1 : ℕ) : ℝ≥0∞) * τ f⌉ₑ, rfl⟩

private theorem iSup_filtration :
    (⨆ t, DLoc.filtration t) = (inferInstance : MeasurableSpace DLoc) := by
  apply le_antisymm
  · exact iSup_le fun t => DLoc.filtration.le t
  · calc
      (inferInstance : MeasurableSpace DLoc) = ⨆ t, DLoc.rawFiltration t :=
        DLoc.iSup_rawFiltration.symm
      _ ≤ _ := iSup_mono fun t => DLoc.rawFiltration.le_rightCont t

private theorem integrable_shiftAt {θ : ℝ} {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    Integrable (fun f => F (DLoc.shiftAt τ f)) (stableLocalLaw θ : Measure DLoc) := by
  obtain ⟨C, hC⟩ := hFb
  apply Integrable.of_bound (hF.comp (DLoc.measurable_shiftAt hτ)).aestronglyMeasurable C
  exact Eventually.of_forall fun f => by
    simpa only [Real.norm_eq_abs, Function.comp_apply] using hC (DLoc.shiftAt τ f)

private theorem integral_shiftAt_mul_past_of_countable_range {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ π : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    (hπ : IsStoppingTime DLoc.filtration π) (hπc : (Set.range π).Countable)
    (hle : τ ≤ π) (htop : ∀ f, π f = ⊤ → τ f = ⊤) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.shiftAt π f) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A * ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let _ : Countable (Set.range π) := hπc.to_subtype
  let atoms : Set.range π → Set DLoc := fun r => A ∩ {f | π f = r.1}
  have hAπ : MeasurableSet[hπ.measurableSpace] A :=
    (IsStoppingTime.measurableSpace_mono hτ hπ hle) A hA
  have hA0 : MeasurableSet A := by
    have hm : MeasurableSet[⨆ t, DLoc.filtration t] A := hA.1
    rwa [iSup_filtration] at hm
  have hπm : Measurable π := hπ.measurable'
  have hatom_meas (r : Set.range π) : MeasurableSet (atoms r) :=
    hA0.inter ((measurableSet_singleton r.1).preimage hπm)
  have hdisj : Pairwise (Function.onFun Disjoint atoms) := by
    intro r s hrs
    apply Set.disjoint_left.mpr
    intro f hfr hfs
    apply hrs
    apply Subtype.ext
    exact hfr.2.symm.trans hfs.2
  have hunion : (⋃ r, atoms r) = A := by
    ext f
    simp only [Set.mem_iUnion, Set.mem_inter_iff, atoms]
    constructor
    · rintro ⟨r, hf, -⟩
      exact hf
    · intro hf
      exact ⟨⟨π f, ⟨f, rfl⟩⟩, hf, rfl⟩
  have hint : IntegrableOn (fun f => F (DLoc.shiftAt π f)) (⋃ r, atoms r) P := by
    rw [hunion]
    exact (integrable_shiftAt (θ := θ) hπ hF hFb).integrableOn
  have hatom (r : Set.range π) :
      ∫ f in atoms r, F (DLoc.shiftAt π f) ∂P =
        P.real (atoms r) * ∫ f, F f ∂P := by
    by_cases hr : r.1 = ⊤
    · have hempty : atoms r = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro f hf
        have hτtop : τ f = ⊤ := htop f (hr ▸ hf.2)
        exact (ne_of_lt (hAτ hf.1)) hτtop
      simp [hempty]
    · obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp hr
      have heq : atoms r = A ∩ {f | π f = (s : ℝ≥0∞)} := by
        change A ∩ {f | π f = r.1} = _
        rw [← hs]
        rfl
      rw [heq]
      have hset : A ∩ {f | π f = (s : ℝ≥0∞)} =
          (A ∩ {f | π f ≤ (s : ℝ≥0∞)}) \ {f | π f < (s : ℝ≥0∞)} := by
        ext f
        simp only [Set.mem_inter_iff, Set.mem_sdiff, Set.mem_ofPred_eq]
        constructor
        · rintro ⟨hfA, hfπ⟩
          exact ⟨⟨hfA, hfπ.le⟩, not_lt_of_ge hfπ.ge⟩
        · rintro ⟨⟨hfA, hfπle⟩, hfπge⟩
          exact ⟨hfA, le_antisymm hfπle (le_of_not_gt hfπge)⟩
      have hmeas : MeasurableSet[DLoc.filtration s] (A ∩ {f | π f = (s : ℝ≥0∞)}) := by
        rw [hset]
        exact (hAπ.2 s).diff (hπ.measurableSet_lt_of_countable_range hπc s)
      have hmeas0 : MeasurableSet (A ∩ {f | π f = (s : ℝ≥0∞)}) := hA0.inter
        ((measurableSet_singleton (s : ℝ≥0∞)).preimage hπm)
      calc
        _ = ∫ f in A ∩ {f | π f = (s : ℝ≥0∞)}, F (DLoc.shift s f) ∂P := by
          apply setIntegral_congr_fun hmeas0
          intro f hf
          have hπf : π f = (s : ℝ≥0∞) := hf.2
          change F (DLoc.shift (π f).toNNReal f) = F (DLoc.shift s f)
          rw [hπf, ENNReal.toNNReal_coe]
        _ = P.real (A ∩ {f | π f = (s : ℝ≥0∞)}) * ∫ f, F f ∂P :=
          integral_shift_mul_past hθ s hmeas hF hFb
  rw [← hunion, integral_iUnion hatom_meas hdisj hint]
  calc
    _ = ∑' r, P.real (atoms r) * ∫ f, F f ∂P := tsum_congr hatom
    _ = (∑' r, P.real (atoms r)) * ∫ f, F f ∂P := tsum_mul_right
    _ = _ := by
      congr 1
      change (∑' r, (P (atoms r)).toReal) = (P (⋃ r, atoms r)).toReal
      rw [measure_iUnion hdisj hatom_meas,
        ENNReal.tsum_toReal_eq (fun _ => measure_ne_top _ _)]

private theorem dyadicApprox_lt_add (n : ℕ) (τ : DLoc → ℝ≥0∞) {f : DLoc}
    (hf : τ f < ⊤) :
    dyadicApprox n τ f < τ f + 1 / ((n + 1 : ℕ) : ℝ≥0∞) := by
  have hmul : ((n + 1 : ℕ) : ℝ≥0∞) * τ f ≠ ⊤ :=
    ENNReal.mul_ne_top (by simp) (ne_of_lt hf)
  unfold dyadicApprox
  calc
    _ < (((n + 1 : ℕ) : ℝ≥0∞) * τ f + 1) / ((n + 1 : ℕ) : ℝ≥0∞) :=
      ENNReal.div_lt_div_right (by simp) (by simp) (ENat.ceil_lt_add_one hmul)
    _ = (((n + 1 : ℕ) : ℝ≥0∞) * τ f) / ((n + 1 : ℕ) : ℝ≥0∞) +
        1 / ((n + 1 : ℕ) : ℝ≥0∞) := ENNReal.add_div
    _ = _ := by rw [mul_div_assoc, ENNReal.mul_div_cancel] <;> simp

private theorem dyadicApprox_lt_top (n : ℕ) (τ : DLoc → ℝ≥0∞) {f : DLoc}
    (hf : τ f < ⊤) : dyadicApprox n τ f < ⊤ := by
  apply (dyadicApprox_lt_add n τ hf).trans
  exact ENNReal.add_lt_top.mpr ⟨hf, ENNReal.div_lt_top (by simp) (by simp)⟩

private theorem dyadicApprox_eq_top_of (n : ℕ) (τ : DLoc → ℝ≥0∞) {f : DLoc}
    (h : dyadicApprox n τ f = ⊤) : τ f = ⊤ := by
  by_contra hf
  have hlt := dyadicApprox_lt_top n τ (lt_top_iff_ne_top.mpr hf)
  rw [h] at hlt
  exact (lt_irrefl _ hlt)

private theorem tendsto_dyadicApprox (τ : DLoc → ℝ≥0∞) {f : DLoc} (hf : τ f < ⊤) :
    Tendsto (fun n => dyadicApprox n τ f) atTop (𝓝 (τ f)) := by
  have heps : Tendsto (fun n : ℕ => (1 / ((n + 1 : ℕ) : ℝ≥0∞))) atTop (𝓝 0) := by
    simpa only [Function.comp_def, one_div, Nat.cast_add, Nat.cast_one] using
      (ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa only [add_zero] using tendsto_const_nhds.add heps)
  · exact fun n => le_dyadicApprox n τ f
  · exact fun n => (dyadicApprox_lt_add n τ hf).le

private theorem tendsto_dyadicApprox_toNNReal (τ : DLoc → ℝ≥0∞) {f : DLoc}
    (hf : τ f < ⊤) :
    Tendsto (fun n => (dyadicApprox n τ f).toNNReal) atTop (𝓝 (τ f).toNNReal) := by
  exact (ENNReal.tendsto_toNNReal (ne_of_lt hf)).comp (tendsto_dyadicApprox τ hf)

private theorem map_restrict_shiftAt_cond_finiteDimensional {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) (U : ℝ≥0) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    (hA0 : (stableLocalLaw θ : Measure DLoc) A ≠ 0)
    (q : Finset (Set.Icc (0 : ℝ) (U : ℝ))) :
    ((stableLocalLaw θ : Measure DLoc)[|A].map
        (fun f : DLoc => fun t : q => DLoc.restrict U (DLoc.shiftAt τ f) t)) =
      (stableLocalLaw θ : Measure DLoc).map
        (fun f : DLoc => fun t : q => DLoc.restrict U (DLoc.shift 0 f) t) := by
  let P : Measure DLoc := stableLocalLaw θ
  let E : (DLoc → ℝ≥0∞) → DLoc → (q → ℝ) :=
    fun σ f u => DLoc.restrict U (DLoc.shiftAt σ f) u
  change P[|A].map (E τ) = P.map (E (fun _ => 0))
  have hE_measurable {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ) :
      Measurable (E σ) := by
    apply Measurable.of_eval
    intro u
    exact (BGW.Skorokhod.measurable_eval u.1).comp
      ((DLoc.measurable_restrict U).comp (DLoc.measurable_shiftAt hσ))
  have hpoint {f : DLoc} (hf : τ f < ⊤) :
      Tendsto (fun n => E (dyadicApprox n τ) f) atTop (𝓝 (E τ f)) := by
    have htend : Tendsto (fun n => (dyadicApprox n τ f).toNNReal) atTop
        (𝓝 (τ f).toNNReal) := tendsto_dyadicApprox_toNNReal τ hf
    rw [tendsto_pi_nhds]
    intro u
    let uu : ℝ≥0 := ⟨u.1.1, u.1.2.1⟩
    have hle (n : ℕ) : (τ f).toNNReal ≤ (dyadicApprox n τ f).toNNReal :=
      (ENNReal.toNNReal_le_toNNReal (ne_of_lt hf)
        (ne_of_lt (dyadicApprox_lt_top n τ hf))).mpr (le_dyadicApprox n τ f)
    have ht : Tendsto (fun n => (dyadicApprox n τ f).toNNReal + uu) atTop
        (𝓝[≥] ((τ f).toNNReal + uu)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨htend.add tendsto_const_nhds, Eventually.of_forall fun n => by
        show (τ f).toNNReal + uu ≤ (dyadicApprox n τ f).toNNReal + uu
        simpa only [add_comm] using add_le_add_right (hle n) uu⟩
    have heval : Tendsto (fun n => f.1 ((dyadicApprox n τ f).toNNReal + uu)) atTop
        (𝓝 (f.1 ((τ f).toNNReal + uu))) :=
      (continuousWithinAt_Ioi_iff_Ici.mp
        (f.2.isRightContinuous ((τ f).toNNReal + uu))).tendsto.comp ht
    have hs : Tendsto (fun n => f.1 (dyadicApprox n τ f).toNNReal) atTop
        (𝓝 (f.1 (τ f).toNNReal)) := by
      apply (continuousWithinAt_Ioi_iff_Ici.mp
        (f.2.isRightContinuous (τ f).toNNReal)).tendsto.comp
      exact tendsto_nhdsWithin_iff.mpr ⟨htend, Eventually.of_forall hle⟩
    exact heval.sub hs
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  let G : DLoc → ℝ := fun g => F (fun u : q => DLoc.restrict U g u)
  have hGm : Measurable G := by
    apply F.measurable.comp
    apply Measurable.of_eval
    intro u
    exact (BGW.Skorokhod.measurable_eval u.1).comp (DLoc.measurable_restrict U)
  have hGb : ∃ C : ℝ, ∀ g, |G g| ≤ C := by
    exact ⟨‖F‖, fun g => F.norm_coe_le_norm _⟩
  have hmass : (P A)⁻¹.toReal * P.real A = 1 := by
    rw [ENNReal.toReal_inv, measureReal_def]
    exact inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hA0, measure_ne_top P A⟩)
  have hseq (n : ℕ) : (∫ x, F x ∂(P[|A].map (E (dyadicApprox n τ)))) =
      ∫ x, F x ∂(P.map (E (fun _ => 0))) := by
    have hfact : (∫ f in A, F (E (dyadicApprox n τ) f) ∂P) =
        P.real A * ∫ f, G f ∂P := by
      change (∫ f in A, G (DLoc.shiftAt (dyadicApprox n τ) f) ∂P) = _
      exact integral_shiftAt_mul_past_of_countable_range hθ hτ
        (isStoppingTime_dyadicApprox hτ n) (countable_range_dyadicApprox n τ)
        (le_dyadicApprox n τ) (fun f => dyadicApprox_eq_top_of n τ) hA hAτ hGm hGb
    calc
      _ = ∫ f, F (E (dyadicApprox n τ) f) ∂P[|A] :=
        integral_map (hE_measurable (isStoppingTime_dyadicApprox hτ n)).aemeasurable
          F.measurable.aestronglyMeasurable
      _ = (P A)⁻¹.toReal * ∫ f, F (E (dyadicApprox n τ) f) ∂(P.restrict A) := by
        rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul]
      _ = (P A)⁻¹.toReal * ∫ f in A, F (E (dyadicApprox n τ) f) ∂P := by rfl
      _ = (P A)⁻¹.toReal * (P.real A * ∫ f, G f ∂P) := by rw [hfact]
      _ = ∫ f, G f ∂P := by rw [← mul_assoc, hmass, one_mul]
      _ = _ := by
        symm
        calc
          _ = ∫ f, F (E (fun _ => 0) f) ∂P :=
            integral_map (hE_measurable (isStoppingTime_const DLoc.filtration 0)).aemeasurable
              F.measurable.aestronglyMeasurable
          _ = ∫ f, G (DLoc.shift 0 f) ∂P := rfl
          _ = ∫ g, G g ∂P.map (DLoc.shift 0) := by
            rw [integral_map (DLoc.measurable_shift_fixed 0).aemeasurable
              hGm.aestronglyMeasurable]
          _ = _ := by rw [map_shift_stableLocalLaw hθ]
  have hlim : Tendsto (fun n => ∫ x, F x ∂(P[|A].map (E (dyadicApprox n τ)))) atTop
      (𝓝 (∫ x, F x ∂(P[|A].map (E τ)))) := by
    have hmapInt {σ : DLoc → ℝ≥0∞} (hσ : IsStoppingTime DLoc.filtration σ) :
        (∫ x, F x ∂(P[|A].map (E σ))) = ∫ f, F (E σ f) ∂P[|A] :=
      integral_map (hE_measurable hσ).aemeasurable F.measurable.aestronglyMeasurable
    simp_rw [hmapInt (isStoppingTime_dyadicApprox hτ _)]
    rw [hmapInt hτ]
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => ‖F‖)
    · exact Eventually.of_forall fun n =>
        (F.measurable.comp (hE_measurable (isStoppingTime_dyadicApprox hτ n))).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun f => F.norm_coe_le_norm _
    · exact integrable_const _
    · have hAmeas : MeasurableSet A := by
        have hm : MeasurableSet[⨆ t, DLoc.filtration t] A := hA.1
        rwa [iSup_filtration] at hm
      have hmem : ∀ᵐ f ∂P[|A], f ∈ A := by
        exact Measure.ae_smul_measure (ae_restrict_mem hAmeas) _
      filter_upwards [hmem] with f hf
      exact (F.continuous.tendsto _).comp (hpoint (hAτ hf))
  exact tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hseq n).symm))

private theorem map_shiftAt_cond_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    (hA0 : (stableLocalLaw θ : Measure DLoc) A ≠ 0) :
    (stableLocalLaw θ : Measure DLoc)[|A].map (DLoc.shiftAt τ) =
      (stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let L : ProbabilityMeasure DLoc := ⟨P[|A], cond_isProbabilityMeasure hA0⟩
  have hL : L.map (DLoc.shiftAt τ) = stableLocalLaw θ := (eq_stableLocalLaw_iff hθ).mpr (by
    intro U hU
    have hPM : (L.map (DLoc.shiftAt τ)).map (DLoc.restrict U) = stableProcessLaw θ U := by
      apply BGW.Skorokhod.ext_of_finiteDimensional dense_univ U.2 (Set.mem_univ _)
      intro q hq
      apply ProbabilityMeasure.toMeasure_injective
      erw [ProbabilityMeasure.toMeasure_map]
      erw [ProbabilityMeasure.toMeasure_map]
      erw [ProbabilityMeasure.toMeasure_map]
      erw [ProbabilityMeasure.toMeasure_map]
      have hEval : Measurable (fun g : D (U : ℝ) ℝ => fun u : q => g u.1) :=
        Measurable.of_eval fun u => BGW.Skorokhod.measurable_eval u.1
      erw [Measure.map_map hEval (DLoc.measurable_restrict U),
        Measure.map_map (hEval.comp (DLoc.measurable_restrict U)) (DLoc.measurable_shiftAt hτ),
        ← map_restrict_stableLocalLaw hθ hU, Measure.map_map hEval (DLoc.measurable_restrict U),
        ← map_shift_stableLocalLaw hθ 0,
        Measure.map_map (hEval.comp (DLoc.measurable_restrict U))
          (DLoc.measurable_shift_fixed 0)]
      exact map_restrict_shiftAt_cond_finiteDimensional hθ hτ U hA hAτ hA0 q
    exact congrArg (fun R : ProbabilityMeasure (D (U : ℝ) ℝ) =>
      (R : Measure (D (U : ℝ) ℝ))) hPM)
  exact congrArg (fun R : ProbabilityMeasure DLoc => (R : Measure DLoc)) hL

/-- **Strong Markov property, integral form.** For `A` in the stopped σ-algebra of `τ` with
`A ⊆ {τ < ⊤}` and bounded Borel `F` on `DLoc`,
`∫_A F(shiftAt τ f) dP = P(A) · ∫ F dP`. (`A = ∅` and `τ ≡ 0` allowed.) -/
theorem integral_shiftAt_mul_past {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.shiftAt τ f) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A * ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  -- `hFb` is part of the stated interface (bounded tests); this proof does not need it.
  have _hFb := hFb
  by_cases hA0 : P A = 0
  · have hzero : P.restrict A = 0 := Measure.restrict_eq_zero.mpr hA0
    change (∫ f in A, F (DLoc.shiftAt τ f) ∂P) = P.real A * ∫ f, F f ∂P
    rw [hzero]
    simp [hA0, measureReal_def]
  · have hlaw := map_shiftAt_cond_stableLocalLaw hθ hτ hA hAτ hA0
    have hmapint : (∫ f, F f ∂P[|A].map (DLoc.shiftAt τ)) = ∫ f, F f ∂P := by
      rw [hlaw]
    rw [integral_map (DLoc.measurable_shiftAt hτ).aemeasurable hF.aestronglyMeasurable,
      ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul] at hmapint
    have hmass : P.real A * (P A)⁻¹.toReal = 1 := by
      rw [ENNReal.toReal_inv, measureReal_def, mul_comm]
      exact inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hA0, measure_ne_top P A⟩)
    calc
      _ = P.real A * ((P A)⁻¹.toReal * ∫ f in A, F (DLoc.shiftAt τ f) ∂P) := by
        rw [← mul_assoc, hmass, one_mul]
      _ = _ := by rw [hmapint]

/-- **Independence form.** Under the conditional probability given `{τ < ⊤}` (when that event has
positive probability), the stopped σ-algebra restricted to the event is independent of the
post-`τ` path. Stated with the restricted (non-normalised) measure, so that the null case is
vacuous-true and no division is needed: for stopped events `A ⊆ {τ < ⊤}` and Borel `B`,
`P(A ∩ shiftAt τ ⁻¹ B) = P(A) · P(B)`. -/
theorem measure_inter_preimage_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {B : Set DLoc} (hB : MeasurableSet B) :
    (stableLocalLaw θ : Measure DLoc) (A ∩ DLoc.shiftAt τ ⁻¹' B) =
      (stableLocalLaw θ : Measure DLoc) A * (stableLocalLaw θ : Measure DLoc) B := by
  let P : Measure DLoc := stableLocalLaw θ
  by_cases hA0 : P A = 0
  · have hzero : P (A ∩ DLoc.shiftAt τ ⁻¹' B) = 0 := measure_mono_null inter_subset_left hA0
    change P (A ∩ DLoc.shiftAt τ ⁻¹' B) = P A * P B
    rw [hzero, hA0, zero_mul]
  · have hlaw := map_shiftAt_cond_stableLocalLaw hθ hτ hA hAτ hA0
    have heval := congrArg (fun μ : Measure DLoc => μ B) hlaw
    rw [Measure.map_apply (DLoc.measurable_shiftAt hτ) hB, ProbabilityTheory.cond,
      Measure.coe_smul, Pi.smul_apply, Measure.restrict_apply ((DLoc.measurable_shiftAt hτ) hB),
      smul_eq_mul] at heval
    rw [Set.inter_comm] at heval
    change P (A ∩ DLoc.shiftAt τ ⁻¹' B) = P A * P B
    change (P A)⁻¹ * P (A ∩ DLoc.shiftAt τ ⁻¹' B) = P B at heval
    calc
      _ = (P A * (P A)⁻¹) * P (A ∩ DLoc.shiftAt τ ⁻¹' B) := by
        rw [ENNReal.mul_inv_cancel hA0 (measure_ne_top P A), one_mul]
      _ = P A * ((P A)⁻¹ * P (A ∩ DLoc.shiftAt τ ⁻¹' B)) := by rw [mul_assoc]
      _ = _ := by rw [heval]

/-- **Law of the post-`τ` path.** Conditionally on `{τ < ⊤}` (i.e. under the restriction of `P`
to it), `shiftAt τ` has the law `stableLocalLaw θ`, scaled by the mass of `{τ < ⊤}`. -/
theorem map_shiftAt_restrict_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) :
    ((stableLocalLaw θ : Measure DLoc).restrict {f | τ f < ⊤}).map (DLoc.shiftAt τ) =
      (stableLocalLaw θ : Measure DLoc) {f | τ f < ⊤} • (stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (DLoc.measurable_shiftAt hτ) hB,
    Measure.restrict_apply ((DLoc.measurable_shiftAt hτ) hB), Measure.coe_smul, Pi.smul_apply,
    smul_eq_mul]
  rw [Set.inter_comm]
  exact measure_inter_preimage_shiftAt hθ hτ (DLoc.measurableSet_lt_top_stopped hτ)
    Subset.rfl hB

/-- **Compact-window form**: the post-`τ` path cut at horizon `U`. -/
theorem integral_futureSegmentAt_mul_past {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) (U : ℝ≥0) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A) (hAτ : A ⊆ {f | τ f < ⊤})
    {F : D (U : ℝ) ℝ → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.restrict U (DLoc.shiftAt τ f)) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A *
        ∫ g, F g ∂(stableProcessLaw θ (U : ℝ) : Measure (D (U : ℝ) ℝ)) := by
  have hbound : ∃ C : ℝ, ∀ f : DLoc, |(F ∘ DLoc.restrict U) f| ≤ C := by
    obtain ⟨C, hC⟩ := hFb
    exact ⟨C, fun f => hC _⟩
  change (∫ f in A, (F ∘ DLoc.restrict U) (DLoc.shiftAt τ f) ∂(stableLocalLaw θ)) = _
  rw [integral_shiftAt_mul_past hθ hτ hA hAτ
    (hF.comp (DLoc.measurable_restrict U)) hbound]
  have hmap : (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict U) =
      (stableProcessLaw θ (U : ℝ) : Measure (D (U : ℝ) ℝ)) := by
    by_cases hU : U = 0
    · subst U
      exact map_restrict_zero_stableLocalLaw hθ
    · exact map_restrict_stableLocalLaw hθ (pos_iff_ne_zero.mpr hU)
  rw [← hmap, integral_map (DLoc.measurable_restrict U).aemeasurable hF.aestronglyMeasurable]
  rfl

/-- **Almost surely finite stopping time**: when `τ < ⊤` a.s., the post-`τ` path has law
`stableLocalLaw θ` and is independent of the whole stopped σ-algebra. -/
theorem integral_shiftAt_mul_past_of_ae_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    (hfin : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤) {A : Set DLoc}
    (hA : MeasurableSet[hτ.measurableSpace] A)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.shiftAt τ f) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A * ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let S : Set DLoc := {f | τ f < ⊤}
  have hS : MeasurableSet[hτ.measurableSpace] S := DLoc.measurableSet_lt_top_stopped hτ
  have hAS : A ∩ S =ᵐ[P] A := by
    filter_upwards [hfin] with f hf
    apply propext
    change (f ∈ A ∧ τ f < ⊤) ↔ f ∈ A
    exact and_iff_left hf
  have hfact := integral_shiftAt_mul_past hθ hτ (hA.inter hS) inter_subset_right hF hFb
  rw [Measure.restrict_congr_set hAS, measureReal_congr hAS] at hfact
  exact hfact

/-- **Strong Markov, conditional-expectation form** (bounded test, on `{τ < ⊤}`): relative to the
stopped σ-algebra, `E[1_{τ<⊤} F(shiftAt τ) | F_τ] = 1_{τ<⊤} E[F]` a.s. -/
theorem condExp_indicator_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[
        {f | τ f < ⊤}.indicator (fun f => F (DLoc.shiftAt τ f)) | hτ.measurableSpace]
      =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      {f | τ f < ⊤}.indicator (fun _ => ∫ g, F g ∂(stableLocalLaw θ : Measure DLoc)) := by
  let P : Measure DLoc := stableLocalLaw θ
  let S : Set DLoc := {f | τ f < ⊤}
  let I : ℝ := ∫ g, F g ∂P
  have hS : MeasurableSet[hτ.measurableSpace] S := DLoc.measurableSet_lt_top_stopped hτ
  have hS0 : MeasurableSet S := by
    have hmS : MeasurableSet[⨆ t, DLoc.filtration t] S := hS.1
    rwa [iSup_filtration] at hmS
  have hm : hτ.measurableSpace ≤ (inferInstance : MeasurableSpace DLoc) := by
    intro B hB
    have hB' : MeasurableSet[⨆ t, DLoc.filtration t] B := hB.1
    rwa [iSup_filtration] at hB'
  have hint : Integrable (S.indicator (fun f => F (DLoc.shiftAt τ f))) P :=
    (integrable_shiftAt hτ hF hFb).indicator hS0
  apply (ae_eq_condExp_of_forall_setIntegral_eq hm hint
    (g := S.indicator (fun _ => I)) ?_ ?_ ?_).symm
  · intro B hB _
    exact ((integrable_const I).indicator hS0).integrableOn
  · intro B hB _
    rw [setIntegral_indicator hS0, setIntegral_indicator hS0, setIntegral_const, smul_eq_mul]
    exact (integral_shiftAt_mul_past hθ hτ (hB.inter hS) inter_subset_right hF hFb).symm
  · exact (stronglyMeasurable_const.indicator hS).aestronglyMeasurable

/-- Version without indicators when `τ < ⊤` a.s. -/
theorem condExp_shiftAt_of_ae_lt_top {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ)
    (hfin : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[(fun f => F (DLoc.shiftAt τ f)) | hτ.measurableSpace]
      =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun _ => ∫ g, F g ∂(stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  have hfun : {f | τ f < ⊤}.indicator (fun f => F (DLoc.shiftAt τ f)) =ᵐ[P]
      fun f => F (DLoc.shiftAt τ f) := by
    filter_upwards [hfin] with f hf
    simp [hf]
  have hconst : {f | τ f < ⊤}.indicator (fun _ => ∫ g, F g ∂P) =ᵐ[P]
      fun _ => ∫ g, F g ∂P := by
    filter_upwards [hfin] with f hf
    simp [hf]
  calc
    P[(fun f => F (DLoc.shiftAt τ f)) | hτ.measurableSpace] =ᵐ[P]
        P[{f | τ f < ⊤}.indicator (fun f => F (DLoc.shiftAt τ f)) | hτ.measurableSpace] :=
      condExp_congr_ae hfun.symm
    _ =ᵐ[P] {f | τ f < ⊤}.indicator (fun _ => ∫ g, F g ∂P) :=
      condExp_indicator_shiftAt hθ hτ hF hFb
    _ =ᵐ[P] _ := hconst

end BGW.StableTrees
