/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureCompensationFinite

/-! General predictable compensation by increasing finite-box exhaustion.

See Bertoin, *Lévy Processes*, Chapter IV, and Kallenberg,
*Foundations of Modern Probability*, Chapters 12 and 22.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **General predictable compensation formula.**  For every `H : (ℝ≥0 × DLoc) × Excursion → ℝ≥0∞`
measurable for `predictableSigma ⊗ Borel(Excursion)`, with `μ_f = excursionPointMeasure f`:
`E ∫ H((x,f),e) μ_f(dx,de) = E ∫_0^∞ ∫ H((x,f),e) N(de) dx`.
Proof route: `π`-`λ` argument on the generating rectangles `(a,b] × F × A` using
`excursion_compensation_step` (with `Y = 1_F`), then monotone class; no pointwise approximation
is needed. -/
theorem excursion_compensation_predictable_general {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {H : (ℝ≥0 × DLoc) × Excursion → ℝ≥0∞}
    (hH : @Measurable _ _ (predictableSigma.prod inferInstance) _ H) :
    ∫⁻ f, ∫⁻ p, H ((p.1, f), p.2) ∂(excursionPointMeasure f)
        ∂(stableLocalLaw θ : Measure DLoc) =
      ∫⁻ f, ∫⁻ x, ∫⁻ e, H ((x, f), e) ∂(excursionMeasure θ) ∂lebNN
        ∂(stableLocalLaw θ : Measure DLoc) := by
  classical
  let P : Measure DLoc := stableLocalLaw θ
  let := sigmaFinite_excursionMeasure hθ
  let := sigmaFinite_lebNN
  let Rfull := (lebNN.prod P).prod (excursionMeasure θ)
  let E : ℕ → Set (ℝ≥0 × Excursion) := fun n =>
    Ioc 0 (n + 1 : ℝ≥0) ×ˢ excursionLifetimeSlab n
  let D : ℕ → Set ((ℝ≥0 × DLoc) × Excursion) := fun n =>
    (Ioc 0 (n + 1 : ℝ≥0) ×ˢ univ) ×ˢ excursionLifetimeSlab n
  have hEmono : Monotone E := by
    intro n m hnm
    exact Set.prod_mono (Ioc_subset_Ioc_right (by exact_mod_cast Nat.add_le_add_right hnm 1))
      (monotone_excursionLifetimeSlab hnm)
  have hDmono : Monotone D := by
    intro n m hnm
    exact Set.prod_mono
      (Set.prod_mono (Ioc_subset_Ioc_right (by exact_mod_cast Nat.add_le_add_right hnm 1))
        Subset.rfl) (monotone_excursionLifetimeSlab hnm)
  have hEu : (⋃ n, E n) = Ioi 0 ×ˢ univ := by
    ext p
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, hn⟩
      exact ⟨hn.1.1, mem_univ _⟩
    · intro hp
      obtain ⟨i, hi⟩ := exists_nat_gt p.1
      obtain ⟨j, hj⟩ := mem_iUnion.mp (iUnion_excursionLifetimeSlab ▸ mem_univ p.2)
      apply mem_iUnion.mpr
      refine ⟨max i j, ?_, monotone_excursionLifetimeSlab (le_max_right i j) hj⟩
      refine ⟨hp.1, hi.le.trans ?_⟩
      exact_mod_cast (le_max_left i j).trans (Nat.le_succ (max i j))
  have hDu : (⋃ n, D n) = (Ioi 0 ×ˢ univ) ×ˢ univ := by
    ext q
    have hh := congrArg (fun S => (q.1.1, q.2) ∈ S) hEu
    simpa only [mem_iUnion, D, E, mem_prod, mem_univ, and_true, eq_iff_iff] using hh
  have hEfull (f : DLoc) : (excursionPointMeasure f).restrict (⋃ n, E n) =
      excursionPointMeasure f := by
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (excursionPointMeasure_atZero f)] with p hp
    rw [hEu]
    have hp0 : p.1 ≠ 0 := by simpa using hp
    have hpPos : (0 : ℝ≥0) < p.1 := lt_of_le_of_ne bot_le hp0.symm
    exact ⟨hpPos, mem_univ _⟩
  have hDfull : Rfull.restrict (⋃ n, D n) = Rfull := by
    have hz : Rfull ((({0} : Set ℝ≥0) ×ˢ univ) ×ˢ univ) = 0 := by
      rw [Measure.prod_prod, Measure.prod_prod, lebNN_singleton_zero, zero_mul, zero_mul]
    apply Measure.restrict_eq_self_of_ae_mem
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with q hq
    rw [hDu]
    have hq0 : q.1.1 ≠ 0 := by simpa using hq
    have hqPos : (0 : ℝ≥0) < q.1.1 := lt_of_le_of_ne bot_le hq0.symm
    exact ⟨⟨hqPos, mem_univ _⟩, mem_univ _⟩
  let F : ℕ → DLoc → ℝ≥0∞ := fun n f =>
    ∫⁻ p in E n, H ((p.1, f), p.2) ∂(excursionPointMeasure f)
  have hFm (n : ℕ) : AEMeasurable (F n) P := by
    obtain ⟨ν, hν, hνfin, hae⟩ := exists_finite_modification_excursionPointMeasure hθ
      (n + 1) (1 / (n + 1)) (by positivity)
    let := hνfin
    have hm := (Measure.measurable_lintegral hH).comp
      (measurable_predictableMarkedMeasure hν)
    let : MeasurableSpace ((ℝ≥0 × DLoc) × Excursion) := predictableSigma.prod inferInstance
    apply hm.aemeasurable.congr
    filter_upwards [hae] with f hf
    have hs : @Measurable _ _ inferInstance (predictableSigma.prod inferInstance)
        (fun p : ℝ≥0 × Excursion => ((p.1, f), p.2)) :=
      ((measurable_predictable_timeSection f).comp measurable_fst).prodMk measurable_snd
    change (∫⁻ q, H q ∂predictableMarkedMeasure f (ν f)) = _
    calc
      _ = ∫⁻ p, H ((p.1, f), p.2) ∂ν f := lintegral_map hH hs
      _ = _ := by rw [hf]; rfl
  have hFmono : Monotone F := by
    intro n m hnm f
    exact lintegral_mono_set (hEmono hnm)
  have hlocal (n : ℕ) : (∫⁻ f, F n f ∂P) = ∫⁻ q in D n, H q ∂Rfull := by
    have hh := excursion_compensation_predictable_finite hθ (n + 1) (1 / (n + 1))
      (by positivity) hH
    change (∫⁻ f, F n f ∂P) =
      ∫⁻ q, H q ∂(((lebNN.prod P).prod (excursionMeasure θ)).restrict
        ((Ioc 0 (n + 1 : ℝ≥0) ×ˢ univ) ×ˢ excursionLifetimeSlab n))
    rw [← Measure.prod_restrict, ← Measure.restrict_prod_eq_prod_univ]
    exact hh
  have hid : @Measurable _ _ inferInstance (predictableSigma.prod inferInstance)
      (id : ((ℝ≥0 × DLoc) × Excursion) → _) :=
    ((measurable_id.mono le_rfl predictableSigma_le_prod).comp measurable_fst).prodMk
      measurable_snd
  have hHfull : Measurable H := hH.comp hid
  calc
    _ = ∫⁻ f, ⨆ n, F n f ∂P := by
      congr 1
      funext f
      rw [← setLIntegral_iUnion_of_directed _ hEmono.directed_le, hEfull]
    _ = ⨆ n, ∫⁻ f, F n f ∂P := lintegral_iSup' hFm (Eventually.of_forall fun f n m h => hFmono h f)
    _ = ⨆ n, ∫⁻ q in D n, H q ∂Rfull := by simp_rw [hlocal]
    _ = ∫⁻ q, H q ∂Rfull := by
      rw [← setLIntegral_iUnion_of_directed _ hDmono.directed_le, hDfull]
    _ = _ := by
      rw [show Rfull = (lebNN.prod P).prod (excursionMeasure θ) from rfl,
        lintegral_prod _ hHfull.aemeasurable,
        lintegral_prod _ hHfull.lintegral_prod_right'.aemeasurable]
      exact lintegral_lintegral_swap hHfull.lintegral_prod_right'.aemeasurable

end BGW.StableTrees
