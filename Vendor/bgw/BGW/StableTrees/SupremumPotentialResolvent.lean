/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumPotentialBasic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Group.Integral

/-!
# Bounded reflected resolvents

Measurability, positive-rate bounds and linearity of the reflected resolvent.

Reference: A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed.,
Springer, 2014, Chapter 8.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

private noncomputable def discountedPathFunctional (q : ℝ) (k : ℝ → ℝ) (f : DLoc) : ℝ :=
  ∫ t in Ioi (0 : ℝ), Real.exp (-q * t) * k (f.1 t.toNNReal)

private theorem measurable_discountedPathFunctional (q : ℝ) {k : ℝ → ℝ} (hk : Measurable k) :
    Measurable (discountedPathFunctional q k) := by
  have hf : Measurable (fun p : DLoc × ℝ => Real.exp (-q * p.2) * k (p.1.1 p.2.toNNReal)) := by
    apply Measurable.mul (by fun_prop)
    exact hk.comp (DLoc.measurable_eval₂.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd)))
  exact hf.stronglyMeasurable.integral_prod_right'.measurable

private theorem discountedPathFunctional_bound {q : ℝ} (hq : 0 < q) {k : ℝ → ℝ}
    (hk : Measurable k) {C : ℝ} (hC : ∀ e, |k e| ≤ C) (f : DLoc) :
    IntegrableOn (fun t => Real.exp (-q * t) * k (f.1 t.toNNReal)) (Ioi 0) ∧
      |discountedPathFunctional q k f| ≤ C / q := by
  have hm : Measurable (fun t : ℝ => Real.exp (-q * t) * k (f.1 t.toNNReal)) := by
    apply Measurable.mul (by fun_prop)
    exact hk.comp ((DLoc.measurable_eval₂.comp
      (measurable_const.prodMk measurable_real_toNNReal)))
  have hd : IntegrableOn (fun t : ℝ => C * Real.exp (-q * t)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_neg_of_pos hq) 0).const_mul C
  have hb (t : ℝ) : ‖Real.exp (-q * t) * k (f.1 t.toNNReal)‖ ≤ C * Real.exp (-q * t) := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hC _) (Real.exp_pos _).le).trans_eq (mul_comm _ _)
  have hi := hd.mono' hm.aestronglyMeasurable (ae_of_all _ hb)
  refine ⟨hi, ?_⟩
  change |∫ t in Ioi (0 : ℝ), Real.exp (-q * t) * k (f.1 t.toNNReal)| ≤ _
  calc
    _ ≤ ∫ t in Ioi (0 : ℝ), ‖Real.exp (-q * t) * k (f.1 t.toNNReal)‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t in Ioi (0 : ℝ), C * Real.exp (-q * t) :=
      integral_mono_ae hi.norm hd (ae_of_all _ hb)
    _ = C / q := by
      rw [integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos hq) 0]
      simp only [mul_zero, Real.exp_zero]
      ring

/-- The reflected resolvent is Borel at every real rate. -/
theorem measurable_reflectedResolvent {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ) {k : ℝ → ℝ}
    (hk : Measurable k) (hkb : ∃ C, ∀ e, |k e| ≤ C) : Measurable (reflectedResolvent θ q k) := by
  -- `hθ` is part of the stated interface; this holds for every θ.
  have _hθ := hθ
  -- `hkb` is part of the stated interface; this holds for every bounded `k`.
  have _hkb := hkb
  have hm : Measurable (fun p : ℝ × DLoc =>
      discountedPathFunctional q k (supReflectedFromLoc p.1.toNNReal p.2)) :=
    (measurable_discountedPathFunctional q hk).comp (measurable_supReflectedFromLoc.comp
      ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  exact hm.stronglyMeasurable.integral_prod_right'.measurable

/-- `|U_q k| ≤ C/q`, on all of `ℝ`. -/
theorem abs_reflectedResolvent_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {k : ℝ → ℝ} (hk : Measurable k) {C : ℝ} (hC : ∀ e, |k e| ≤ C) (y : ℝ) :
    |reflectedResolvent θ q k y| ≤ C / q := by
  -- `hθ` is part of the stated interface; this holds for every θ.
  have _hθ := hθ
  change |∫ f, discountedPathFunctional q k (supReflectedFromLoc y.toNNReal f)
    ∂(stableLocalLaw θ : Measure DLoc)| ≤ C / q
  rw [← Real.norm_eq_abs]
  have hb : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ‖discountedPathFunctional q k (supReflectedFromLoc y.toNNReal f)‖ ≤ C / q :=
    ae_of_all _ (fun f => by simpa only [Real.norm_eq_abs] using
      (discountedPathFunctional_bound hq hk hC (supReflectedFromLoc y.toNNReal f)).2)
  simpa using norm_integral_le_of_norm_le_const hb

private theorem integrable_reflected_pathFunctional {θ q : ℝ} (hq : 0 < q) {k : ℝ → ℝ}
    (hk : Measurable k) {C : ℝ} (hC : ∀ e, |k e| ≤ C) (y : ℝ) :
    Integrable (fun f => discountedPathFunctional q k (supReflectedFromLoc y.toNNReal f))
      (stableLocalLaw θ : Measure DLoc) := by
  have hm : Measurable (fun f => discountedPathFunctional q k (supReflectedFromLoc y.toNNReal f)) :=
    (measurable_discountedPathFunctional q hk).comp
      (measurable_supReflectedFromLoc.comp (measurable_const.prodMk measurable_id))
  apply Integrable.of_bound hm.aestronglyMeasurable (C / q)
  exact ae_of_all _ (fun f => (discountedPathFunctional_bound hq hk hC
    (supReflectedFromLoc y.toNNReal f)).2)

/-- Subtraction of bounded reflected resolvents at positive rates. -/
theorem reflectedResolvent_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    {k₁ k₂ : ℝ → ℝ} (h₁ : Measurable k₁) (h₂ : Measurable k₂) (b₁ : ∃ C, ∀ e, |k₁ e| ≤ C)
    (b₂ : ∃ C, ∀ e, |k₂ e| ≤ C) (y : ℝ) :
    reflectedResolvent θ q (fun r => k₁ r - k₂ r) y =
      reflectedResolvent θ q k₁ y - reflectedResolvent θ q k₂ y := by
  -- `hθ` is part of the stated interface; this holds for every θ.
  have _hθ := hθ
  obtain ⟨C₁, hC₁⟩ := b₁
  obtain ⟨C₂, hC₂⟩ := b₂
  have hi₁ := integrable_reflected_pathFunctional (θ := θ) hq h₁ hC₁ y
  have hi₂ := integrable_reflected_pathFunctional (θ := θ) hq h₂ hC₂ y
  have he (f : DLoc) : discountedPathFunctional q (fun r => k₁ r - k₂ r)
      (supReflectedFromLoc y.toNNReal f) =
      discountedPathFunctional q k₁ (supReflectedFromLoc y.toNNReal f) -
        discountedPathFunctional q k₂ (supReflectedFromLoc y.toNNReal f) := by
    unfold discountedPathFunctional
    simp_rw [mul_sub]
    exact integral_sub
      (discountedPathFunctional_bound hq h₁ hC₁ (supReflectedFromLoc y.toNNReal f)).1
      (discountedPathFunctional_bound hq h₂ hC₂ (supReflectedFromLoc y.toNNReal f)).1
  change (∫ f, discountedPathFunctional q (fun r => k₁ r - k₂ r)
    (supReflectedFromLoc y.toNNReal f) ∂(stableLocalLaw θ : Measure DLoc)) = _
  simp_rw [he]
  exact integral_sub hi₁ hi₂

private theorem integral_tail_translate (F : ℝ → ℝ) (s : ℝ) :
    (∫ t in Ioi s, F t) = ∫ u in Ioi 0, F (s + u) := by
  rw [← integral_indicator measurableSet_Ioi,
    ← integral_add_left_eq_self ((Ioi s).indicator F) s]
  have he : (fun u => (Ioi s).indicator F (s + u)) = (Ioi 0).indicator (fun u => F (s + u)) := by
    funext u
    have hh : s < s + u ↔ 0 < u := by constructor <;> intro h <;> linarith
    simp only [indicator_apply, mem_Ioi, hh]
  rw [he, integral_indicator measurableSet_Ioi]

/-- Conditional resolvent identity at every positive rate. -/
theorem condExp_reflectedResolvent_tail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    (x s : ℝ≥0) {k : ℝ → ℝ} (hk : Measurable k) (hkb : ∃ C, ∀ e, |k e| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[fun f =>
      ∫ t in Ioi (s : ℝ), Real.exp (-q * t) * k (supReflectedFrom x f t.toNNReal) |
        DLoc.filtration s] =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => Real.exp (-q * (s : ℝ)) * reflectedResolvent θ q k (supReflectedFrom x f s) := by
  obtain ⟨C, hC⟩ := hkb
  let G := discountedPathFunctional q k
  have hG : Measurable G := measurable_discountedPathFunctional q hk
  have hb : ∃ D, ∀ f, |G f| ≤ D :=
    ⟨C / q, fun f => (discountedPathFunctional_bound hq hk hC f).2⟩
  have hM := condExp_supReflectedFromLoc_markov hθ x s hG hb
  let H := fun f => G (supReflectedFromLoc (supReflectedFrom x f s).toNNReal (DLoc.shift s f))
  have he (f : DLoc) : (∫ t in Ioi (s : ℝ),
      Real.exp (-q * t) * k (supReflectedFrom x f t.toNNReal)) =
      Real.exp (-q * (s : ℝ)) * H f := by
    rw [integral_tail_translate]
    change (∫ u in Ioi 0, Real.exp (-q * ((s : ℝ) + u)) *
      k (supReflectedFrom x f ((s : ℝ) + u).toNNReal)) =
      Real.exp (-q * (s : ℝ)) * (∫ u in Ioi 0, Real.exp (-q * u) *
        k (supReflectedFrom (supReflectedFrom x f s).toNNReal (DLoc.shift s f) u.toNNReal))
    rw [← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    change Real.exp (-q * ((s : ℝ) + u)) * k (supReflectedFrom x f ((s : ℝ) + u).toNNReal) = _
    have hu0 : 0 < u := hu
    have ht : ((s : ℝ) + u).toNNReal = s + u.toNNReal := by
      ext
      rw [Real.coe_toNNReal _ (by positivity), NNReal.coe_add, Real.coe_toNNReal _ hu0.le]
    rw [ht, supReflectedFrom_restart,
      show -q * ((s : ℝ) + u) = -q * (s : ℝ) + -q * u by ring, Real.exp_add]
    ring
  have hscale := condExp_smul (μ := (stableLocalLaw θ : Measure DLoc))
    (Real.exp (-q * (s : ℝ))) H (DLoc.filtration s)
  have hcond := condExp_congr_ae (μ := (stableLocalLaw θ : Measure DLoc))
    (m := DLoc.filtration s) (ae_of_all _ he)
  filter_upwards [hcond, hscale, hM] with f hf hs hm
  rw [hf]
  change (stableLocalLaw θ : Measure DLoc)[Real.exp (-q * (s : ℝ)) • H | DLoc.filtration s] f = _
  rw [hs]
  change Real.exp (-q * (s : ℝ)) *
    (stableLocalLaw θ : Measure DLoc)[H | DLoc.filtration s] f = _
  rw [hm]
  rfl

/-- The reflected family satisfies the rate-one resolvent Markov property. -/
theorem resolventMarkov_supReflectedFrom {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) {k : ℝ → ℝ}
    (hk : Measurable k) (hkb : ∃ C, ∀ e, |k e| ≤ C) :
    ResolventMarkov DLoc.filtration (stableLocalLaw θ : Measure DLoc)
      (fun t f => supReflectedFrom x f t) k (reflectedResolvent θ 1 k) := by
  intro s
  simpa only [neg_one_mul] using condExp_reflectedResolvent_tail hθ zero_lt_one x s hk hkb

private theorem abs_supOccKernel_le {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    |supOccKernel ε r| ≤ ε⁻¹ := by
  obtain ⟨h0, h1⟩ := supOccKernel_mem_Icc hε r
  rwa [abs_of_nonneg h0]

/-- The difference of two occupation kernels has the corresponding difference resolvent. -/
theorem resolventMarkov_supReflectedFrom_sub {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ResolventMarkov DLoc.filtration (stableLocalLaw θ : Measure DLoc)
      (fun t f => supReflectedFrom x f t) (fun r => supOccKernel ε r - supOccKernel η r)
      (fun y => supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y) := by
  have hεb : ∃ C, ∀ r, |supOccKernel ε r| ≤ C := ⟨ε⁻¹, abs_supOccKernel_le hε⟩
  have hηb : ∃ C, ∀ r, |supOccKernel η r| ≤ C := ⟨η⁻¹, abs_supOccKernel_le hη⟩
  have hb : ∃ C, ∀ r, |supOccKernel ε r - supOccKernel η r| ≤ C := by
    refine ⟨ε⁻¹ + η⁻¹, fun r => ?_⟩
    exact (abs_sub _ _).trans (add_le_add (abs_supOccKernel_le hε r) (abs_supOccKernel_le hη r))
  have he : reflectedResolvent θ 1 (fun r => supOccKernel ε r - supOccKernel η r) =
      fun y => supOccupationResolvent θ 1 ε y - supOccupationResolvent θ 1 η y := by
    funext y
    exact reflectedResolvent_sub hθ zero_lt_one (measurable_supOccKernel ε)
      (measurable_supOccKernel η) hεb hηb y
  rw [← he]
  exact resolventMarkov_supReflectedFrom hθ x
    ((measurable_supOccKernel ε).sub (measurable_supOccKernel η)) hb

end BGW.StableTrees
