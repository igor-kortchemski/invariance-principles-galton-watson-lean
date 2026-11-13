module

public import BGW.StableTrees.ForestLocalLimitWeights
public import BGW.Probability.SeparableRepresentation
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! Finite-mass weighted convergence. Adapted from BGW's mass-one Scheffé
argument: the approximating nonnegative weights need only have masses tending
to one. Integrability is explicit, so a zero totalized integral is not used as
evidence of integrability. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeWeighted

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

theorem tendsto_integral_abs_sub_of_mass_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {w : ℕ → Ω → ℝ} {w₀ : Ω → ℝ}
    (hw : ∀ k, Measurable (w k)) (hw₀ : Measurable w₀)
    (hnn : ∀ k ω, 0 ≤ w k ω) (hnn₀ : ∀ ω, 0 ≤ w₀ ω)
    (hi : ∀ k, Integrable (w k) P)
    (hmass : Tendsto (fun k => ∫ ω, w k ω ∂P) atTop (𝓝 1))
    (h10 : ∫ ω, w₀ ω ∂P = 1)
    (hconv : TendstoInMeasure P w atTop w₀) :
    Tendsto (fun k => ∫ ω, |w k ω - w₀ ω| ∂P) atTop (𝓝 0) := by
  have hi₀ := integrable_of_integral_eq_one h10
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hmsmono, hms⟩ := (hconv.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hm (k : ℕ) : Integrable (fun ω => min (w (ns (ms k)) ω) (w₀ ω)) P := by
    apply hi₀.mono' ((hw _).min hw₀).aestronglyMeasurable
    exact ae_of_all _ fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hnn _ _) (hnn₀ _))]
      exact min_le_right _ _
  have hlim : Tendsto (fun k => ∫ ω, min (w (ns (ms k)) ω) (w₀ ω) ∂P) atTop (𝓝 1) := by
    rw [← h10]
    apply tendsto_integral_of_dominated_convergence w₀
    · intro k
      exact ((hw _).min hw₀).aestronglyMeasurable
    · exact hi₀
    · intro k
      exact ae_of_all _ fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hnn _ _) (hnn₀ _))]
        exact min_le_right _ _
    · filter_upwards [hms] with ω hω
      simpa only [min_self, Function.comp_apply] using hω.min (tendsto_const_nhds (x := w₀ ω))
  have heq (k : ℕ) : (∫ ω, |w (ns (ms k)) ω - w₀ ω| ∂P) =
      (∫ ω, w (ns (ms k)) ω ∂P) + 1 - 2 * ∫ ω, min (w (ns (ms k)) ω) (w₀ ω) ∂P := by
    have hab (x y : ℝ) : |x - y| = x + y - 2 * min x y := by
      rcases le_total x y with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.2 h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.2 h)]; ring
    simp_rw [hab]
    rw [integral_sub
      (show Integrable (fun ω => w (ns (ms k)) ω + w₀ ω) P from (hi _).add hi₀)
      ((hm k).const_mul 2), integral_add (hi _) hi₀,
      integral_const_mul, h10]
  have hmass' := hmass.comp (hns.comp hmsmono.tendsto_atTop)
  simpa only [heq, Function.comp_def, show (1 : ℝ) + 1 - 2 * 1 = 0 by norm_num] using
    (hmass'.add_const 1).sub (hlim.const_mul 2)

/-- **Weighted convergence** (consequence): uniformly bounded measurable `F_k → F` in measure
and weights as above give `∫ F_k w_k → ∫ F w₀`. -/
theorem tendsto_integral_mul_of_mass_tendsto {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {w : ℕ → Ω → ℝ} {w₀ : Ω → ℝ}
    (hw : ∀ k, Measurable (w k)) (hw₀ : Measurable w₀)
    (hnn : ∀ k ω, 0 ≤ w k ω) (hnn₀ : ∀ ω, 0 ≤ w₀ ω)
    (hi : ∀ k, Integrable (w k) P)
    (hmass : Tendsto (fun k => ∫ ω, w k ω ∂P) atTop (𝓝 1))
    (h10 : ∫ ω, w₀ ω ∂P = 1)
    (hconv : TendstoInMeasure P w atTop w₀)
    {F : ℕ → Ω → ℝ} {F₀ : Ω → ℝ} {C : ℝ} (hF : ∀ k, Measurable (F k)) (hF₀ : Measurable F₀)
    (hC : ∀ k ω, |F k ω| ≤ C) (hC₀ : ∀ ω, |F₀ ω| ≤ C)
    (hFc : TendstoInMeasure P F atTop F₀) :
    Tendsto (fun k => ∫ ω, (F k ω * w k ω) ∂P) atTop (𝓝 (∫ ω, (F₀ ω * w₀ ω) ∂P)) := by
  have hi₀ := integrable_of_integral_eq_one h10
  have hL := tendsto_integral_abs_sub_of_mass_tendsto hw hw₀ hnn hnn₀ hi hmass h10 hconv
  have hip (k : ℕ) := (hi k).bdd_mul (hF k).aestronglyMeasurable
    (ae_of_all _ fun ω => (Real.norm_eq_abs _).symm ▸ hC k ω)
  have hip₀ := hi₀.bdd_mul hF₀.aestronglyMeasurable
    (ae_of_all _ fun ω => (Real.norm_eq_abs _).symm ▸ hC₀ ω)
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hmsmono, hms⟩ := (hFc.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  have hD : Tendsto (fun k => ∫ ω, (F (ns (ms k)) ω - F₀ ω) * w₀ ω ∂P)
      atTop (𝓝 0) := by
    have hbound : Integrable (fun ω => (2 * C) * w₀ ω) P := hi₀.const_mul _
    have hlim := tendsto_integral_of_dominated_convergence (fun ω => (2 * C) * w₀ ω)
      (fun k => (((hF _).sub hF₀).mul hw₀).aestronglyMeasurable) hbound
      (fun k => ae_of_all _ fun ω => ?_)
      (show ∀ᵐ ω ∂P, Tendsto (fun k => (F (ns (ms k)) ω - F₀ ω) * w₀ ω)
        atTop (𝓝 ((0 : Ω → ℝ) ω)) from ?_)
    · simpa using hlim
    · change ‖(F (ns (ms k)) ω - F₀ ω) * w₀ ω‖ ≤ _
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn₀ _)]
      exact mul_le_mul_of_nonneg_right
        ((abs_sub _ _).trans (by linarith [hC (ns (ms k)) ω, hC₀ ω])) (hnn₀ _)
    · filter_upwards [hms] with ω hω
      simpa using (hω.sub_const (F₀ ω)).mul_const (w₀ ω)
  have hE : Tendsto (fun k => ∫ ω, F (ns (ms k)) ω *
      (w (ns (ms k)) ω - w₀ ω) ∂P) atTop (𝓝 0) := by
    have hLC := (hL.comp (hns.comp hmsmono.tendsto_atTop)).const_mul C
    rw [mul_zero] at hLC
    apply squeeze_zero_norm' _ hLC
    · exact Eventually.of_forall fun k => by
        calc ‖∫ ω, F (ns (ms k)) ω * (w (ns (ms k)) ω - w₀ ω) ∂P‖
            ≤ ∫ ω, ‖F (ns (ms k)) ω * (w (ns (ms k)) ω - w₀ ω)‖ ∂P :=
              norm_integral_le_integral_norm _
          _ ≤ ∫ ω, C * |w (ns (ms k)) ω - w₀ ω| ∂P := by
            apply integral_mono_of_nonneg (ae_of_all _ fun _ => norm_nonneg _)
              (((hi _).sub hi₀).abs.const_mul C)
            exact ae_of_all _ fun ω => by
              change ‖F (ns (ms k)) ω * (w (ns (ms k)) ω - w₀ ω)‖ ≤
                C * |w (ns (ms k)) ω - w₀ ω|
              rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_right (hC _ _) (abs_nonneg _)
          _ = C * ∫ ω, |w (ns (ms k)) ω - w₀ ω| ∂P := integral_const_mul _ _
  have hsum := hE.add hD
  have heq (k : ℕ) :
      (∫ ω, F (ns (ms k)) ω * w (ns (ms k)) ω ∂P) - (∫ ω, F₀ ω * w₀ ω ∂P) =
      (∫ ω, F (ns (ms k)) ω * (w (ns (ms k)) ω - w₀ ω) ∂P) +
        ∫ ω, (F (ns (ms k)) ω - F₀ ω) * w₀ ω ∂P := by
    have hiF := hi₀.bdd_mul (hF (ns (ms k))).aestronglyMeasurable
      (ae_of_all _ fun ω => (Real.norm_eq_abs _).symm ▸ hC _ ω)
    rw [← integral_sub (hip _) hip₀,
      ← integral_add ((hip (ns (ms k))).sub hiF |>.congr
        (ae_of_all _ fun ω => (mul_sub _ _ _).symm))
        (hiF.sub hip₀ |>.congr (ae_of_all _ fun ω => (sub_mul _ _ _).symm))]
    apply integral_congr_ae
    exact ae_of_all _ fun ω => by ring
  have hh : Tendsto (fun k => (∫ ω, F (ns (ms k)) ω * w (ns (ms k)) ω ∂P) -
      (∫ ω, F₀ ω * w₀ ω ∂P)) atTop (𝓝 0) := by
    simpa only [heq, add_zero] using hsum
  have hh' := hh.add_const (∫ ω, F₀ ω * w₀ ω ∂P)
  simpa only [sub_add_cancel, zero_add, Function.comp_def] using hh'


/-- Weighted weak convergence with finite masses tending to one. -/
theorem tendsto_integral_mul_weight_finiteMass {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [TopologicalSpace.SeparableSpace E] {P : ℕ → ProbabilityMeasure E}
    {P₀ : ProbabilityMeasure E}
    (hP : Tendsto P atTop (𝓝 P₀)) {w : ℕ → E → ℝ} {w₀ : E → ℝ}
    (hw : ∀ k, Measurable (w k)) (hw₀ : Measurable w₀)
    (hnn : ∀ k x, 0 ≤ w k x) (hnn₀ : ∀ x, 0 ≤ w₀ x)
    (hi : ∀ k, Integrable (w k) (P k : Measure E))
    (hmass : Tendsto (fun k => ∫ x, w k x ∂(P k : Measure E)) atTop (𝓝 1))
    (h10 : ∫ x, w₀ x ∂(P₀ : Measure E) = 1)
    (S : ℕ → Set E) (hS : ∀ k, (P k : Measure E) (S k)ᶜ = 0)
    (G : Set E) (hG : (P₀ : Measure E) Gᶜ = 0)
    (hconv : ∀ x ∈ G, ∀ y : ℕ → E, (∀ k, y k ∈ S k) → Tendsto y atTop (𝓝 x) →
      Tendsto (fun k => w k (y k)) atTop (𝓝 (w₀ x))) (F : BoundedContinuousFunction E ℝ) :
    Tendsto (fun k => ∫ x, F x * w k x ∂(P k : Measure E)) atTop
      (𝓝 (∫ x, F x * w₀ x ∂(P₀ : Measure E))) := by
  obtain ⟨Ω, mΩ, ν, hν, X, Y, hXm, hYm, hXlaw, hYlaw, hXY⟩ :=
    BGW.Probability.exists_probabilitySpace_tendsto_ae_of_tendsto_metric hP
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure ν := hν
  have hSae : ∀ᵐ ω ∂ν, ∀ k, X k ω ∈ S k := by
    apply ae_all_iff.mpr
    intro k
    have hs : ∀ᵐ x ∂(P k : Measure E), x ∈ S k := by
      rw [ae_iff]
      exact hS k
    rw [← hXlaw k] at hs
    exact ae_of_ae_map (hXm k).aemeasurable hs
  have hGae : ∀ᵐ ω ∂ν, Y ω ∈ G := by
    have hg : ∀ᵐ x ∂(P₀ : Measure E), x ∈ G := by
      rw [ae_iff]
      exact hG
    rw [← hYlaw] at hg
    exact ae_of_ae_map hYm.aemeasurable hg
  have hweight : ∀ᵐ ω ∂ν,
      Tendsto (fun k => w k (X k ω)) atTop (𝓝 (w₀ (Y ω))) := by
    filter_upwards [hSae, hGae, hXY] with ω hs hg hc
    exact hconv (Y ω) hg (fun k => X k ω) hs hc
  have htest : ∀ᵐ ω ∂ν,
      Tendsto (fun k => F (X k ω)) atTop (𝓝 (F (Y ω))) := by
    filter_upwards [hXY] with ω hc
    exact (F.continuous.tendsto _).comp hc
  have hint (k : ℕ) : Integrable (fun ω => w k (X k ω)) ν := by
    apply (integrable_map_measure (hw k).aestronglyMeasurable (hXm k).aemeasurable).mp
    rw [hXlaw]
    exact hi k
  have hmass' : Tendsto (fun k => ∫ ω, w k (X k ω) ∂ν) atTop (𝓝 1) := by
    convert hmass using 1
    funext k
    rw [← integral_map (hXm k).aemeasurable (hw k).aestronglyMeasurable, hXlaw]
  have hmass₀ : ∫ ω, w₀ (Y ω) ∂ν = 1 := by
    rw [← integral_map hYm.aemeasurable hw₀.aestronglyMeasurable, hYlaw, h10]
  have ht := tendsto_integral_mul_of_mass_tendsto
    (fun k => (hw k).comp (hXm k)) (hw₀.comp hYm)
    (fun k ω => hnn k (X k ω)) (fun ω => hnn₀ (Y ω)) hint hmass' hmass₀
    (tendstoInMeasure_of_tendsto_ae
      (fun k => ((hw k).comp (hXm k)).aestronglyMeasurable) hweight)
    (fun k => F.continuous.measurable.comp (hXm k)) (F.continuous.measurable.comp hYm)
    (fun k ω => by
      simpa only [Real.norm_eq_abs, Function.comp_apply] using F.norm_coe_le_norm (X k ω))
    (fun ω => by simpa only [Real.norm_eq_abs, Function.comp_apply] using F.norm_coe_le_norm (Y ω))
    (tendstoInMeasure_of_tendsto_ae
      (fun k => (F.continuous.measurable.comp (hXm k)).aestronglyMeasurable) htest)
  have hsource (k : ℕ) : (∫ ω, F (X k ω) * w k (X k ω) ∂ν) =
      ∫ x, F x * w k x ∂(P k : Measure E) := by
    rw [← hXlaw k, integral_map (hXm k).aemeasurable]
    exact (F.continuous.measurable.mul (hw k)).aestronglyMeasurable
  have htarget : (∫ ω, F (Y ω) * w₀ (Y ω) ∂ν) =
      ∫ x, F x * w₀ x ∂(P₀ : Measure E) := by
    rw [← hYlaw, integral_map hYm.aemeasurable]
    exact (F.continuous.measurable.mul hw₀).aestronglyMeasurable
  simpa only [Function.comp_apply, hsource, htarget] using ht


/-- Finite-mass transfer for bounded measurable tests continuous on the full-mass good set. -/
theorem tendsto_integral_mul_weight_test {E : Type*} [MetricSpace E] [MeasurableSpace E]
    [BorelSpace E] [TopologicalSpace.SeparableSpace E] {P : ℕ → ProbabilityMeasure E}
    {P₀ : ProbabilityMeasure E}
    (hP : Tendsto P atTop (𝓝 P₀)) {w : ℕ → E → ℝ} {w₀ : E → ℝ}
    (hw : ∀ k, Measurable (w k)) (hw₀ : Measurable w₀)
    (hnn : ∀ k x, 0 ≤ w k x) (hnn₀ : ∀ x, 0 ≤ w₀ x)
    (hi : ∀ k, Integrable (w k) (P k : Measure E))
    (hmass : Tendsto (fun k => ∫ x, w k x ∂(P k : Measure E)) atTop (𝓝 1))
    (h10 : ∫ x, w₀ x ∂(P₀ : Measure E) = 1)
    (S : ℕ → Set E) (hS : ∀ k, (P k : Measure E) (S k)ᶜ = 0)
    (G : Set E) (hG : (P₀ : Measure E) Gᶜ = 0)
    (hconv : ∀ x ∈ G, ∀ y : ℕ → E, (∀ k, y k ∈ S k) → Tendsto y atTop (𝓝 x) →
      Tendsto (fun k => w k (y k)) atTop (𝓝 (w₀ x))) (F : E → ℝ) (hFm : Measurable F) {C : ℝ}
    (hFb : ∀ x, |F x| ≤ C) (hFc : ∀ x ∈ G, ContinuousAt F x) :
    Tendsto (fun k => ∫ x, F x * w k x ∂(P k : Measure E)) atTop
      (𝓝 (∫ x, F x * w₀ x ∂(P₀ : Measure E))) := by
  obtain ⟨Ω, mΩ, ν, hν, X, Y, hXm, hYm, hXlaw, hYlaw, hXY⟩ :=
    BGW.Probability.exists_probabilitySpace_tendsto_ae_of_tendsto_metric hP
  let : MeasurableSpace Ω := mΩ
  let : IsProbabilityMeasure ν := hν
  have hSae : ∀ᵐ ω ∂ν, ∀ k, X k ω ∈ S k := by
    apply ae_all_iff.mpr
    intro k
    have hs : ∀ᵐ x ∂(P k : Measure E), x ∈ S k := by
      rw [ae_iff]
      exact hS k
    rw [← hXlaw k] at hs
    exact ae_of_ae_map (hXm k).aemeasurable hs
  have hGae : ∀ᵐ ω ∂ν, Y ω ∈ G := by
    have hg : ∀ᵐ x ∂(P₀ : Measure E), x ∈ G := by
      rw [ae_iff]
      exact hG
    rw [← hYlaw] at hg
    exact ae_of_ae_map hYm.aemeasurable hg
  have hweight : ∀ᵐ ω ∂ν,
      Tendsto (fun k => w k (X k ω)) atTop (𝓝 (w₀ (Y ω))) := by
    filter_upwards [hSae, hGae, hXY] with ω hs hg hc
    exact hconv (Y ω) hg (fun k => X k ω) hs hc
  have htest : ∀ᵐ ω ∂ν,
      Tendsto (fun k => F (X k ω)) atTop (𝓝 (F (Y ω))) := by
    filter_upwards [hXY, hGae] with ω hc hg
    exact (hFc (Y ω) hg).tendsto.comp hc
  have hint (k : ℕ) : Integrable (fun ω => w k (X k ω)) ν := by
    apply (integrable_map_measure (hw k).aestronglyMeasurable (hXm k).aemeasurable).mp
    rw [hXlaw]
    exact hi k
  have hmass' : Tendsto (fun k => ∫ ω, w k (X k ω) ∂ν) atTop (𝓝 1) := by
    convert hmass using 1
    funext k
    rw [← integral_map (hXm k).aemeasurable (hw k).aestronglyMeasurable, hXlaw]
  have hmass₀ : ∫ ω, w₀ (Y ω) ∂ν = 1 := by
    rw [← integral_map hYm.aemeasurable hw₀.aestronglyMeasurable, hYlaw, h10]
  have ht := tendsto_integral_mul_of_mass_tendsto
    (fun k => (hw k).comp (hXm k)) (hw₀.comp hYm)
    (fun k ω => hnn k (X k ω)) (fun ω => hnn₀ (Y ω)) hint hmass' hmass₀
    (tendstoInMeasure_of_tendsto_ae
      (fun k => ((hw k).comp (hXm k)).aestronglyMeasurable) hweight)
    (fun k => hFm.comp (hXm k)) (hFm.comp hYm)
    (fun k ω => by
      exact hFb (X k ω))
    (fun ω => by exact hFb (Y ω))
    (tendstoInMeasure_of_tendsto_ae
      (fun k => (hFm.comp (hXm k)).aestronglyMeasurable) htest)
  have hsource (k : ℕ) : (∫ ω, F (X k ω) * w k (X k ω) ∂ν) =
      ∫ x, F x * w k x ∂(P k : Measure E) := by
    rw [← hXlaw k, integral_map (hXm k).aemeasurable]
    exact (hFm.mul (hw k)).aestronglyMeasurable
  have htarget : (∫ ω, F (Y ω) * w₀ (Y ω) ∂ν) =
      ∫ x, F x * w₀ x ∂(P₀ : Measure E) := by
    rw [← hYlaw, integral_map hYm.aemeasurable]
    exact (hFm.mul hw₀).aestronglyMeasurable
  simpa only [Function.comp_apply, hsource, htarget] using ht


/-- Removing a set of vanishing mass changes bounded test integrals by at most
its mass times the test bound. -/
theorem integral_restrict_error {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {S : Set Ω} (hS : MeasurableSet S)
    {F : Ω → ℝ} (hi : Integrable F P) {C : ℝ} (hC : ∀ x, |F x| ≤ C) :
    |(∫ x, F x ∂P) - ∫ x in S, F x ∂P| ≤ C * P.real Sᶜ := by
  have he := integral_add_compl hS hi
  rw [← he, add_sub_cancel_left]
  simpa only [Real.norm_eq_abs, mul_comm] using
    norm_setIntegral_le_of_norm_le_const (f := F) (C := C) (measure_lt_top P Sᶜ)
      (fun x _ => by simpa only [Real.norm_eq_abs] using hC x)

end BGWLeaves.GeneralAFunctional.TreeWeighted
