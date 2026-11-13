/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Measure.Portmanteau
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
public import Mathlib.Topology.GDelta.MetrizableSpace
public import BGW.MetricMeasure.WeakPerturbation

import Mathlib.Topology.Order.LiminfLimsup

/-!
# Generic weak-convergence tools

Extended continuous mapping, countability of positive-mass frontiers, Slutsky's
theorem, and the approximation theorem for probability measures, on varying probability
spaces where relevant.

Reference: P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999,
Theorems 2.7, 3.9 and 3.2. The labels C9–C11 in docstrings refer to the specification
`CLASSICAL_THEORY_INPUTS.md` of this repository.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped Topology BoundedContinuousFunction

namespace BGW.Probability

/-- A map continuous at almost every point is almost everywhere measurable: its set of
continuity points is a `G_δ` (C9, companion 1). -/
theorem aemeasurable_of_ae_continuousAt {S S' : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    [PseudoMetricSpace S'] [MeasurableSpace S'] [BorelSpace S']
    {μ : Measure S} {h : S → S'} (hcont : ∀ᵐ x ∂μ, ContinuousAt h x) :
    AEMeasurable h μ := by
  let C : Set S := {x | ContinuousAt h x}
  have hC : MeasurableSet C := (IsGδ.setOfPred_continuousAt h).measurableSet
  have hcontOn : ContinuousOn h C := fun x hx => hx.continuousWithinAt
  have hCae : ∀ᵐ x ∂μ, x ∈ C := by
    simpa [C] using hcont
  have hrestrict : AEMeasurable h (μ.restrict C) := hcontOn.aemeasurable hC
  rw [Measure.restrict_eq_self_of_ae_mem hCae] at hrestrict
  exact hrestrict

/-- Extended continuous mapping theorem (Billingsley 1999, Theorem 2.7): weak convergence
is preserved by a map that is continuous at almost every point of the limit law (C9). -/
private theorem tendsto_map_of_ae_continuousAt_core {S S' : Type*}
    [PseudoMetricSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    [PseudoMetricSpace S'] [MeasurableSpace S'] [BorelSpace S']
    {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated] [L.NeBot]
    {P : ι → ProbabilityMeasure S} {Q : ProbabilityMeasure S} (hPQ : Tendsto P L (𝓝 Q))
    {h : S → S'} (hmeas : ∀ i, AEMeasurable h (P i))
    (hcont : ∀ᵐ x ∂(Q : Measure S), ContinuousAt h x) :
    Tendsto (fun i => (P i).map h) L (𝓝 (Q.map h)) := by
  apply MeasureTheory.tendsto_of_forall_isClosed_limsup_le
  intro F hF
  let A : Set S := h ⁻¹' F
  let C : Set S := {x | ContinuousAt h x}
  have hclosure : (Q : Measure S) (closure A) ≤ (Q : Measure S) A := by
    have hsubset : closure A ⊆ A ∪ Cᶜ := by
      intro x hx
      by_cases hxC : x ∈ C
      · left
        change h x ∈ F
        change ContinuousAt h x at hxC
        have hmem : h x ∈ closure (h '' A) := _root_.mem_closure_image hxC hx
        have himage : h '' A ⊆ F := by
          rintro y ⟨z, hz, rfl⟩
          exact hz
        have hmemF : h x ∈ closure F := closure_mono himage hmem
        simpa [hF.closure_eq] using hmemF
      · exact Or.inr hxC
    have hnull : (Q : Measure S) Cᶜ = 0 := by
      change (Q : Measure S) {x | ¬ ContinuousAt h x} = 0
      exact ae_iff.mp hcont
    calc
      (Q : Measure S) (closure A) ≤ (Q : Measure S) (A ∪ Cᶜ) := measure_mono hsubset
      _ ≤ (Q : Measure S) A + (Q : Measure S) Cᶜ :=
        measure_union_le (μ := (Q : Measure S)) A Cᶜ
      _ = (Q : Measure S) A := by rw [hnull, add_zero]
  have hmap (i : ι) :
      ((P i).map h) F = (P i) A :=
    ProbabilityMeasure.map_apply (P i) (hmeas i) hF.measurableSet
  have hmapQ : (Q.map h) F = Q A :=
    ProbabilityMeasure.map_apply Q (aemeasurable_of_ae_continuousAt hcont)
      hF.measurableSet
  have hpoint (i : ι) : (P i) A ≤ (P i) (closure A) :=
    ProbabilityMeasure.apply_mono (P i) subset_closure
  have hupper (i : ι) : (P i) (closure A) ≤ 1 := by
    calc
      (P i) (closure A) ≤ (P i) univ :=
        ProbabilityMeasure.apply_mono (P i) (subset_univ _)
      _ = 1 := ProbabilityMeasure.coeFn_univ _
  have haux : ENNReal.ofNNReal (L.limsup fun i => (P i) (closure A)) =
      L.limsup (fun i => ENNReal.ofNNReal ((P i) (closure A))) :=
    Monotone.map_limsup_of_continuousAt (F := L) ENNReal.coe_mono
      (fun i => (P i) (closure A)) (by fun_prop)
      (isBoundedUnder_of ⟨1, hupper⟩)
      (Filter.isCoboundedUnder_le_of_le L fun _ => bot_le)
  have hport : L.limsup (fun i => ENNReal.ofNNReal ((P i) (closure A))) ≤
      ENNReal.ofNNReal (Q (closure A)) := by
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using
      (ProbabilityMeasure.limsup_measure_closed_le_of_tendsto hPQ isClosed_closure)
  have hclosurePM : Q (closure A) ≤ Q A := by
    apply (ENNReal.coe_le_coe).mp
    simpa only [ProbabilityMeasure.ennreal_coeFn_eq_coeFn_toMeasure] using hclosure
  have hlimsupA : L.limsup (fun i => (P i) A) ≤ Q A := by
    apply (ENNReal.coe_le_coe).mp
    calc
      ENNReal.ofNNReal (L.limsup fun i => (P i) A) ≤
          ENNReal.ofNNReal (L.limsup fun i => (P i) (closure A)) :=
        ENNReal.coe_mono <| Filter.limsup_le_limsup
          (Filter.Eventually.of_forall hpoint)
          (Filter.isCoboundedUnder_le_of_le L fun _ => bot_le)
          (isBoundedUnder_of ⟨1, hupper⟩)
      _ = L.limsup (fun i => ENNReal.ofNNReal ((P i) (closure A))) := haux
      _ ≤ ENNReal.ofNNReal (Q (closure A)) := hport
      _ ≤ ENNReal.ofNNReal (Q A) := ENNReal.coe_mono hclosurePM
  have hupperMap (i : ι) : ((P i).map h) F ≤ 1 := by
    calc
      ((P i).map h) F ≤ ((P i).map h) univ :=
        ProbabilityMeasure.apply_mono _ (subset_univ _)
      _ = 1 := ProbabilityMeasure.coeFn_univ _
  have hupperA (i : ι) : (P i) A ≤ 1 := by
    exact (hpoint i).trans (hupper i)
  calc
    L.limsup (fun i => ((P i).map h) F) ≤ L.limsup (fun i => (P i) A) :=
      Filter.limsup_le_limsup (Filter.Eventually.of_forall fun i => hmap i ▸ le_rfl)
        (Filter.isCoboundedUnder_le_of_le L fun _ => bot_le)
        (isBoundedUnder_of ⟨1, hupperA⟩)
    _ ≤ Q A := hlimsupA
    _ = (Q.map h) F := hmapQ.symm

/-- Extended continuous mapping theorem (Billingsley 1999, Theorem 2.7): weak convergence
is preserved by a map that is continuous at almost every point of the limit law (C9). -/
theorem tendsto_map_of_ae_continuousAt {S S' : Type*}
    [PseudoMetricSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    [PseudoMetricSpace S'] [MeasurableSpace S'] [BorelSpace S']
    {ι : Type*} {L : Filter ι} [L.IsCountablyGenerated]
    {P : ι → ProbabilityMeasure S} {Q : ProbabilityMeasure S} (hPQ : Tendsto P L (𝓝 Q))
    {h : S → S'} (hmeas : ∀ i, AEMeasurable h (P i))
    (hcont : ∀ᵐ x ∂(Q : Measure S), ContinuousAt h x) :
    Tendsto (fun i => (P i).map h) L (𝓝 (Q.map h)) := by
  rcases L.eq_or_neBot with rfl | hL
  · simp
  · exact @tendsto_map_of_ae_continuousAt_core S S' _ _ _ _ _ _ ι L _ hL P Q
      hPQ h hmeas hcont

/-- A finite measure gives positive mass to at most countably many sets of a family with
pairwise disjoint frontiers; used to choose cut-off levels with null boundaries
(C9, companion 2; N11). -/
theorem countable_setOf_measure_frontier_ne_zero {S ι : Type*}
    [TopologicalSpace S] [MeasurableSpace S] [OpensMeasurableSpace S]
    (μ : Measure S) [IsFiniteMeasure μ] {A : ι → Set S}
    (hdisj : Pairwise (Function.onFun Disjoint fun i => frontier (A i))) :
    {i | μ (frontier (A i)) ≠ 0}.Countable := by
  have hmeas : ∀ i, MeasurableSet (frontier (A i)) :=
    fun i => isClosed_frontier.measurableSet
  have hcount := Measure.countable_meas_pos_of_disjoint_iUnion (μ := μ) hmeas hdisj
  apply hcount.mono
  intro i hi
  have hnonneg : 0 ≤ μ (frontier (A i)) := bot_le
  exact lt_of_le_of_ne hnonneg (Ne.symm hi)

/-- Slutsky on varying probability spaces (Billingsley 1999, Theorem 3.9): if `X n`
converges in law and `Y n` converges in probability to a constant `c`, then the pair
converges in law to the product of the limit law with the Dirac mass at `c` (C10(2)). -/
theorem tendsto_map_prodMk_of_tendsto_of_error {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {S S' : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SecondCountableTopology S]
    [PseudoMetricSpace S'] [MeasurableSpace S'] [BorelSpace S'] [SecondCountableTopology S']
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) {X : (n : ℕ) → Ω n → S}
    {Y : (n : ℕ) → Ω n → S'} (hX : ∀ n, Measurable (X n)) (hY : ∀ n, Measurable (Y n))
    {P : ProbabilityMeasure S} {c : S'}
    (hlim : Tendsto (fun n => (μ n).map (X n)) atTop (𝓝 P))
    (herr : ∀ ε > 0, Tendsto (fun n =>
      (μ n : Measure (Ω n)).real {ω | ε < dist (Y n ω) c}) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).map (fun ω => (X n ω, Y n ω))) atTop
      (𝓝 (P.map (fun x => (x, c)))) := by
  let F : (n : ℕ) → Ω n → S × S' := fun n ω => (X n ω, Y n ω)
  let G : (n : ℕ) → Ω n → S × S' := fun n ω => (X n ω, c)
  have hF : ∀ n, Measurable (F n) := fun n => (hX n).prodMk (hY n)
  have hG : ∀ n, Measurable (G n) := fun n => (hX n).prodMk measurable_const
  have hlimG : Tendsto (fun n => (μ n).map (G n)) atTop
      (𝓝 (P.map fun x => (x, c))) := by
    have hcont : Continuous (fun x : S => (x, c)) := continuous_id.prodMk continuous_const
    have hmap (n : ℕ) : (μ n).map (G n) = ((μ n).map (X n)).map (fun x => (x, c)) := by
      apply Subtype.ext
      change (μ n : Measure (Ω n)).map (fun ω => (X n ω, c)) =
        ((μ n : Measure (Ω n)).map (X n)).map (fun x => (x, c))
      exact (Measure.map_map hcont.measurable (hX n)).symm
    simpa only [hmap] using ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => (μ n).map (X n)) P hlim hcont
  have herrFG : ∀ ε > 0, Tendsto (fun n =>
      (μ n : Measure (Ω n)).real {ω | ε < dist (F n ω) (G n ω)}) atTop (𝓝 0) := by
    intro ε hε
    convert herr ε hε using 1
    ext ω
    simp [F, G, dist_prod_same_left]
  exact BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability μ hF hG herrFG hlimG

/-- Approximation theorem (Billingsley 1999, Theorem 3.2), on varying probability spaces:
if `X u n ⇒ Z u` as `n → ∞`, `Z u ⇒ ν` as `u → ∞`, and `X u n` approximates `Y n`
uniformly in probability as `u → ∞`, then `Y n ⇒ ν` (C11(1)). -/
theorem tendsto_of_tendsto_approx {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    {S : Type*} [PseudoMetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [SecondCountableTopology S]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) {Y : (n : ℕ) → Ω n → S}
    {X : ℕ → (n : ℕ) → Ω n → S} (hY : ∀ n, Measurable (Y n))
    (hX : ∀ u n, Measurable (X u n)) {Z : ℕ → ProbabilityMeasure S}
    {ν : ProbabilityMeasure S}
    (hXZ : ∀ u, Tendsto (fun n => (μ n).map (X u n)) atTop (𝓝 (Z u)))
    (hZ : Tendsto Z atTop (𝓝 ν))
    (herr : ∀ ε > 0, Tendsto (fun u => limsup (fun n =>
      (μ n : Measure (Ω n)).real {ω | ε ≤ dist (X u n ω) (Y n ω)}) atTop) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).map (Y n)) atTop (𝓝 ν) := by
  apply tendsto_iff_forall_lipschitz_integral_tendsto.mpr
  intro φ hbounded hlipschitz
  obtain ⟨M, hM⟩ := hbounded
  obtain ⟨L, hL⟩ := hlipschitz
  let Φ : S →ᵇ ℝ :=
    { toFun := φ, continuous_toFun := hL.continuous, map_bounded' := ⟨M, hM⟩ }
  let B := max M 0
  let iy : ℕ → ℝ := fun n => ∫ t, φ t ∂((μ n).map (Y n))
  let ix : ℕ → ℕ → ℝ := fun u n => ∫ t, φ t ∂((μ n).map (X u n))
  let iz : ℕ → ℝ := fun u => ∫ t, φ t ∂(Z u)
  let izν : ℝ := ∫ t, φ t ∂ν
  have hYint (n : ℕ) : Integrable (fun ω => φ (Y n ω)) (μ n : Measure (Ω n)) :=
    (Φ.integrable ((μ n).map (Y n))).comp_measurable (hY n)
  have hXint (u n : ℕ) : Integrable (fun ω => φ (X u n ω)) (μ n : Measure (Ω n)) :=
    (Φ.integrable ((μ n).map (X u n))).comp_measurable (hX u n)
  have hbound (u n : ℕ) {ε : ℝ} (hε : 0 < ε) :
      |iy n - ix u n| ≤ (L : ℝ) * ε + B *
        (μ n : Measure (Ω n)).real {ω | ε ≤ dist (X u n ω) (Y n ω)} := by
    let A := {ω | ε ≤ dist (X u n ω) (Y n ω)}
    have hA : MeasurableSet A :=
      measurableSet_le measurable_const ((hX u n).dist (hY n))
    have hI : Integrable (fun ω => (L : ℝ) * ε + A.indicator (fun _ => B) ω)
        (μ n : Measure (Ω n)) :=
      integrable_const _ |>.add ((integrable_const B).indicator hA)
    have hpt (ω : Ω n) : ‖φ (Y n ω) - φ (X u n ω)‖ ≤
        (L : ℝ) * ε + A.indicator (fun _ => B) ω := by
      by_cases hω : ω ∈ A
      · rw [Set.indicator_of_mem hω]
        have hb : dist (φ (Y n ω)) (φ (X u n ω)) ≤ B := by
          calc
            dist (φ (Y n ω)) (φ (X u n ω)) = dist (φ (X u n ω)) (φ (Y n ω)) :=
              dist_comm _ _
            _ ≤ M := hM _ _
            _ ≤ max M 0 := le_max_left _ _
        simpa only [dist_eq_norm] using
          hb.trans (le_add_of_nonneg_left (mul_nonneg L.coe_nonneg hε.le))
      · rw [Set.indicator_of_notMem hω, add_zero]
        have hd : dist (X u n ω) (Y n ω) < ε := lt_of_not_ge hω
        have hdist : dist (φ (Y n ω)) (φ (X u n ω)) ≤ (L : ℝ) * ε := by
          rw [dist_comm]
          exact (hL.dist_le_mul _ _).trans
            (mul_le_mul_of_nonneg_left hd.le L.coe_nonneg)
        simpa only [dist_eq_norm] using hdist
    change |(∫ t, φ t ∂((μ n).map (Y n))) -
      ∫ t, φ t ∂((μ n).map (X u n))| ≤ _
    rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
      integral_map (hY n).aemeasurable hL.continuous.aestronglyMeasurable,
      integral_map (hX u n).aemeasurable hL.continuous.aestronglyMeasurable,
      ← integral_sub (hYint n) (hXint u n), ← Real.norm_eq_abs]
    calc
      ‖∫ ω, φ (Y n ω) - φ (X u n ω) ∂(μ n : Measure (Ω n))‖ ≤
          ∫ ω, ‖φ (Y n ω) - φ (X u n ω)‖ ∂(μ n : Measure (Ω n)) :=
        norm_integral_le_integral_norm _
      _ ≤ ∫ ω, (L : ℝ) * ε + A.indicator (fun _ => B) ω ∂(μ n : Measure (Ω n)) :=
        integral_mono ((hYint n).sub (hXint u n)).norm hI hpt
      _ = (L : ℝ) * ε + B *
          (μ n : Measure (Ω n)).real {ω | ε ≤ dist (X u n ω) (Y n ω)} := by
        rw [integral_add (integrable_const _) ((integrable_const B).indicator hA),
          integral_indicator_const B hA]
        simp [smul_eq_mul, mul_comm, A]
  have hZint : Tendsto iz atTop (𝓝 izν) := by
    have h := tendsto_iff_forall_lipschitz_integral_tendsto.mp hZ φ ⟨M, hM⟩ ⟨L, hL⟩
    simpa [iz, izν] using h
  have hεevent (ε η : ℝ) (hε : 0 < ε) (hη : 0 < η) :
      ∀ᶠ u in atTop, limsup (fun n =>
        (μ n : Measure (Ω n)).real {ω | ε ≤ dist (X u n ω) (Y n ω)}) atTop < η :=
    (herr ε hε).eventually (Iio_mem_nhds hη)
  have hYtendsto : Tendsto iy atTop (𝓝 izν) := by
    rw [Metric.tendsto_nhds]
    intro δ hδ
    let ε := δ / (4 * ((L : ℝ) + 1))
    have hε : 0 < ε := by dsimp [ε]; positivity
    have hsmall : (L : ℝ) * ε < δ / 4 := by
      dsimp [ε]
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 4 * ((L : ℝ) + 1))]
      have hLpos : 0 ≤ (L : ℝ) := L.coe_nonneg
      nlinarith [mul_pos hδ (by norm_num : (0 : ℝ) < 1)]
    let α := δ / (8 * (B + 1))
    have hα : 0 < α := by dsimp [α]; positivity
    have hZnear : ∀ᶠ u in atTop, |iz u - izν| < δ / 4 := by
      have h := hZint.eventually
        (Metric.ball_mem_nhds izν (show 0 < δ / 4 by positivity))
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using h
    have herrnear : ∀ᶠ u in atTop, limsup (fun n =>
        (μ n : Measure (Ω n)).real {ω | ε ≤ dist (X u n ω) (Y n ω)}) atTop < α := by
      simpa [α] using hεevent ε α hε hα
    obtain ⟨u, huZ, huerr⟩ := (hZnear.and herrnear).exists
    let p : ℕ → ℝ := fun n =>
      (μ n : Measure (Ω n)).real {ω | ε ≤ dist (X u n ω) (Y n ω)}
    have hpupper : ∀ n, p n ≤ 1 := by
      intro n
      dsimp [p]
      rw [ProbabilityMeasure.measureReal_eq_coe_coeFn]
      exact_mod_cast ProbabilityMeasure.apply_mono (μ n) (subset_univ _)
    have hp : ∀ᶠ n in atTop, p n < α :=
      eventually_lt_of_limsup_lt huerr (isBoundedUnder_of ⟨1, hpupper⟩)
    have hXZint : Tendsto (ix u) atTop (𝓝 (iz u)) := by
      have h := tendsto_iff_forall_lipschitz_integral_tendsto.mp
        (hXZ u) φ ⟨M, hM⟩ ⟨L, hL⟩
      simpa [ix, iz] using h
    have hXnear : ∀ᶠ n in atTop, |ix u n - iz u| < δ / 4 := by
      have h := hXZint.eventually
        (Metric.ball_mem_nhds (iz u) (show 0 < δ / 4 by positivity))
      simpa [Metric.mem_ball, Real.dist_eq, abs_sub_comm] using h
    have htail : ∀ᶠ n in atTop, B * p n < δ / 4 := by
      filter_upwards [hp] with n hn
      dsimp [α] at hn ⊢
      have hB : 0 ≤ B := le_max_right _ _
      have hprod : B * p n ≤ B * (δ / (8 * (B + 1))) := by gcongr
      have hratio : B * (δ / (8 * (B + 1))) ≤ δ / 8 := by
        rw [← mul_div_assoc, div_le_iff₀ (by positivity : 0 < (8 : ℝ) * (B + 1))]
        nlinarith [mul_nonneg hδ.le hB]
      calc
        B * p n ≤ B * (δ / (8 * (B + 1))) := hprod
        _ ≤ δ / 8 := hratio
        _ < δ / 4 := by linarith
    filter_upwards [hXnear, htail] with n hXn ht
    have htri : |iy n - izν| ≤ |iy n - ix u n| +
        |ix u n - iz u| + |iz u - izν| := by
      have h₁ := abs_sub_le (iy n) (ix u n) izν
      have h₂ := abs_sub_le (ix u n) (iz u) izν
      linarith
    calc
      |iy n - izν| ≤ |iy n - ix u n| + |ix u n - iz u| + |iz u - izν| := htri
      _ < δ := by
        have hb := hbound u n hε
        have he : (L : ℝ) * ε + B * p n < δ / 2 := by linarith [hsmall, ht]
        linarith [huZ]
  simpa [iy, izν] using hYtendsto

end BGW.Probability

