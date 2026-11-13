/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.ReverseBridge
public import BGW.StableTrees.BridgeProjective
public import BGW.StableTrees.StableProcessReversal
import BGW.Skorokhod.Prefix

/-!
# The closed stable bridge

This module characterizes the closed stable bridge by its strict prefix laws and terminal
pinning, proves invariance under time reversal, and establishes absence of discontinuities at
fixed times (P. Fitzsimmons, J. Pitman and M. Yor, Markovian bridges: construction, Palm
interpretation, and splicing, Seminar on Stochastic Processes 1992, Birkhäuser, 1993; L. Chaumont,
Excursion normalisée, méandre et pont pour les processus de Lévy stables, Bull. Sci. Math. 121
(1997), 377–403).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ### Bounded-prefix expectation formulas -/

/-- **Prefix expectation.** For `0 < a < 1` and bounded Borel `F` on `D a ℝ`:
`E_bridge[F(f|[0,a])] = E_{P_a}[w_a · F]`. The integrand on the right lives on `D a ℝ` (it is not
another restriction from `D 1 ℝ`). -/
theorem integral_restrict_stableBridgeLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (ha1 : a < 1) {F : D a ℝ → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f, F (restrict (E := ℝ) ha1.le f) ∂(stableBridgeLaw θ : Measure (D 1 ℝ)) =
      ∫ g, bridgePrefixWeight θ a ha.le g * F g ∂(stableProcessLaw θ a : Measure (D a ℝ)) := by
  have _hFb := hFb
  calc
    ∫ f, F (restrict (E := ℝ) ha1.le f) ∂(stableBridgeLaw θ : Measure (D 1 ℝ)) =
        ∫ g, F g ∂(stableBridgeLaw θ : Measure (D 1 ℝ)).map (restrict ha1.le) :=
      (integral_map (measurable_restrict _).aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ g, F g ∂bridgePrefixLaw θ a ha.le
        (stableProcessLaw θ a : Measure (D a ℝ)) := by
      rw [map_restrict_stableBridgeLaw hθ ha ha1]
    _ = ∫ g, bridgePrefixWeight θ a ha.le g * F g
        ∂(stableProcessLaw θ a : Measure (D a ℝ)) := by
      rw [bridgePrefixLaw, integral_withDensity_eq_integral_toReal_smul
        (measurable_bridgePrefixWeight hθ ha.le).ennreal_ofReal
        (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
      apply integral_congr_ae
      filter_upwards [] with g
      rw [ENNReal.toReal_ofReal (bridgePrefixWeight_nonneg hθ ha.le ha1 g), smul_eq_mul]

/-- Prefix probabilities: for measurable `B ⊆ D a ℝ`,
`P_bridge(f|[0,a] ∈ B) = ∫_B w_a dP_a`. -/
theorem measure_restrict_preimage_stableBridgeLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (ha1 : a < 1) {B : Set (D a ℝ)} (hB : MeasurableSet B) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)) (restrict (E := ℝ) ha1.le ⁻¹' B) =
      ∫⁻ g in B, ENNReal.ofReal (bridgePrefixWeight θ a ha.le g)
        ∂(stableProcessLaw θ a : Measure (D a ℝ)) := by
  rw [← Measure.map_apply (measurable_restrict _) hB,
    map_restrict_stableBridgeLaw hθ ha ha1, bridgePrefixLaw, withDensity_apply _ hB]

/-- Strict prefixes of the bridge are absolutely continuous with respect to the stable law. -/
theorem map_restrict_stableBridgeLaw_absolutelyContinuous {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) (ha1 : a < 1) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map (restrict (E := ℝ) ha1.le) ≪
      (stableProcessLaw θ a : Measure (D a ℝ)) := by
  rw [map_restrict_stableBridgeLaw hθ ha ha1]
  exact bridgePrefixLaw_absolutelyContinuous θ a ha.le _

/-- The prefix weight integrates to one against `P_a` (mass one of the tilted prefix law). -/
theorem integral_bridgePrefixWeight_stableProcessLaw {θ a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (ha : 0 < a) (ha1 : a < 1) :
    ∫ g, bridgePrefixWeight θ a ha.le g ∂(stableProcessLaw θ a : Measure (D a ℝ)) = 1 := by
  have h := integral_restrict_stableBridgeLaw hθ ha ha1 (F := fun _ => 1) measurable_const
    ⟨1, fun _ => by simp⟩
  simpa using h.symm

private theorem continuousAt_top_of_leftLim_eq {f : D 1 ℝ}
    (h : f ⟨1, zero_le_one, le_rfl⟩ = Function.leftLim f ⟨1, zero_le_one, le_rfl⟩) :
    ContinuousAt f ⟨1, zero_le_one, le_rfl⟩ := by
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, (isCadlag f).isRightContinuous _⟩
  rw [ContinuousWithinAt, h]
  exact (isCadlag f).tendsto_nhdsLT_leftLim _

private theorem tendsto_bridgeHorizon : Tendsto bridgeHorizon atTop (𝓝 1) := by
  change Tendsto (fun n : ℕ => 1 - (1 / 2 : ℝ) ^ (n + 1)) atTop (𝓝 1)
  have hpow : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using (tendsto_const_nhds (x := (1 : ℝ))).sub
    (hpow.comp (tendsto_add_atTop_nat 1))

/-- **Uniqueness, minimal endpoint form.** A law on `D 1 ℝ` with the prescribed prefix laws on
every `[0, a]`, `a < 1`, and which a.s. has no jump at time `1` (`f 1 = f 1-`), is the stable
bridge. (The prefix laws force `f 1- = 0` a.s.) -/
theorem stableBridgeLaw_unique {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {Q : ProbabilityMeasure (D 1 ℝ)}
    (hprefix : ∀ a : ℝ, ∀ ha : 0 < a, ∀ ha1 : a < 1,
      (Q : Measure (D 1 ℝ)).map (restrict (E := ℝ) ha1.le) =
        bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ)))
    (hend : ∀ᵐ f : D 1 ℝ ∂(Q : Measure (D 1 ℝ)),
      f ⟨1, zero_le_one, le_rfl⟩ = Function.leftLim f ⟨1, zero_le_one, le_rfl⟩) :
    Q = stableBridgeLaw θ := by
  apply ext_of_restrict (P := Q) (Q := stableBridgeLaw θ) zero_lt_one
    (fun k => bridgeHorizon_lt_one k) tendsto_bridgeHorizon
  · filter_upwards [hend] with f hf
    exact continuousAt_top_of_leftLim_eq hf
  · filter_upwards [stableBridgeLaw_endpoints hθ] with f hf
    exact continuousAt_top_of_leftLim_eq (hf.2.1.trans hf.2.2.symm)
  · intro k
    apply ProbabilityMeasure.toMeasure_injective
    change (Q : Measure (D 1 ℝ)).map (restrict (bridgeHorizon_lt_one k).le) =
      (stableBridgeLaw θ : Measure (D 1 ℝ)).map (restrict (bridgeHorizon_lt_one k).le)
    rw [hprefix _ (bridgeHorizon_pos k) (bridgeHorizon_lt_one k),
      map_restrict_stableBridgeLaw hθ (bridgeHorizon_pos k) (bridgeHorizon_lt_one k)]

/-- **Uniqueness, pinned form** (the endpoint conditions of `stableBridgeLaw_endpoints`): prefix
laws plus
`f 1 = 0 ∧ f 1- = 0` almost surely. -/
theorem stableBridgeLaw_unique_of_endpoints {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {Q : ProbabilityMeasure (D 1 ℝ)}
    (hprefix : ∀ a : ℝ, ∀ ha : 0 < a, ∀ ha1 : a < 1,
      (Q : Measure (D 1 ℝ)).map (restrict (E := ℝ) ha1.le) =
        bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ)))
    (hend : ∀ᵐ f : D 1 ℝ ∂(Q : Measure (D 1 ℝ)),
      f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧ Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ = 0) :
    Q = stableBridgeLaw θ := by
  apply stableBridgeLaw_unique hθ hprefix
  filter_upwards [hend] with f hf
  exact hf.1.trans hf.2.symm

/-- **Characterization.** `Q` is the stable bridge law iff it has the tilted prefix laws and is a.s.
pinned at time `1`. -/
theorem eq_stableBridgeLaw_iff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {Q : ProbabilityMeasure (D 1 ℝ)} :
    Q = stableBridgeLaw θ ↔
      ((∀ a : ℝ, ∀ ha : 0 < a, ∀ ha1 : a < 1,
        (Q : Measure (D 1 ℝ)).map (restrict (E := ℝ) ha1.le) =
          bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ))) ∧
      ∀ᵐ f : D 1 ℝ ∂(Q : Measure (D 1 ℝ)),
        f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧ Function.leftLim f ⟨1, zero_le_one, le_rfl⟩ = 0) := by
  constructor
  · rintro rfl
    refine ⟨fun a ha ha1 => map_restrict_stableBridgeLaw hθ ha ha1, ?_⟩
    filter_upwards [stableBridgeLaw_endpoints hθ] with f hf
    exact ⟨hf.2.1, hf.2.2⟩
  · rintro ⟨hprefix, hend⟩
    exact stableBridgeLaw_unique_of_endpoints hθ hprefix hend

private def closedTop : Set.Icc (0 : ℝ) 1 := ⟨1, zero_le_one, le_rfl⟩

private noncomputable def terminalOneFun (f : D 1 ℝ) (s : Set.Icc (0 : ℝ) 1) : ℝ :=
  if s = closedTop then 1 else f s

private theorem isCadlag_terminalOneFun (f : D 1 ℝ) : IsCadlag (terminalOneFun f) := by
  constructor
  · intro s
    by_cases hs : s = closedTop
    · subst s
      have htop : IsTop closedTop := fun t => t.2.2
      have hi : Set.Ioi closedTop = ∅ := by
        ext t
        simp only [mem_Ioi, mem_empty_iff_false, iff_false]
        exact not_lt_of_ge (htop t)
      rw [ContinuousWithinAt, hi, nhdsWithin_empty]
      exact tendsto_bot
    · apply ContinuousWithinAt.congr_of_eventuallyEq ((isCadlag f).isRightContinuous s) _
        (ite_eq_right hs)
      have hst : s < closedTop := lt_of_le_of_ne s.2.2 hs
      filter_upwards [mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hst)] with t ht
      change (if t = closedTop then 1 else f t) = f t
      exact ite_eq_right (fun h => ht.ne (congrArg Subtype.val h))
  · intro s
    refine ⟨Function.leftLim f s, ?_⟩
    have heq : terminalOneFun f =ᶠ[𝓝[<] s] f := by
      filter_upwards [self_mem_nhdsWithin] with t ht
      change (if t = closedTop then 1 else f t) = f t
      exact ite_eq_right (fun h => (ht.trans_le s.2.2).ne (congrArg Subtype.val h))
    exact (tendsto_congr' heq).2 ((isCadlag f).tendsto_nhdsLT_leftLim s)

private noncomputable def terminalOne (f : D 1 ℝ) : D 1 ℝ :=
  ⟨terminalOneFun f, isCadlag_terminalOneFun f⟩

private theorem terminalOne_apply (f : D 1 ℝ) (s : Set.Icc (0 : ℝ) 1) :
    terminalOne f s = if s = closedTop then 1 else f s := rfl

private theorem measurable_terminalOne : Measurable terminalOne := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap terminalOne (inferInstance : MeasurableSpace (D 1 ℝ)) ≤
    (inferInstance : MeasurableSpace (D 1 ℝ))
  conv_lhs =>
    rw [measurableSpace_eq_iSup_comap_eval (T := 1) (E := ℝ) (S := Set.univ)
      dense_univ zero_le_one (by simp)]
  simp only [MeasurableSpace.comap_iSup, iSup_le_iff, MeasurableSpace.comap_comp,
    Function.comp_def]
  intro u _hu
  rw [show (fun f : D 1 ℝ => terminalOne f u) = fun f => if u = closedTop then 1 else f u by
    funext f; exact terminalOne_apply f u]
  by_cases hu : u = closedTop
  · simp only [hu, ite_true]
    exact measurable_const.comap_le
  · simp only [hu, ite_false]
    exact (measurable_eval u).comap_le

private theorem restrict_terminalOne {a : ℝ} (ha1 : a < 1) :
    (restrict (E := ℝ) ha1.le) ∘ terminalOne = restrict (E := ℝ) ha1.le := by
  funext f
  ext t
  change terminalOne f ⟨t, t.2.1, t.2.2.trans ha1.le⟩ = f ⟨t, t.2.1, t.2.2.trans ha1.le⟩
  rw [terminalOne_apply]
  exact ite_eq_right (show (⟨t, t.2.1, t.2.2.trans ha1.le⟩ : Set.Icc (0 : ℝ) 1) ≠ closedTop by
    intro h
    have := congrArg Subtype.val h
    exact (lt_of_le_of_lt t.2.2 ha1).ne this)

/-- Prefix laws alone do not determine the law: the value at time `1` is free. This is the
necessity of the endpoint hypothesis (a concrete second law with the same prefixes: the bridge
with its terminal value overwritten by `1`). -/
theorem exists_ne_stableBridgeLaw_same_prefixes {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ Q : ProbabilityMeasure (D 1 ℝ), Q ≠ stableBridgeLaw θ ∧
      ∀ a : ℝ, ∀ ha : 0 < a, ∀ ha1 : a < 1,
        (Q : Measure (D 1 ℝ)).map (restrict (E := ℝ) ha1.le) =
          bridgePrefixLaw θ a ha.le (stableProcessLaw θ a : Measure (D a ℝ)) := by
  let Q : ProbabilityMeasure (D 1 ℝ) := (stableBridgeLaw θ).map terminalOne
  refine ⟨Q, ?_, ?_⟩
  · intro hQ
    have hend : ∀ᵐ f : D 1 ℝ ∂(Q : Measure (D 1 ℝ)), f closedTop = 0 := by
      rw [hQ]
      filter_upwards [stableBridgeLaw_endpoints hθ] with f hf
      exact hf.2.1
    have hs : MeasurableSet {f : D 1 ℝ | f closedTop = 0} :=
      (measurable_eval _) (measurableSet_singleton 0)
    change ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)).map terminalOne,
      f closedTop = 0 at hend
    rw [ae_map_iff measurable_terminalOne.aemeasurable hs] at hend
    have hone (f : D 1 ℝ) : terminalOne f closedTop = 1 := by
      rw [terminalOne_apply, ite_eq_left rfl]
    change {f : D 1 ℝ | terminalOne f closedTop = 0} ∈
      ae (stableBridgeLaw θ : Measure (D 1 ℝ)) at hend
    have hempty : {f : D 1 ℝ | terminalOne f closedTop = 0} = ∅ := by
      ext f
      simp [hone f]
    rw [hempty] at hend
    simp at hend
  · intro a ha ha1
    change ((stableBridgeLaw θ : Measure (D 1 ℝ)).map terminalOne).map
      (restrict ha1.le) = _
    rw [Measure.map_map (measurable_restrict _) measurable_terminalOne,
      restrict_terminalOne ha1, map_restrict_stableBridgeLaw hθ ha ha1]

private theorem continuousAt_of_restrict {f : D 1 ℝ} {a t : ℝ} (ht : 0 ≤ t)
    (hta : t < a) (ha1 : a < 1)
    (h : ContinuousAt (restrict ha1.le f) ⟨t, ht, hta.le⟩) :
    ContinuousAt f ⟨t, ht, hta.le.trans ha1.le⟩ := by
  let t0 : Set.Icc (0 : ℝ) 1 := ⟨t, ht, hta.le.trans ha1.le⟩
  change ContinuousAt f t0
  let t' : Set.Icc (0 : ℝ) a := ⟨t, ht, hta.le⟩
  rw [Metric.continuousAt_iff] at h ⊢
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := h ε hε
  refine ⟨min δ (a - t), lt_min hδ (sub_pos.mpr hta), ?_⟩
  intro u hu
  have huδ : dist u t0 < δ := hu.trans_le (min_le_left _ _)
  have huAdist : dist u t0 < a - t := hu.trans_le (min_le_right _ _)
  have huA : (u : ℝ) < a := by
    have hu_abs : |(u : ℝ) - t| < a - t := by
      simpa only [t0, Subtype.dist_eq, Real.dist_eq] using huAdist
    linarith [((abs_lt.mp hu_abs).2 : (u : ℝ) - t < a - t)]
  let u' : Set.Icc (0 : ℝ) a := ⟨u, u.2.1, huA.le⟩
  have hu' : dist u' t' < δ := by
    simpa [u', t', t0, Subtype.dist_eq, Real.dist_eq] using huδ
  exact hδf hu'

/-- **No fixed discontinuities.** At every fixed time `t ∈ [0, 1]` (including `0` and `1`) the
bridge is almost surely continuous. -/
theorem stableBridgeLaw_ae_continuousAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : Set.Icc (0 : ℝ) 1) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), ContinuousAt f t := by
  by_cases ht : (t : ℝ) = 1
  · have ht' : t = ⟨1, zero_le_one, le_rfl⟩ := Subtype.ext ht
    subst t
    filter_upwards [stableBridgeLaw_endpoints hθ] with f hf
    exact continuousAt_top_of_leftLim_eq (hf.2.1.trans hf.2.2.symm)
  · have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 ht
    let a : ℝ := (t + 1) / 2
    have hta : (t : ℝ) < a := by dsimp [a]; linarith
    have ha : 0 < a := by dsimp [a]; linarith [t.2.1]
    have ha1 : a < 1 := by dsimp [a]; linarith
    let ta : Set.Icc (0 : ℝ) a := ⟨t, t.2.1, hta.le⟩
    have hstable := ae_continuousAt_stableProcessLaw hθ ha ta
    have hprefix := (map_restrict_stableBridgeLaw_absolutelyContinuous hθ ha ha1).ae_le hstable
    have hpre := ae_of_ae_map (measurable_restrict ha1.le).aemeasurable hprefix
    filter_upwards [hpre] with f hf
    exact continuousAt_of_restrict t.2.1 hta ha1 hf

/-- Fixed-time left limit equals the value, almost surely (equivalent form, quantified over
all fixed times at once is not claimed). -/
theorem stableBridgeLaw_ae_leftLim_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : Set.Icc (0 : ℝ) 1) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), Function.leftLim f t = f t := by
  filter_upwards [stableBridgeLaw_ae_continuousAt hθ t] with f hf
  exact hf.continuousWithinAt.leftLim_eq

private noncomputable def shiftedEval (b : ℝ) (s : Set.Icc (0 : ℝ) 1) (f : D b ℝ) : ℝ :=
  if h : 1 - (s : ℝ) ≤ b then f ⟨b - (1 - s), by linarith [h], by linarith [s.2.2]⟩ else 0

private theorem measurable_shiftedEval (b : ℝ) (s : Set.Icc (0 : ℝ) 1) :
    Measurable (shiftedEval b s) := by
  classical
  unfold shiftedEval
  split_ifs
  · exact measurable_eval _
  · exact measurable_const

private noncomputable def evalSeq (s : Finset (Set.Icc (0 : ℝ) 1)) (n : ℕ)
    (f : D 1 ℝ) : s → ℝ := fun i =>
  shiftedEval (bridgeHorizon n) i (restrict (bridgeHorizon_lt_one n).le f)

private noncomputable def reversedEvalSeq (s : Finset (Set.Icc (0 : ℝ) 1)) (n : ℕ)
    (f : D 1 ℝ) : s → ℝ := fun i =>
  shiftedEval (bridgeHorizon n) i
    (reverseIncrements (bridgeHorizon_pos n).le (restrict (bridgeHorizon_lt_one n).le f))

private theorem measurable_evalSeq (s : Finset (Set.Icc (0 : ℝ) 1)) (n : ℕ) :
    Measurable (evalSeq s n) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_shiftedEval _ _).comp (measurable_restrict _)

private theorem measurable_reversedEvalSeq (s : Finset (Set.Icc (0 : ℝ) 1)) (n : ℕ) :
    Measurable (reversedEvalSeq s n) := by
  apply Measurable.of_eval
  intro i
  exact (measurable_shiftedEval _ _).comp
    ((measurable_reverseIncrements _).comp (measurable_restrict _))

private theorem map_evalSeq_eq_map_reversedEvalSeq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s : Finset (Set.Icc (0 : ℝ) 1)) (n : ℕ) :
    (stableBridgeLaw θ).map (evalSeq s n) = (stableBridgeLaw θ).map (reversedEvalSeq s n) := by
  apply ProbabilityMeasure.toMeasure_injective
  let b := bridgeHorizon n
  let G : D b ℝ → s → ℝ := fun g i => shiftedEval b i g
  have hG : Measurable G := Measurable.of_eval fun i => measurable_shiftedEval b i
  change (stableBridgeLaw θ : Measure (D 1 ℝ)).map
      (fun f => G (restrict (bridgeHorizon_lt_one n).le f)) =
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map
      (fun f => G (reverseIncrements (bridgeHorizon_pos n).le
        (restrict (bridgeHorizon_lt_one n).le f)))
  calc
    _ = ((stableBridgeLaw θ : Measure (D 1 ℝ)).map
        (restrict (bridgeHorizon_lt_one n).le)).map G := by
      simpa only [Function.comp_def] using
        (Measure.map_map hG (measurable_restrict (bridgeHorizon_lt_one n).le)).symm
    _ = (bridgePrefixLaw θ b (bridgeHorizon_pos n).le
        (stableProcessLaw θ b : Measure (D b ℝ))).map G := by
      rw [map_restrict_stableBridgeLaw hθ (bridgeHorizon_pos n) (bridgeHorizon_lt_one n)]
    _ = (bridgePrefixLaw θ b (bridgeHorizon_pos n).le
        (stableProcessLaw θ b : Measure (D b ℝ))).map
          (G ∘ reverseIncrements (bridgeHorizon_pos n).le) := by
      rw [← Measure.map_map hG (measurable_reverseIncrements _),
        map_reverseIncrements_bridgePrefixLaw hθ (bridgeHorizon_pos n)
          (isStableLevyLaw_stableProcessLaw hθ (bridgeHorizon_pos n))]
    _ = ((stableBridgeLaw θ : Measure (D 1 ℝ)).map
        (restrict (bridgeHorizon_lt_one n).le)).map
          (G ∘ reverseIncrements (bridgeHorizon_pos n).le) := by
      rw [map_restrict_stableBridgeLaw hθ (bridgeHorizon_pos n) (bridgeHorizon_lt_one n)]
    _ = _ := by
      simpa only [Function.comp_def] using
        (Measure.map_map (hG.comp (measurable_reverseIncrements _))
          (measurable_restrict (bridgeHorizon_lt_one n).le))

private theorem leftLim_restrict {f : D 1 ℝ} {b t : ℝ} (ht : 0 ≤ t) (htb : t ≤ b)
    (hb1 : b < 1) :
    Function.leftLim (restrict hb1.le f) ⟨t, ht, htb⟩ =
      Function.leftLim f ⟨t, ht, htb.trans hb1.le⟩ := by
  by_cases ht0 : t = 0
  · subst t
    rw [leftLim_eq_of_isBot (f := restrict hb1.le f) (fun u => u.2.1),
      leftLim_eq_of_isBot (f := f) (fun u => u.2.1)]
    rfl
  · have htpos : 0 < t := lt_of_le_of_ne ht (Ne.symm ht0)
    let tb : Set.Icc (0 : ℝ) b := ⟨t, ht, htb⟩
    let t1 : Set.Icc (0 : ℝ) 1 := ⟨t, ht, htb.trans hb1.le⟩
    let inc : Set.Icc (0 : ℝ) b → Set.Icc (0 : ℝ) 1 := fun u =>
      ⟨u, u.2.1, u.2.2.trans hb1.le⟩
    have hinc : Continuous inc := Continuous.subtype_mk continuous_subtype_val _
    have hleft : Tendsto inc (𝓝[<] tb) (𝓝[<] t1) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hinc.continuousAt, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hu
    let zb : Set.Icc (0 : ℝ) b := ⟨0, le_rfl, htpos.le.trans htb⟩
    have hz : zb < tb := htpos
    let z1 : Set.Icc (0 : ℝ) 1 := ⟨0, le_rfl, htpos.le.trans (htb.trans hb1.le)⟩
    have hz1 : z1 < t1 := htpos
    have : (𝓝[<] tb).NeBot := nhdsLT_neBot_of_exists_lt ⟨zb, hz⟩
    have : (𝓝[<] t1).NeBot := nhdsLT_neBot_of_exists_lt ⟨z1, hz1⟩
    apply leftLim_eq_of_tendsto
    exact ((isCadlag f).tendsto_nhdsLT_leftLim t1).comp hleft

private noncomputable def shiftedTime (n : ℕ) (s : Set.Icc (0 : ℝ) 1) :
    Set.Icc (0 : ℝ) 1 := ⟨max 0 (bridgeHorizon n - (1 - s)), le_max_left _ _, by
      apply max_le zero_le_one
      have hb := (bridgeHorizon_lt_one n).le
      have hs := s.2.1
      have hs1 := s.2.2
      linarith⟩

private theorem tendsto_shiftedTime {s : Set.Icc (0 : ℝ) 1} (hs : 0 < (s : ℝ)) :
    Tendsto (fun n => shiftedTime n s) atTop (𝓝 s) := by
  apply tendsto_subtype_rng.mpr
  have hev : ∀ᶠ n in atTop, 1 - (s : ℝ) ≤ bridgeHorizon n := by
    filter_upwards [tendsto_bridgeHorizon.eventually
      (Ioi_mem_nhds (sub_lt_self 1 hs))] with n hn
    exact hn.le
  have heq : (fun n => (shiftedTime n s : ℝ)) =ᶠ[atTop]
      fun n => bridgeHorizon n - (1 - s) := by
    filter_upwards [hev] with n hn
    simp [shiftedTime, max_eq_right (show 0 ≤ bridgeHorizon n - (1 - s) by linarith)]
  apply (tendsto_congr' heq).2
  simpa using tendsto_bridgeHorizon.sub (tendsto_const_nhds (x := 1 - (s : ℝ)))

private theorem eventually_evalSeq (s : Finset (Set.Icc (0 : ℝ) 1)) (f : D 1 ℝ)
    (i : s) (hi : 0 < (i : ℝ)) : ∀ᶠ n in atTop,
      evalSeq s n f i = f (shiftedTime n i) := by
  have hev : ∀ᶠ n in atTop, 1 - (i : ℝ) ≤ bridgeHorizon n := by
    filter_upwards [tendsto_bridgeHorizon.eventually
      (Ioi_mem_nhds (sub_lt_self 1 hi))] with n hn
    exact hn.le
  filter_upwards [hev] with n hn
  have hn' : 0 ≤ bridgeHorizon n - (1 - (i : ℝ)) := by linarith
  simp [evalSeq, shiftedEval, shiftedTime, hn, hn']
  rfl

private theorem ae_tendsto_evalSeq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s : Finset (Set.Icc (0 : ℝ) 1)) : ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      Tendsto (fun n => evalSeq s n f) atTop (𝓝 (fun i => f i)) := by
  have hc : ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      ∀ i : s, ContinuousAt f i := by
    rw [ae_all_iff]
    exact fun i => stableBridgeLaw_ae_continuousAt hθ i
  filter_upwards [hc, stableBridgeLaw_endpoints hθ] with f hfc he
  rw [tendsto_pi_nhds]
  intro i
  by_cases hi : (i : ℝ) = 0
  · have hi0 : (i : Set.Icc (0 : ℝ) 1) = ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext hi
    have hfi : f i = 0 := by rw [hi0]; exact he.1
    rw [hfi]
    have hev : ∀ n, evalSeq s n f i = 0 := by
      intro n
      have hn : ¬ 1 - (i : ℝ) ≤ bridgeHorizon n := by
        rw [hi]
        simpa using not_le_of_gt (bridgeHorizon_lt_one n)
      change shiftedEval (bridgeHorizon n) i (restrict (bridgeHorizon_lt_one n).le f) = 0
      unfold shiftedEval
      rw [dite_eq_right hn]
    exact (tendsto_congr' (Eventually.of_forall hev)).2 tendsto_const_nhds
  · have hipos : 0 < (i : ℝ) := lt_of_le_of_ne i.val.2.1 (Ne.symm hi)
    exact (tendsto_congr' (eventually_evalSeq s f i hipos)).2
      ((hfc i).tendsto.comp (tendsto_shiftedTime hipos))

private noncomputable def horizonTime (n : ℕ) : Set.Icc (0 : ℝ) 1 :=
  ⟨bridgeHorizon n, (bridgeHorizon_pos n).le, (bridgeHorizon_lt_one n).le⟩

private noncomputable def reverseTime (s : Set.Icc (0 : ℝ) 1) : Set.Icc (0 : ℝ) 1 :=
  ⟨1 - s, by linarith [s.2.2], by linarith [s.2.1]⟩

private theorem tendsto_horizonTime : Tendsto horizonTime atTop (𝓝 closedTop) := by
  apply tendsto_subtype_rng.mpr
  exact tendsto_bridgeHorizon

private theorem reversedEvalSeq_apply_of_le (s : Finset (Set.Icc (0 : ℝ) 1)) (f : D 1 ℝ)
    (i : s) (n : ℕ) (hn : 1 - (i : ℝ) ≤ bridgeHorizon n) :
    reversedEvalSeq s n f i = f (horizonTime n) - Function.leftLim f (reverseTime i) := by
  change shiftedEval (bridgeHorizon n) i
    (reverseIncrements (bridgeHorizon_pos n).le (restrict (bridgeHorizon_lt_one n).le f)) = _
  unfold shiftedEval
  rw [dite_eq_left hn, reverseIncrements_apply]
  change f (horizonTime n) - Function.leftLim (restrict (bridgeHorizon_lt_one n).le f)
    ⟨bridgeHorizon n - (bridgeHorizon n - (1 - (i : ℝ))),
      by linarith [i.val.2.2], by linarith [i.val.2.1]⟩ = _
  rw [show (⟨bridgeHorizon n - (bridgeHorizon n - (1 - (i : ℝ))),
      by linarith [i.val.2.2], by linarith [i.val.2.1]⟩ : Set.Icc (0 : ℝ) (bridgeHorizon n)) =
      ⟨1 - (i : ℝ), by linarith [i.val.2.2], hn⟩ by
    apply Subtype.ext
    dsimp
    ring]
  exact congrArg (fun x => f (horizonTime n) - x)
    (leftLim_restrict (f := f) (by linarith [i.val.2.2]) hn (bridgeHorizon_lt_one n))

private theorem eventually_reversedEvalSeq (s : Finset (Set.Icc (0 : ℝ) 1)) (f : D 1 ℝ)
    (i : s) (hi : 0 < (i : ℝ)) : ∀ᶠ n in atTop,
      reversedEvalSeq s n f i = f (horizonTime n) - Function.leftLim f (reverseTime i) := by
  have hev : ∀ᶠ n in atTop, 1 - (i : ℝ) ≤ bridgeHorizon n := by
    filter_upwards [tendsto_bridgeHorizon.eventually
      (Ioi_mem_nhds (sub_lt_self 1 hi))] with n hn
    exact hn.le
  filter_upwards [hev] with n hn
  exact reversedEvalSeq_apply_of_le s f i n hn

private theorem ae_tendsto_reversedEvalSeq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s : Finset (Set.Icc (0 : ℝ) 1)) : ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      Tendsto (fun n => reversedEvalSeq s n f) atTop (𝓝 (fun i => reverseBridge f i)) := by
  filter_upwards [stableBridgeLaw_endpoints hθ] with f he
  have hct : ContinuousAt f closedTop := continuousAt_top_of_leftLim_eq (he.2.1.trans he.2.2.symm)
  have htop : Tendsto (fun n => f (horizonTime n)) atTop (𝓝 0) := by
    have h := hct.tendsto.comp tendsto_horizonTime
    have he1 : f closedTop = 0 := he.2.1
    rw [he1] at h
    exact h
  rw [tendsto_pi_nhds]
  intro i
  by_cases hi : (i : ℝ) = 0
  · have hi0 : (i : Set.Icc (0 : ℝ) 1) = ⟨0, le_rfl, zero_le_one⟩ := Subtype.ext hi
    have hri : reverseBridge f i = 0 := by
      rw [hi0, reverseBridge_apply]
      simp only [sub_zero, neg_eq_zero]
      exact he.2.2
    rw [hri]
    have hev : ∀ n, reversedEvalSeq s n f i = 0 := by
      intro n
      have hn : ¬ 1 - (i : ℝ) ≤ bridgeHorizon n := by
        rw [hi]
        simpa using not_le_of_gt (bridgeHorizon_lt_one n)
      change shiftedEval (bridgeHorizon n) i
        (reverseIncrements (bridgeHorizon_pos n).le (restrict (bridgeHorizon_lt_one n).le f)) = 0
      unfold shiftedEval
      rw [dite_eq_right hn]
    exact (tendsto_congr' (Eventually.of_forall hev)).2 tendsto_const_nhds
  · have hipos : 0 < (i : ℝ) := lt_of_le_of_ne i.val.2.1 (Ne.symm hi)
    apply (tendsto_congr' (eventually_reversedEvalSeq s f i hipos)).2
    simpa [reverseBridge_apply, reverseTime] using
      htop.sub (tendsto_const_nhds (x := Function.leftLim f (reverseTime i)))

private theorem map_reverseBridge_finiteDimensional {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s : Finset (Set.Icc (0 : ℝ) 1)) :
    (stableBridgeLaw θ).map (fun f : D 1 ℝ => fun i : s => f i) =
      (stableBridgeLaw θ).map (fun f : D 1 ℝ => fun i : s => reverseBridge f i) := by
  let original : D 1 ℝ → s → ℝ := fun f i => f i
  let reversed : D 1 ℝ → s → ℝ := fun f i => reverseBridge f i
  change (stableBridgeLaw θ).map original = (stableBridgeLaw θ).map reversed
  have horiginal : Measurable original := by
    dsimp only [original]
    exact Measurable.of_eval fun i => measurable_eval i.val
  have hreversed : Measurable reversed := by
    dsimp only [reversed]
    exact Measurable.of_eval fun i =>
      (measurable_eval (i : Set.Icc (0 : ℝ) 1)).comp measurable_reverseBridge
  have hg : Tendsto (fun n => (stableBridgeLaw θ).map (evalSeq s n)) atTop
      (𝓝 ((stableBridgeLaw θ).map original)) := by
    exact tendsto_probabilityMeasure_map_of_ae_tendsto (stableBridgeLaw θ)
      (fun n => measurable_evalSeq s n) horiginal (ae_tendsto_evalSeq hθ s)
  have hh : Tendsto (fun n => (stableBridgeLaw θ).map (reversedEvalSeq s n)) atTop
      (𝓝 ((stableBridgeLaw θ).map reversed)) := by
    exact tendsto_probabilityMeasure_map_of_ae_tendsto (stableBridgeLaw θ)
      (fun n => measurable_reversedEvalSeq s n) hreversed (ae_tendsto_reversedEvalSeq hθ s)
  have hh' : Tendsto (fun n => (stableBridgeLaw θ).map (evalSeq s n)) atTop
      (𝓝 ((stableBridgeLaw θ).map reversed)) := by
    simpa only [map_evalSeq_eq_map_reversedEvalSeq hθ s] using hh
  exact tendsto_nhds_unique hg hh'

/-- **Reversal invariance.** `(stableBridgeLaw θ).map reverseBridge = stableBridgeLaw θ`. -/
theorem map_reverseBridge_stableBridgeLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    (stableBridgeLaw θ : Measure (D 1 ℝ)).map reverseBridge =
      (stableBridgeLaw θ : Measure (D 1 ℝ)) := by
  have hprob : (stableBridgeLaw θ).map reverseBridge = stableBridgeLaw θ := by
    apply ext_of_finiteDimensional dense_univ zero_le_one (mem_univ _)
    intro s _hs
    let ev : D 1 ℝ → s → ℝ := fun f i => f i
    let revEv : D 1 ℝ → s → ℝ := fun f i => reverseBridge f i
    have hev : Measurable ev := by
      dsimp only [ev]
      exact Measurable.of_eval fun i => measurable_eval i.val
    calc
      ((stableBridgeLaw θ).map reverseBridge).map ev = (stableBridgeLaw θ).map revEv := by
        apply ProbabilityMeasure.toMeasure_injective
        change ((stableBridgeLaw θ : Measure (D 1 ℝ)).map reverseBridge).map ev =
          (stableBridgeLaw θ : Measure (D 1 ℝ)).map revEv
        rw [Measure.map_map hev measurable_reverseBridge]
        rfl
      _ = (stableBridgeLaw θ).map ev := (map_reverseBridge_finiteDimensional hθ s).symm
  exact congrArg (fun Q : ProbabilityMeasure (D 1 ℝ) => (Q : Measure (D 1 ℝ))) hprob

/-- Almost surely the reversed path is the increment reversal of the original (the reversal of
the bridge is the reversal of increments on `{f 1 = 0}`). -/
theorem ae_reverseBridge_eq_reverseIncrements {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      reverseBridge f = reverseIncrements zero_le_one f := by
  filter_upwards [stableBridgeLaw_endpoints hθ] with f hf
  exact reverseBridge_eq_reverseIncrements hf.2.1

/-- Almost surely the reversal is an involution on the bridge (the totalized map is NOT an
involution on arbitrary paths with endpoint jumps, so this is stated a.s. only). -/
theorem ae_reverseBridge_reverseBridge {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)), reverseBridge (reverseBridge f) = f := by
  filter_upwards [stableBridgeLaw_endpoints hθ] with f he
  have hf : f closedTop = Function.leftLim f closedTop := he.2.1.trans he.2.2.symm
  ext s
  rw [reverseBridge_apply, leftLim_reverseBridge f hf]
  simp only [neg_neg]
  congr 1
  apply Subtype.ext
  dsimp
  ring

/-- The reversed bridge is again a pinned bridge: almost surely it starts and ends at `0` and has
no left jump at `1`. -/
theorem ae_endpoints_reverseBridge {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f : D 1 ℝ ∂(stableBridgeLaw θ : Measure (D 1 ℝ)),
      reverseBridge f ⟨0, le_rfl, zero_le_one⟩ = 0 ∧
        reverseBridge f ⟨1, zero_le_one, le_rfl⟩ = 0 ∧
        Function.leftLim (reverseBridge f) ⟨1, zero_le_one, le_rfl⟩ = 0 := by
  filter_upwards [stableBridgeLaw_endpoints hθ] with f he
  have hf : f closedTop = Function.leftLim f closedTop := he.2.1.trans he.2.2.symm
  refine ⟨?_, ?_, ?_⟩
  · rw [reverseBridge_apply]
    simp only [sub_zero, neg_eq_zero]
    exact he.2.2
  · rw [reverseBridge_apply]
    simp only [sub_self, neg_eq_zero]
    rw [leftLim_eq_of_isBot (f := f) (fun u => u.2.1)]
    exact he.1
  · rw [leftLim_reverseBridge f hf]
    simp only [sub_self, neg_eq_zero]
    exact he.1

end BGW.StableTrees
