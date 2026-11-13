/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.RealWalkTightness
public import BGW.StableTrees.RealAttractionBounds
public import BGW.Probability.RealWalkMaximal
public import BGW.Probability.RealWalkExitCount
public import BGW.Skorokhod.ExitPartition
public import BGW.Skorokhod.Tightness
public import BGW.Skorokhod.Measurable
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

import BGW.Skorokhod.Separable
import BGW.Skorokhod.CompleteMetricCompleteness
import BGW.Skorokhod.MeasurableExtrema
import Mathlib.MeasureTheory.Measure.Tight
import Mathlib.Topology.Order.Lattice

/-!
# Tightness of real walk step paths

The laws of the floor-step paths of a real iid walk are tight on Skorokhod space.  The proof
transfers compact containment and modulus bounds from the walk to its path law.

This is the tightness half of the functional limit theorem for walks in a stable domain of
attraction (item C17 of `CLASSICAL_THEORY_INPUTS.md`), through Billingsley's criterion with the
modulus `w'` (P. Billingsley, *Convergence of Probability Measures*, 1999, Theorem 13.2).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology ENNReal

namespace BGW.Skorokhod

open BGW.Probability.RealWalk

/-- The step path depends continuously on the real walk with its product topology. -/
theorem continuous_realStepPath (T : ℝ) (n : ℕ) (b : ℝ) :
    Continuous (realStepPath T n b) := by
  by_cases hT : 0 ≤ T
  · apply continuous_iff_continuousAt.2
    intro ω₀
    rw [Metric.continuousAt_iff']
    intro ε hε
    let M : ℕ := ⌊(n : ℝ) * T⌋₊
    let s : Finset (Fin (M + 1)) := Finset.univ
    let p (k : Fin (M + 1)) (ω : ℕ → ℝ) : ℝ :=
      |partialSum ω k.val / b - partialSum ω₀ k.val / b|
    let q (ω : ℕ → ℝ) : ℝ := s.sup' Finset.univ_nonempty fun k => p k ω
    have hq_cont : Continuous q := by
      change Continuous (fun ω => s.sup' Finset.univ_nonempty (fun k => p k ω))
      exact Continuous.finset_sup'_apply Finset.univ_nonempty fun k hk => by
        dsimp [p]
        unfold partialSum
        fun_prop
    have hq_zero : q ω₀ = 0 := by
      simp [q, p, s]
    have hq_event : ∀ᶠ ω in 𝓝 ω₀, q ω < ε := by
      have hcont : ContinuousAt q ω₀ := hq_cont.continuousAt
      have hq_lt : q ω₀ < ε := by simpa [hq_zero] using hε
      exact hcont.eventually (Iio_mem_nhds hq_lt)
    filter_upwards [hq_event] with ω hω
    ·
      have hdist : dist (realStepPath T n b ω) (realStepPath T n b ω₀) ≤ q ω := by
        refine (dist_le_iSup_dist _ _).trans ?_
        apply csSup_le
        · exact ⟨_, ⟨⟨0, by simp [hT]⟩, rfl⟩⟩
        · intro d hd
          rcases hd with ⟨t, rfl⟩
          change dist (realStepPath T n b ω t) (realStepPath T n b ω₀ t) ≤ q ω
          rw [realStepPath_apply, realStepPath_apply]
          let k : ℕ := ⌊(n : ℝ) * (t : ℝ)⌋₊
          have ht : (n : ℝ) * (t : ℝ) ≤ (n : ℝ) * T :=
            mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
          have hk : k ≤ M := by
            dsimp [k, M]
            exact Nat.floor_mono ht
          have hk' : k < M + 1 := by omega
          have hle := Finset.le_sup' (fun j : Fin (M + 1) => p j ω)
            (Finset.mem_univ ⟨k, hk'⟩)
          change p ⟨k, hk'⟩ ω ≤ s.sup' Finset.univ_nonempty (fun j => p j ω)
          exact hle
      exact lt_of_le_of_lt hdist hω
  · have hneg : T < 0 := lt_of_not_ge hT
    have hsubsingleton : ∀ f g : D T ℝ, f = g := by
      intro f g
      apply BGW.Skorokhod.ext
      intro t
      exact (not_le_of_gt hneg (le_trans t.property.1 t.property.2)).elim
    have hconst : realStepPath T n b = fun _ => realStepPath T n b 0 := by
      funext ω
      exact hsubsingleton _ _
    rw [hconst]
    exact continuous_const

/-- The continuous step-path map is Borel measurable. -/
theorem measurable_realStepPath (T : ℝ) (n : ℕ) (b : ℝ) :
    Measurable (realStepPath T n b) :=
  (continuous_realStepPath T n b).measurable

/-- The step path starts at zero whenever its time interval contains zero. -/
theorem realStepPath_apply_zero {T : ℝ} (hT : 0 ≤ T) (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) :
    realStepPath T n b ω ⟨0, le_rfl, hT⟩ = 0 := by
  simp [realStepPath, BGW.Probability.RealWalk.partialSum]

end BGW.Skorokhod

namespace BGW.StableTrees

open BGW.Probability.RealWalk BGW.Skorokhod

/-- The law of the floor-step path `t ↦ S_{⌊n t⌋} / B n` on `[0,T]`,
as the genuine pushforward of `iidLaw ν` under the canonical walk map. The normalizer `B n` is
arbitrary; no attraction
hypothesis is needed to define the law. -/
noncomputable def stepPathLaw (ν : ProbabilityMeasure ℝ) (T : ℝ) (B : ℕ → ℝ) (n : ℕ) :
    ProbabilityMeasure (D T ℝ) :=
  (iidLaw ν).map (realStepPath T n (B n))

/-- The coercion of `stepPathLaw` to a measure is the pushforward of the canonical walk measure. -/
theorem coe_stepPathLaw (ν : ProbabilityMeasure ℝ) (T : ℝ) (B : ℕ → ℝ) (n : ℕ) :
    (stepPathLaw ν T B n : Measure (D T ℝ)) =
      Measure.map (realStepPath T n (B n)) (iidLaw ν : Measure (ℕ → ℝ)) := rfl

/-- Every individual step-path law is tight, independently of attraction assumptions. -/
theorem isTightMeasureSet_stepPathLaw_singleton (ν : ProbabilityMeasure ℝ) (T : ℝ)
    (B : ℕ → ℝ) (n : ℕ) :
    IsTightMeasureSet {(stepPathLaw ν T B n : Measure (D T ℝ))} := by
  exact MeasureTheory.isTightMeasureSet_singleton

private theorem measure_maxExceed_eq_ofReal_maxTail (ν : ProbabilityMeasure ℝ)
    (m : ℕ) (r : ℝ) :
    (iidLaw ν : Measure (ℕ → ℝ)) (maxExceed m r) = ENNReal.ofReal (maxTail ν m r) := by
  rw [maxTail, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]

/-- Compact containment of a step path is bounded by the walk's finite-horizon maximum tail. -/
theorem stepPathLaw_not_mem_Icc_le (ν : ProbabilityMeasure ℝ) {T : ℝ} (hT : 0 < T)
    (B : ℕ → ℝ) (n : ℕ) (hB : 0 < B n) (K : ℝ) :
    (stepPathLaw ν T B n : Measure (D T ℝ)) {f | ∃ t, f t ∉ Set.Icc (-K) K} ≤
      ENNReal.ofReal (maxTail ν ⌊(n : ℝ) * T⌋₊ (K * B n)) := by
  -- Positivity is part of the audited finite-horizon statement; the countable-time argument
  -- below also works for an empty or degenerate interval.
  have _hT : 0 < T := hT
  let A : Set (D T ℝ) := {f | ∃ t, f t ∉ Set.Icc (-K) K}
  let J : Set (Set.Icc (0 : ℝ) T) := Set.univ
  have hJ : Set.OrdConnected J := by
    simpa [J] using (Set.ordConnected_univ : Set.OrdConnected
      (Set.univ : Set (Set.Icc (0 : ℝ) T)))
  obtain ⟨Q, hQ_countable, hQ_detect⟩ :=
    BGW.Skorokhod.exists_countable_detecting_times hJ
  let QT := {q : J // q ∈ Q}
  let _ : Countable QT := hQ_countable.to_subtype
  have hAeq : A = ⋃ q : QT, {f | f q.val.val ∉ Set.Icc (-K) K} := by
    ext f
    constructor
    · rintro ⟨t, ht⟩
      have hnot : f t ∈ (Set.Icc (-K) K)ᶜ := ht
      obtain ⟨q, hq, hqnot⟩ := hQ_detect ℝ f (Set.Icc (-K) K)ᶜ
        isClosed_Icc.isOpen_compl
        ⟨t, Set.mem_univ t⟩ hnot
      exact Set.mem_iUnion.2 ⟨⟨q, hq⟩, hqnot⟩
    · intro hf
      obtain ⟨q, hq⟩ := Set.mem_iUnion.1 hf
      exact ⟨q.val.val, hq⟩
  have hA_meas : MeasurableSet A := by
    rw [hAeq]
    exact MeasurableSet.iUnion fun q =>
      measurable_eval q.val.val isClosed_Icc.measurableSet.compl
  have hpre : realStepPath T n (B n) ⁻¹' A ⊆
      maxExceed ⌊(n : ℝ) * T⌋₊ (K * B n) := by
    rintro ω ⟨t, ht⟩
    have habs : K < |realStepPath T n (B n) ω t| := by
      simp only [Set.mem_Icc, not_and_or] at ht
      rcases ht with hlow | hhigh
      · exact lt_of_lt_of_le (by linarith) (neg_le_abs _)
      · exact (lt_of_not_ge hhigh).trans_le (le_abs_self _)
    let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
    have hk : k ≤ ⌊(n : ℝ) * T⌋₊ := by
      apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left t.property.2 (Nat.cast_nonneg n)
    rw [realStepPath_apply] at habs
    rw [abs_div, abs_of_pos hB] at habs
    refine ⟨k, hk, ?_⟩
    exact (lt_div_iff₀ hB).mp habs
  calc
    _ = Measure.map (realStepPath T n (B n)) (iidLaw ν : Measure (ℕ → ℝ)) A := by
      rw [coe_stepPathLaw]
    _ = (iidLaw ν : Measure (ℕ → ℝ)) (realStepPath T n (B n) ⁻¹' A) :=
      Measure.map_apply_of_aemeasurable
        (measurable_realStepPath T n (B n)).aemeasurable hA_meas
    _ ≤ (iidLaw ν : Measure (ℕ → ℝ)) (maxExceed ⌊(n : ℝ) * T⌋₊ (K * B n)) :=
      measure_mono hpre
    _ = ENNReal.ofReal (maxTail ν ⌊(n : ℝ) * T⌋₊ (K * B n)) :=
      measure_maxExceed_eq_ofReal_maxTail ν _ _

/-- The initial-window bad event is bounded by the corresponding short-block maximum. -/
theorem measureReal_initialBad_le (ν : ProbabilityMeasure ℝ) (T : ℝ) (n : ℕ) {b ε δ : ℝ}
    (hb : 0 < b) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | initialBad T n b ε δ ω} ≤
      maxTail ν ⌊2 * (n : ℝ) * δ⌋₊ (ε * b) := by
  let m := ⌊2 * (n : ℝ) * δ⌋₊
  by_cases hδ : 0 ≤ δ
  · have hsub : {ω | initialBad T n b ε δ ω} ⊆ maxExceed m (ε * b) := by
      rintro ω ⟨t, ht0, htδ, htT, hmove⟩
      have htM : (n : ℝ) * t ≤ 2 * (n : ℝ) * δ := by
        nlinarith [mul_le_mul_of_nonneg_left htδ (Nat.cast_nonneg n)]
      let k := ⌊(n : ℝ) * t⌋₊
      have hk : k ≤ m := by
        dsimp [k, m]
        exact Nat.floor_mono htM
      have hstep : ε < |partialSum ω k / b| := by
        simpa [stepValue, k, partialSum] using hmove
      have hscaled : ε * b < |partialSum ω k| := by
        rw [abs_div, abs_of_pos hb] at hstep
        exact (lt_div_iff₀ hb).mp hstep
      exact ⟨k, hk, hscaled⟩
    calc
      _ ≤ (iidLaw ν : Measure (ℕ → ℝ)).real (maxExceed m (ε * b)) :=
        measureReal_mono hsub (measure_ne_top _ _)
      _ = maxTail ν m (ε * b) := rfl
  · have hempty : {ω | initialBad T n b ε δ ω} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨t, ht0, htδ, htT, _⟩
      linarith
    rw [hempty]
    simpa [hempty] using maxTail_nonneg ν m (ε * b)

/-- The terminal-window bad event is bounded using a fresh start at its left endpoint. -/
theorem measureReal_terminalBad_le (ν : ProbabilityMeasure ℝ) {T : ℝ} (n : ℕ) {b ε δ : ℝ}
    (hb : 0 < b) (hδ : 0 ≤ δ) (hδT : 2 * δ ≤ T) :
    (iidLaw ν : Measure (ℕ → ℝ)).real {ω | terminalBad T n b ε δ ω} ≤
      maxTail ν (⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * (T - 2 * δ)⌋₊) (ε * b) := by
  -- Retain the audited nonnegative-window premise; the endpoint estimate itself also follows
  -- from the left and right endpoint inequalities.
  have _hδ : 0 ≤ δ := hδ
  let M := ⌊(n : ℝ) * T⌋₊
  let j := ⌊(n : ℝ) * (T - 2 * δ)⌋₊
  let m := M - j
  have hsub : {ω | terminalBad T n b ε δ ω} ⊆
      {ω | ∃ k ≤ m, ε * b < |blockSum ω j k|} := by
    rintro ω ⟨t, htleft, htright, hmove⟩
    let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
    have hs_nonneg : 0 ≤ T - 2 * δ := by linarith
    have hjk : j ≤ k := by
      dsimp [j, k]
      apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left htleft (Nat.cast_nonneg n)
    have hkM : k ≤ M := by
      dsimp [k, M]
      apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left htright (Nat.cast_nonneg n)
    have hq : k - j ≤ m := by
      dsimp [m, M, j]
      exact Nat.sub_le_sub_right hkM _
    have hstep : ε < |(partialSum ω k - partialSum ω j) / b| := by
      have hmove' := hmove
      change ε < |partialSum ω k / b - partialSum ω j / b| at hmove'
      have hdiv : partialSum ω k / b - partialSum ω j / b =
          (partialSum ω k - partialSum ω j) / b := by ring
      rw [hdiv] at hmove'
      exact hmove'
    have hsum : partialSum ω k - partialSum ω j = blockSum ω j (k - j) := by
      have hkEq : j + (k - j) = k := by omega
      calc
        partialSum ω k - partialSum ω j =
            partialSum ω (j + (k - j)) - partialSum ω j := by rw [hkEq]
        _ = blockSum ω j (k - j) := by rw [partialSum_add]; ring
    have hscaled : ε * b < |blockSum ω j (k - j)| := by
      have hstepBlock : ε < |blockSum ω j (k - j) / b| := by
        rw [← hsum]
        exact hstep
      rw [abs_div, abs_of_pos hb] at hstepBlock
      exact (lt_div_iff₀ hb).mp hstepBlock
    exact ⟨k - j, hq, hscaled⟩
  calc
    _ ≤ (iidLaw ν : Measure (ℕ → ℝ)).real {ω | ∃ k ≤ m, ε * b < |blockSum ω j k|} :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ = maxTail ν m (ε * b) := measureReal_exceed_block ν j m (ε * b)

/-- The terminal window spans at most `2 n δ + 1` discrete indices. -/
theorem floor_sub_floor_le {T : ℝ} (n : ℕ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hδT : 2 * δ ≤ T) :
    ((⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * (T - 2 * δ)⌋₊ : ℕ) : ℝ) ≤
      2 * n * δ + 1 := by
  let x := (n : ℝ) * T
  let y := (n : ℝ) * (T - 2 * δ)
  have hT : 0 ≤ T := le_trans (mul_nonneg (by norm_num) hδ) hδT
  have hy : 0 ≤ y := mul_nonneg (Nat.cast_nonneg n) (sub_nonneg.mpr hδT)
  have hyx : y ≤ x := by dsimp [y, x]; nlinarith
  have hfloor : ⌊y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hyx
  have hx_floor : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le (mul_nonneg (Nat.cast_nonneg n) hT)
  have hy_floor : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  have hcast : ((⌊x⌋₊ - ⌊y⌋₊ : ℕ) : ℝ) = (⌊x⌋₊ : ℝ) - ⌊y⌋₊ :=
    Nat.cast_sub hfloor
  rw [show ⌊(n : ℝ) * T⌋₊ = ⌊x⌋₊ by rfl,
    show ⌊(n : ℝ) * (T - 2 * δ)⌋₊ = ⌊y⌋₊ by rfl, hcast]
  dsimp [x, y]
  nlinarith

/-- The outer measure of the path modulus event is controlled by the three finite-coordinate
bad events from the exit partition. Inner regularity on the walk space bridges the potentially
nonmeasurable modulus event without applying `Measure.map` to it. -/
theorem stepPathLaw_modulus_le (ν : ProbabilityMeasure ℝ) {T : ℝ} (hT : 0 < T)
    (B : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n) (hB : 0 < B n) {ε δ : ℝ}
    (hε : 0 < ε) (hδ : 0 < δ)
    (hδT : 4 * δ < T) :
    (stepPathLaw ν T B n : Measure (D T ℝ)) {f | 4 * ε < cadlagModulus f δ} ≤
      ENNReal.ofReal
        ((iidLaw ν : Measure (ℕ → ℝ)).real
            {ω | closeExit ⌊(n : ℝ) * T⌋₊ (ε * B n) ⌈2 * n * δ + 2⌉₊ ω} +
          (iidLaw ν : Measure (ℕ → ℝ)).real {ω | initialBad T n (B n) ε δ ω} +
          (iidLaw ν : Measure (ℕ → ℝ)).real {ω | terminalBad T n (B n) ε δ ω}) := by
  let μ : Measure (ℕ → ℝ) := iidLaw ν
  let μp : Measure (D T ℝ) := stepPathLaw ν T B n
  let M := ⌊(n : ℝ) * T⌋₊
  let L := ⌈2 * n * δ + 2⌉₊
  let C : Set (ℕ → ℝ) := {ω | closeExit M (ε * B n) L ω}
  let I : Set (ℕ → ℝ) := {ω | initialBad T n (B n) ε δ ω}
  let U : Set (ℕ → ℝ) := {ω | terminalBad T n (B n) ε δ ω}
  let Bad : Set (ℕ → ℝ) := C ∪ (I ∪ U)
  let G : Set (ℕ → ℝ) := (toMeasurable μ Bad)ᶜ
  let A : Set (D T ℝ) := {f | 4 * ε < cadlagModulus f δ}
  let r : ℝ := μ.real C + μ.real I + μ.real U
  let g : (ℕ → ℝ) → D T ℝ := realStepPath T n (B n)
  have hcoe : μp = Measure.map g μ := by
    dsimp [μp, μ, g]
    exact coe_stepPathLaw ν T B n
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hBad_real : μ.real Bad ≤ r := by
    calc
      μ.real Bad = μ.real (C ∪ (I ∪ U)) := rfl
      _ ≤ μ.real C + μ.real (I ∪ U) := measureReal_union_le _ _
      _ ≤ μ.real C + (μ.real I + μ.real U) := by
        have h := measureReal_union_le (μ := μ) I U
        linarith
      _ = r := by dsimp [r]; ring
  have hBad_enn : μ Bad ≤ ENNReal.ofReal r := by
    calc
      μ Bad = ENNReal.ofReal (μ.real Bad) := by
        rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
      _ ≤ ENNReal.ofReal r := ENNReal.ofReal_le_ofReal hBad_real
  have hG_meas : MeasurableSet G := by
    change MeasurableSet ((toMeasurable μ Bad)ᶜ)
    exact (measurableSet_toMeasurable μ Bad).compl
  have hgood (ω : ℕ → ℝ) (hω : ω ∈ G) : g ω ∉ A := by
    have hω_notBad : ω ∉ Bad := by
      intro hωBad
      exact hω (subset_toMeasurable μ Bad hωBad)
    have hclose : ¬ closeExit M (ε * B n) L ω := by
      intro hc
      exact hω_notBad (Or.inl hc)
    have hinitial : ¬ initialBad T n (B n) ε δ ω := by
      intro hi
      exact hω_notBad (Or.inr (Or.inl hi))
    have hterminal : ¬ terminalBad T n (B n) ε δ ω := by
      intro ht
      exact hω_notBad (Or.inr (Or.inr ht))
    have hmod := cadlagModulus_realStepPath_le hT hn hB hε hδ hδT hclose hinitial hterminal
    change ¬ (4 * ε < cadlagModulus (g ω) δ)
    exact not_lt_of_ge hmod
  have hbound (e : ℝ) (he : 0 < e) : μp A ≤ ENNReal.ofReal (r + e) := by
    obtain ⟨K, hKG, hKcompact, hGminus⟩ :=
      hG_meas.exists_isCompact_sdiff_lt (measure_ne_top μ G)
        (ε := ENNReal.ofReal e) (ENNReal.ofReal_ne_zero_iff.mpr he)
    have hA_image : A ⊆ (g '' K)ᶜ := by
      intro f hf himage
      obtain ⟨ω, hωK, hωeq⟩ := himage
      apply hgood ω (hKG hωK)
      rw [hωeq]
      exact hf
    have hpre : g ⁻¹' (g '' K)ᶜ ⊆ Kᶜ := by
      intro ω hω hωK
      exact hω ⟨ω, hωK, rfl⟩
    have himage_closed : IsClosed (g '' K) := by
      have hcompact : IsCompact (g '' K) :=
        hKcompact.image (continuous_realStepPath T n (B n))
      exact hcompact.isClosed
    have hmap_le : μp A ≤ μ Kᶜ := by
      rw [hcoe]
      calc
        Measure.map g μ A ≤ Measure.map g μ (g '' K)ᶜ := measure_mono hA_image
        _ = μ (g ⁻¹' (g '' K)ᶜ) :=
          Measure.map_apply_of_aemeasurable (measurable_realStepPath T n (B n)).aemeasurable
            himage_closed.measurableSet.compl
        _ ≤ μ Kᶜ := measure_mono hpre
    have hKcompl_eq : Kᶜ = toMeasurable μ Bad ∪ (G \ K) := by
      ext ω
      constructor
      · intro hωK
        by_cases hωbad : ω ∈ toMeasurable μ Bad
        · exact Or.inl hωbad
        · exact Or.inr ⟨hωbad, hωK⟩
      · rintro (hωbad | ⟨hωgood, hωK⟩)
        · intro hωK'
          exact (hKG hωK') hωbad
        · exact hωK
    have hKcompl_le : μ Kᶜ ≤ ENNReal.ofReal (r + e) := by
      rw [hKcompl_eq]
      calc
        μ (toMeasurable μ Bad ∪ (G \ K)) ≤
            μ (toMeasurable μ Bad) + μ (G \ K) := measure_union_le _ _
        _ = μ Bad + μ (G \ K) := by rw [measure_toMeasurable]
        _ ≤ ENNReal.ofReal r + ENNReal.ofReal e := add_le_add hBad_enn hGminus.le
        _ = ENNReal.ofReal (r + e) := (ENNReal.ofReal_add hr he.le).symm
    exact hmap_le.trans hKcompl_le
  by_contra hnot
  have hμpA_top : μp A ≠ ∞ := measure_ne_top _ _
  have hμpA_gt : ENNReal.ofReal r < μp A := lt_of_not_ge hnot
  have hμpA_gt_real : r < (μp A).toReal :=
    (ENNReal.ofReal_lt_iff_lt_toReal hr hμpA_top).mp hμpA_gt
  let e := ((μp A).toReal - r) / 2
  have he : 0 < e := by dsimp [e]; linarith
  have hsmall := hbound e he
  have hμpA_le_real : (μp A).toReal ≤ r + e := by
    have h := ENNReal.toReal_mono (by simp) hsmall
    simpa [ENNReal.toReal_ofReal, add_nonneg hr he.le] using h
  dsimp [e] at hμpA_le_real
  linarith

/-! ### Eventual estimates and tightness for an attracted walk -/

/-- For every positive tolerance, the step-path laws eventually stay in one bounded interval
with all but that much mass. -/
theorem IsRealStableAttracted.stepPath_bounded_eventually {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    ∀ η > 0, ∃ K : Set ℝ, Bornology.IsBounded K ∧ ∃ N : ℕ, ∀ n ≥ N,
      (stepPathLaw ν T B n : Measure (D T ℝ)) {f | ∃ t, f t ∉ K} ≤ ENNReal.ofReal η := by
  intro η hη
  obtain ⟨K, hKpos, NK, htail⟩ := h.horizon_max_tight hT η hη
  obtain ⟨Npos, hpos⟩ := Filter.eventually_atTop.1 h.pos
  refine ⟨Set.Icc (-K) K, Metric.isBounded_Icc _ _, max NK Npos, ?_⟩
  intro n hn
  have hnK : NK ≤ n := le_trans (le_max_left _ _) hn
  have hnpos : Npos ≤ n := le_trans (le_max_right _ _) hn
  calc
    _ ≤ ENNReal.ofReal (maxTail ν ⌊(n : ℝ) * T⌋₊ (K * B n)) :=
      stepPathLaw_not_mem_Icc_le ν hT B n (hpos n hnpos) K
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal (htail n hnK)

/-- The step-path laws eventually have arbitrarily small Skorokhod modulus at a sufficiently
short time scale. -/
theorem IsRealStableAttracted.stepPath_modulus_eventually {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    ∀ ε > 0, ∀ η > 0, ∃ δ : ℝ, 0 < δ ∧ δ < T ∧ ∃ N : ℕ, ∀ n ≥ N,
      (stepPathLaw ν T B n : Measure (D T ℝ)) {f | ε < cadlagModulus f δ} ≤
        ENNReal.ofReal η := by
  intro ε hε η hη
  let e := ε / 8
  have he : 0 < e := by dsimp [e]; positivity
  obtain ⟨a, ha, Nsafe, hsafe⟩ := h.small_block_max e he (1 / 2) (by norm_num)
  let C := 2 * (2 * T / a + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  let q := η / (2 * (C + 2))
  have hq : 0 < q := by dsimp [q]; positivity
  obtain ⟨α, hα, Nshort, hshort⟩ := h.small_block_max e he q hq
  let δ := min (α / 4) (T / 8)
  have hδpos : 0 < δ := by dsimp [δ]; positivity
  have hδα : δ ≤ α / 4 := min_le_left _ _
  have hδT4 : 4 * δ < T := by
    have hδT : δ ≤ T / 8 := min_le_right _ _
    dsimp [δ] at hδT ⊢
    nlinarith [hT]
  have hδT : δ < T := by linarith
  have hδT2 : 2 * δ ≤ T := by linarith
  obtain ⟨Npos, hpos⟩ := Filter.eventually_atTop.1 h.pos
  let L := fun n : ℕ => ⌊a * (n : ℝ)⌋₊
  have hLtop : Tendsto L atTop atTop := by
    simpa [L] using tendsto_nat_floor_mul_atTop a ha
  obtain ⟨NL, hNL⟩ := Filter.eventually_atTop.1
    (hLtop.eventually (Filter.eventually_ge_atTop 2))
  have hαtop : Tendsto (fun n : ℕ => α * (n : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop hα tendsto_natCast_atTop_atTop
  obtain ⟨Nα, hNα⟩ := Filter.eventually_atTop.1
    (hαtop.eventually (Filter.eventually_ge_atTop 2))
  let N := max Nsafe (max Nshort (max Npos (max NL Nα)))
  refine ⟨δ, hδpos, hδT, N, ?_⟩
  intro n hn
  have hnSafe : Nsafe ≤ n := by
    apply le_trans (le_max_left _ _)
    exact hn
  have hnShort : Nshort ≤ n := by
    apply le_trans (le_max_left _ _)
    apply le_trans (le_max_right _ _)
    exact hn
  have hnPos : Npos ≤ n := by
    apply le_trans (le_max_left _ _)
    apply le_trans (le_max_right _ _)
    apply le_trans (le_max_right _ _)
    exact hn
  have hnL : NL ≤ n := by
    apply le_trans (le_max_left _ _)
    apply le_trans (le_max_right _ _)
    apply le_trans (le_max_right _ _)
    apply le_trans (le_max_right _ _)
    exact hn
  have hnα : Nα ≤ n := by
    apply le_trans (le_max_right _ _)
    apply le_trans (le_max_right _ _)
    apply le_trans (le_max_right _ _)
    apply le_trans (le_max_right _ _)
    exact hn
  have hnB : 0 < B n := hpos n hnPos
  let M := ⌊(n : ℝ) * T⌋₊
  let Lₙ := L n
  let mclose := ⌈2 * (n : ℝ) * δ + 2⌉₊
  let minitial := ⌊2 * (n : ℝ) * δ⌋₊
  let mterminal := ⌊(n : ℝ) * T⌋₊ - ⌊(n : ℝ) * (T - 2 * δ)⌋₊
  have hLnat : 2 ≤ Lₙ := hNL n hnL
  have hLcast : 2 ≤ (Lₙ : ℝ) := by exact_mod_cast hLnat
  have han : 2 ≤ a * (n : ℝ) := by
    have hfloor : (Lₙ : ℝ) ≤ a * (n : ℝ) := by
      dsimp [Lₙ, L]
      exact Nat.floor_le (by positivity)
    linarith
  have hLlower : a * (n : ℝ) / 2 ≤ (Lₙ : ℝ) := by
    have hfloor : a * (n : ℝ) - 1 < (Lₙ : ℝ) := by
      dsimp [Lₙ, L]
      exact Nat.sub_one_lt_floor _
    nlinarith
  have hLsafe : (Lₙ : ℝ) ≤ a * (n : ℝ) + 2 := by
    have hfloor : (Lₙ : ℝ) ≤ a * (n : ℝ) := by
      dsimp [Lₙ, L]
      exact Nat.floor_le (by positivity)
    linarith
  have hsafeN := hsafe n hnSafe Lₙ hLsafe
  have hαn : 2 ≤ α * (n : ℝ) := hNα n hnα
  have hshort_bound (m : ℕ) (hm : (m : ℝ) ≤ α * (n : ℝ) + 2) :
      maxTail ν m (e * B n) ≤ q := hshort n hnShort m hm
  have hMupper : (M : ℝ) ≤ (n : ℝ) * T := by
    dsimp [M]
    exact Nat.floor_le (by positivity)
  have hLpos : 0 < (Lₙ : ℝ) := by positivity
  have hratio : (M : ℝ) / (Lₙ : ℝ) ≤ 2 * T / a := by
    apply (div_le_iff₀ hLpos).2
    calc
      (M : ℝ) ≤ (n : ℝ) * T := hMupper
      _ = (2 * T / a) * (a * (n : ℝ) / 2) := by field_simp [ha.ne']
      _ ≤ (2 * T / a) * (Lₙ : ℝ) :=
        mul_le_mul_of_nonneg_left hLlower (le_of_lt (by positivity))
  have hfactor : 2 * ((M : ℝ) / (Lₙ : ℝ) + 1) ≤ C := by
    dsimp [C]
    linarith
  have hcloseLen : (mclose : ℝ) ≤ α * (n : ℝ) + 2 := by
    have hceil := Nat.ceil_le_floor_add_one (2 * (n : ℝ) * δ + 2)
    have hfloor :
        (⌊2 * (n : ℝ) * δ + 2⌋₊ : ℝ) ≤ 2 * (n : ℝ) * δ + 2 :=
      Nat.floor_le (by positivity)
    have hceilCast : (mclose : ℝ) ≤ 2 * (n : ℝ) * δ + 3 := by
      calc
        (mclose : ℝ) ≤ (⌊2 * (n : ℝ) * δ + 2⌋₊ : ℝ) + 1 := by
          dsimp [mclose]
          exact_mod_cast hceil
        _ ≤ 2 * (n : ℝ) * δ + 3 := by linarith
    nlinarith [hδα, hαn, hceilCast]
  have hinitialLen : (minitial : ℝ) ≤ α * (n : ℝ) + 2 := by
    have hfloor : (minitial : ℝ) ≤ 2 * (n : ℝ) * δ := by
      dsimp [minitial]
      exact Nat.floor_le (by positivity)
    nlinarith [hδα, hαn]
  have hterminalLen : (mterminal : ℝ) ≤ α * (n : ℝ) + 2 := by
    have hbound := floor_sub_floor_le n hδpos.le hδT2
    dsimp [mterminal] at hbound ⊢
    nlinarith [hbound, hδα, hαn]
  have hclose :
      (iidLaw ν : Measure (ℕ → ℝ)).real
        {ω | closeExit M (e * B n) mclose ω} ≤ C * q := by
    calc
      _ ≤ 2 * ((M : ℝ) / Lₙ + 1) * maxTail ν mclose (e * B n) :=
        measure_closeExit_le_of_safe ν (mul_pos he hnB) (by omega)
          hsafeN mclose
      _ ≤ 2 * ((M : ℝ) / Lₙ + 1) * q :=
        mul_le_mul_of_nonneg_left (hshort_bound mclose hcloseLen) (by positivity)
      _ ≤ C * q := mul_le_mul_of_nonneg_right hfactor hq.le
  have hinitial :
      (iidLaw ν : Measure (ℕ → ℝ)).real
        {ω | initialBad T n (B n) e δ ω} ≤ q := by
    calc
      _ ≤ maxTail ν minitial (e * B n) :=
        measureReal_initialBad_le ν T n hnB
      _ ≤ q := hshort_bound minitial hinitialLen
  have hterminal :
      (iidLaw ν : Measure (ℕ → ℝ)).real
        {ω | terminalBad T n (B n) e δ ω} ≤ q := by
    calc
      _ ≤ maxTail ν mterminal (e * B n) :=
        measureReal_terminalBad_le ν (T := T) n hnB hδpos.le hδT2
      _ ≤ q := hshort_bound mterminal hterminalLen
  have hsum :
      (iidLaw ν : Measure (ℕ → ℝ)).real
          {ω | closeExit M (e * B n) mclose ω} +
        (iidLaw ν : Measure (ℕ → ℝ)).real
          {ω | initialBad T n (B n) e δ ω} +
        (iidLaw ν : Measure (ℕ → ℝ)).real
          {ω | terminalBad T n (B n) e δ ω} ≤ η := by
    calc
      _ ≤ C * q + q + q := add_le_add (add_le_add hclose hinitial) hterminal
      _ = η / 2 := by dsimp [q]; field_simp; ring
      _ ≤ η := by linarith
  have hnOne : 1 ≤ n := by
    have hnZero : n ≠ 0 := by
      intro hnZero
      subst n
      norm_num at han
    exact Nat.one_le_iff_ne_zero.mpr hnZero
  have hmod := stepPathLaw_modulus_le ν hT B hnOne hnB he hδpos hδT4
  have hsubset : {f : D T ℝ | ε < cadlagModulus f δ} ⊆
      {f | 4 * e < cadlagModulus f δ} := by
    intro f hf
    have heps : 4 * e < ε := by dsimp [e]; linarith
    exact lt_trans heps hf
  calc
    _ ≤ (stepPathLaw ν T B n : Measure (D T ℝ)) {f | 4 * e < cadlagModulus f δ} :=
      measure_mono hsubset
    _ ≤ ENNReal.ofReal
        ((iidLaw ν : Measure (ℕ → ℝ)).real
            {ω | closeExit M (e * B n) mclose ω} +
          (iidLaw ν : Measure (ℕ → ℝ)).real {ω | initialBad T n (B n) e δ ω} +
          (iidLaw ν : Measure (ℕ → ℝ)).real {ω | terminalBad T n (B n) e δ ω}) := by
      simpa [M, mclose, e] using hmod
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hsum

/-- The family of step-path laws of an attracted walk is tight in the Skorokhod space. -/
theorem IsRealStableAttracted.isTightMeasureSet_stepPathLaw {ν : ProbabilityMeasure ℝ}
    {θ : ℝ} {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    IsTightMeasureSet
      (Set.range fun n => (stepPathLaw ν T B n : Measure (D T ℝ))) := by
  apply BGW.Skorokhod.isTightMeasureSet_of_cadlagModulus_eventually
    (fun n => (stepPathLaw ν T B n : Measure (D T ℝ)))
  · intro n
    exact isTightMeasureSet_stepPathLaw_singleton ν T B n
  · exact h.stepPath_bounded_eventually hT
  · exact h.stepPath_modulus_eventually hT

end BGW.StableTrees
