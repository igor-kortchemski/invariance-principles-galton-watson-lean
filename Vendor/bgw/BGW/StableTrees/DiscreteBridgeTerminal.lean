/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridgeRN
public import BGW.StableTrees.DiscreteBridgeShortDensity
public import BGW.StableTrees.DiscreteBridgeReversal
import BGW.Skorokhod.MeasurableExtrema

/-!
# Terminal-window control for walk bridges

Reversing the bridge vector reduces terminal windows to initial windows. A single
prefix density bound and the unconditioned small-block maximal estimate control them.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.Skorokhod BGW.Probability.RealWalk

/-- The open exceedance event after a specified time on a càdlàg path. -/
def windowExceed {T : ℝ} (c r : ℝ) : Set (D T ℝ) :=
  {x | ∃ t : Set.Icc (0 : ℝ) T, c ≤ (t : ℝ) ∧ r < |x t|}

/-- Open window exceedances are measurable by a countable detecting family of times. -/
theorem measurableSet_windowExceed {T c r : ℝ} (hc0 : 0 ≤ c) (hcT : c ≤ T) :
    MeasurableSet (windowExceed (T := T) c r) := by
  let J : Set (Set.Icc (0 : ℝ) T) := Ici ⟨c, hc0, hcT⟩
  have hJ : J.OrdConnected := ordConnected_Ici
  obtain ⟨K, hKc, hK⟩ := exists_countable_detecting_times hJ
  let KT := {q : J // q ∈ K}
  let _ : Countable KT := hKc.to_subtype
  have heq : windowExceed (T := T) c r = ⋃ q : KT, {x | r < |x q.val.val|} := by
    ext x
    constructor
    · rintro ⟨t, ht, hx⟩
      have htJ : t ∈ J := ht
      obtain ⟨q, hq, hxq⟩ := hK ℝ x {z | r < |z|}
        (isOpen_lt continuous_const continuous_abs) ⟨t, htJ⟩ hx
      exact mem_iUnion.mpr ⟨⟨q, hq⟩, hxq⟩
    · intro hx
      obtain ⟨q, hq⟩ := mem_iUnion.mp hx
      exact ⟨q.val.val, q.val.property, hq⟩
  rw [heq]
  exact MeasurableSet.iUnion fun q => measurableSet_lt measurable_const
    (continuous_abs.measurable.comp (measurable_eval (E := ℝ) q.val.val))

private theorem vecPath_apply {B : ℕ → ℝ} {n : ℕ} (ω : Fin n → ℕ)
    (t : Set.Icc (0 : ℝ) 1) :
    vecPath B n ω t = (((stepWord ω).take ⌊(n : ℝ) * (t : ℝ)⌋₊).sum : ℝ) / B n := by
  change (((stepWord ω).take ⌊((stepWord ω).length : ℝ) * (t : ℝ)⌋₊).sum : ℝ) /
    B n = _
  rw [show (stepWord ω).length = n by simp [stepWord]]

private theorem terminal_window_reversed {B : ℕ → ℝ} {n : ℕ} (hn : 1 ≤ n)
    (hB : 0 < B n) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ) (hδhalf : 2 * δ ≤ 1)
    (hnδ : 1 ≤ δ * n) (hend : 1 / B n < ε / 4)
    {ω : Fin n → ℕ} (hω : ω ∈ countBridges n)
    (htail : vecPath B n ω ∈ windowExceed (1 - δ) (3 * ε / 4)) :
    BGW.Skorokhod.restrict (show 2 * δ ≤ 1 from hδhalf) (vecPath B n (reverseVec ω)) ∈
      windowExceed (T := 2 * δ) 0 (ε / 2) := by
  have _ := hε
  have _ := hδ
  obtain ⟨t, ht, hx⟩ := htail
  let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hk : k ≤ n := Nat.floor_le_of_le (mul_le_of_le_one_right hnR.le t.2.2)
  let j := n - k
  have hjR : (j : ℝ) ≤ 2 * δ * n := by
    have hf := Nat.lt_floor_add_one ((n : ℝ) * (t : ℝ))
    have hkn : (k : ℝ) ≤ n := by exact_mod_cast hk
    have hj : (j : ℝ) = n - k := Nat.cast_sub hk
    dsimp only [k] at hj hkn
    rw [hj]
    nlinarith
  let s : Set.Icc (0 : ℝ) (2 * δ) :=
    ⟨(j : ℝ) / n, div_nonneg (Nat.cast_nonneg _) hnR.le,
      (div_le_iff₀ hnR).mpr hjR⟩
  let s₁ : Set.Icc (0 : ℝ) 1 := ⟨s, s.2.1, s.2.2.trans hδhalf⟩
  have hsidx : ⌊(n : ℝ) * (s₁ : ℝ)⌋₊ = j := by
    change ⌊(n : ℝ) * ((j : ℝ) / n)⌋₊ = j
    rw [mul_div_cancel₀ _ hnR.ne', Nat.floor_natCast]
  have hw := (stepWord_mem_bridgeWords_iff ω).mpr hω
  have hvals : vecPath B n ω t + vecPath B n (reverseVec ω) s₁ = -1 / B n := by
    rw [vecPath_apply, vecPath_apply, hsidx]
    change (((stepWord ω).take k).sum : ℝ) / B n +
      (((stepWord (reverseVec ω)).take (n - k)).sum : ℝ) / B n = _
    rw [sum_take_stepWord_reverseVec ω hk, hw.2.2, Int.cast_sub, Int.cast_neg, Int.cast_one]
    ring
  have htri : |vecPath B n ω t| ≤ 1 / B n + |vecPath B n (reverseVec ω) s₁| := by
    have heq : vecPath B n ω t = -1 / B n - vecPath B n (reverseVec ω) s₁ := by
      linarith
    rw [heq]
    simpa [abs_div, abs_of_pos hB] using abs_sub_le (-1 / B n) 0
      (vecPath B n (reverseVec ω) s₁)
  refine ⟨s, s.2.1, ?_⟩
  change ε / 2 < |vecPath B n (reverseVec ω) s₁|
  linarith

/-- A terminal window is bounded by an initial window of the reversed bridge vector. -/
theorem walkBridgeLaw_terminal_le_prefix {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ}
    (hn : Admissible μ n) (hB : 0 < B n) {ε δ : ℝ} (hε : 0 < ε) (hδ : 0 < δ)
    (hδhalf : 2 * δ < 1) (hnδ : 1 ≤ δ * n) (hend : 1 / B n < ε / 4) :
    (walkBridgeLaw μ B n hn : Measure (D 1 ℝ))
        {x | ∃ t : Set.Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ ε ≤ |x t|} ≤
      (restrictLaw (⟨2 * δ, by positivity⟩ : ℝ≥0) (by exact_mod_cast hδhalf.le)
        (walkBridgeLaw μ B n hn)).toMeasure (windowExceed 0 (ε / 2)) := by
  have hn1 : 1 ≤ n := by
    by_contra hn1
    have : n = 0 := by omega
    subst n
    exact hn (by simp [LocallyFinite.sizeEvent_zero])
  have hc0 : 0 ≤ 1 - δ := by linarith
  have hc1 : 1 - δ ≤ 1 := by linarith
  have hterminal := measurableSet_windowExceed (r := 3 * ε / 4) hc0 hc1
  have hinitial := measurableSet_windowExceed (r := ε / 2) (c := 0) le_rfl
    (show (0 : ℝ) ≤ 2 * δ by positivity)
  let ν := (offspringVec μ n)[|countBridges n]
  let f := BGW.Skorokhod.restrict (E := ℝ) hδhalf.le ∘ vecPath B n
  have hf : Measurable f := (measurable_restrict _).comp (measurable_vecPath B n)
  have hsrc : (walkBridgeLaw μ B n hn : Measure (D 1 ℝ))
      (windowExceed (1 - δ) (3 * ε / 4)) =
      ν ((vecPath B n) ⁻¹' windowExceed (1 - δ) (3 * ε / 4)) := by
    change (conditionedVecOrJunk μ n (countBridges n) : Measure (Fin n → ℕ)).map
      (vecPath B n) _ = _
    rw [coe_conditionedVecOrJunk μ n _ (offspringVec_countBridges_ne_zero hn),
      Measure.map_apply (measurable_vecPath B n) hterminal]
  have htgt : (restrictLaw (⟨2 * δ, by positivity⟩ : ℝ≥0) (by exact_mod_cast hδhalf.le)
      (walkBridgeLaw μ B n hn)).toMeasure (windowExceed 0 (ε / 2)) =
      ν (f ⁻¹' windowExceed 0 (ε / 2)) := by
    change (((conditionedVecOrJunk μ n (countBridges n) : Measure (Fin n → ℕ)).map
      (vecPath B n)).map (BGW.Skorokhod.restrict hδhalf.le)) _ = _
    rw [Measure.map_map (measurable_restrict _) (measurable_vecPath B n),
      coe_conditionedVecOrJunk μ n _ (offspringVec_countBridges_ne_zero hn)]
    change (ν.map f) (windowExceed 0 (ε / 2)) = _
    exact Measure.map_apply hf hinitial
  calc
    _ ≤ (walkBridgeLaw μ B n hn : Measure (D 1 ℝ))
        (windowExceed (1 - δ) (3 * ε / 4)) := by
      apply measure_mono
      rintro x ⟨t, ht, hx⟩
      exact ⟨t, ht, by linarith⟩
    _ = _ := hsrc
    _ ≤ ν (reverseVec ⁻¹' (f ⁻¹' windowExceed 0 (ε / 2))) := by
      apply measure_mono_ae
      exact ae_cond_of_forall_mem (Set.to_countable _).measurableSet fun ω hω htail =>
        terminal_window_reversed hn1 hB hε hδ hδhalf.le hnδ hend hω htail
    _ = (ν.map reverseVec) (f ⁻¹' windowExceed 0 (ε / 2)) :=
      (Measure.map_apply (measurable_reverseVec n) (hf hinitial)).symm
    _ = ν (f ⁻¹' windowExceed 0 (ε / 2)) := by rw [map_reverseVec_cond_countBridges]
    _ = _ := htgt.symm

private theorem bridge_initial_le {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ}
    (hn : Admissible μ n) (hB : 0 < B n) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1)
    {C : ℝ} (hC : ∀ x : D (a : ℝ) ℝ, bridgePathDensity μ B n a x ≤ C) (r : ℝ) :
    (restrictLaw a ha.2.le (walkBridgeLaw μ B n hn) : Measure (D (a : ℝ) ℝ))
        (windowExceed 0 r) ≤
      ENNReal.ofReal C * ENNReal.ofReal
        (maxTail (realOffspringStepLaw μ) ⌊(n : ℝ) * a⌋₊ (r * B n)) := by
  have hA := measurableSet_windowExceed (T := (a : ℝ)) (r := r) le_rfl a.coe_nonneg
  have ha0 : 0 < (a : ℝ) := by exact_mod_cast ha.1
  rw [restrictLaw_walkBridgeLaw_eq_withDensity hn hB.ne' a ha, withDensity_apply _ hA]
  calc
    _ ≤ ∫⁻ x in windowExceed 0 r, ENNReal.ofReal C
        ∂(stepPathLaw (realOffspringStepLaw μ) (a : ℝ) B n : Measure (D (a : ℝ) ℝ)) :=
      lintegral_mono fun x => ENNReal.ofReal_le_ofReal (hC x)
    _ = ENNReal.ofReal C *
        (stepPathLaw (realOffspringStepLaw μ) (a : ℝ) B n : Measure (D (a : ℝ) ℝ))
          (windowExceed 0 r) := by simp
    _ ≤ _ := by
      apply mul_le_mul_right
      apply (measure_mono ?_).trans (stepPathLaw_not_mem_Icc_le _ ha0 B n hB r)
      rintro x ⟨t, _, ht⟩
      refine ⟨t, ?_⟩
      intro hxt
      exact not_le_of_gt ht (abs_le.mpr hxt)

/-- **Terminal window** (time reversal of the bridge increments, endpoint error `1/B n`):
the walk bridge is uniformly small near time `1`. -/
theorem walkBridgeLaw_terminal_small {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, Admissible μ (q k)) {ε η : ℝ} (hε : 0 < ε) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ ∀ᶠ k : ℕ in atTop,
      ((walkBridgeLaw μ B (q k) (hq k) : ProbabilityMeasure (D 1 ℝ)) : Measure (D 1 ℝ))
        {x | ∃ t : Set.Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ ε ≤ |x t|} ≤
          ENNReal.ofReal η := by
  obtain ⟨C, hCpos, hC⟩ := bridgePathDensity_short_le h
  obtain ⟨d, hd, N, hN⟩ := h.isRealStableAttracted.small_block_max
    (ε / 2) (by positivity) (η / C) (div_pos hη hCpos)
  let a : ℝ≥0 := ⟨min d (1 / 4), (lt_min hd (by norm_num)).le⟩
  have ha0 : 0 < a := by
    change 0 < min d (1 / 4)
    exact lt_min hd (by norm_num)
  have haQuarter : (a : ℝ) ≤ 1 / 4 := min_le_right _ _
  have had : (a : ℝ) ≤ d := min_le_left _ _
  have ha : a ∈ Ioo (0 : ℝ≥0) 1 :=
    ⟨ha0, by exact_mod_cast (show (a : ℝ) < 1 by linarith)⟩
  let δ : ℝ := (a : ℝ) / 2
  have hδ : 0 < δ := by dsimp [δ]; exact half_pos (by exact_mod_cast ha0)
  have haδ : 2 * δ = (a : ℝ) := by dsimp [δ]; ring
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  have hδhalf : 2 * δ < 1 := by rw [haδ]; linarith
  have hBtop := (Scalar.tendsto_atTop h).comp hqtop
  have hend : ∀ᶠ k in atTop, 1 / B (q k) < ε / 4 :=
    (hBtop.const_div_atTop (1 : ℝ)).eventually_lt_const (by positivity)
  have hqδ : ∀ᶠ k in atTop, 1 ≤ δ * q k :=
    ((tendsto_natCast_atTop_atTop.comp hqtop).const_mul_atTop hδ).eventually_ge_atTop 1
  refine ⟨δ, hδ, hδ1, ?_⟩
  filter_upwards [hqtop.eventually hC, hqtop.eventually (eventually_ge_atTop N),
    hqtop.eventually (eventually_ge_atTop 1), hend, hqδ] with k hkC hkN hk1 hkEnd hkδ
  have hB := h.pos (q k) hk1
  have htail := walkBridgeLaw_terminal_le_prefix (hq k) hB hε hδ hδhalf hkδ hkEnd
  have htail' : (walkBridgeLaw μ B (q k) (hq k) : Measure (D 1 ℝ))
      {x | ∃ t : Set.Icc (0 : ℝ) 1, 1 - δ ≤ (t : ℝ) ∧ ε ≤ |x t|} ≤
      (restrictLaw a ha.2.le (walkBridgeLaw μ B (q k) (hq k)) : Measure (D (a : ℝ) ℝ))
        (windowExceed 0 (ε / 2)) := by
    have hcut : (⟨2 * δ, by positivity⟩ : ℝ≥0) = a := Subtype.ext haδ
    have htransport (b c : ℝ≥0) (hb : b ≤ 1) (hc : c ≤ 1) (heq : b = c) :
        (restrictLaw b hb (walkBridgeLaw μ B (q k) (hq k))).toMeasure
            (windowExceed 0 (ε / 2)) =
          (restrictLaw c hc (walkBridgeLaw μ B (q k) (hq k))).toMeasure
            (windowExceed 0 (ε / 2)) := by
      subst c
      rfl
    exact htail.trans_eq (htransport _ _ _ _ hcut)
  have hsmall := hN (q k) hkN ⌊(q k : ℝ) * a⌋₊ (by
    have hf := Nat.floor_le (mul_nonneg (Nat.cast_nonneg (q k)) a.coe_nonneg)
    have hnR := Nat.cast_nonneg (α := ℝ) (q k)
    nlinarith [mul_le_mul_of_nonneg_right had hnR])
  refine htail'.trans ((bridge_initial_le (hq k) hB a ha
    (hkC (hq k) a ha0 (by linarith)) (ε / 2)).trans ?_)
  calc
    ENNReal.ofReal C * ENNReal.ofReal _ ≤ ENNReal.ofReal C * ENNReal.ofReal (η / C) :=
      mul_le_mul_right (ENNReal.ofReal_le_ofReal hsmall) _
    _ = ENNReal.ofReal η := by
      rw [← ENNReal.ofReal_mul hCpos.le, mul_div_cancel₀ η hCpos.ne']


end BGW.StableTrees.DiscreteBridge
