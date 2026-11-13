/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxCutoff
import BGW.StableTrees.SurvivalBasic

/-!
# Discrete height and occupation in two limits

The stopped band estimate, ladder-count tightness and the vanishing ceiling
error give the height approximation. Finite-time reversal restores forest heights.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

/-- Addition is compatible with upper limits of nonnegative extended-real sequences. -/
theorem limsup_add_le_ennreal {α : Type*} (f : Filter α) (u v : α → ℝ≥0∞) :
    limsup (fun i => u i + v i) f ≤ limsup u f + limsup v f := by
  rw [limsup_eq_iInf_iSup (u := u), limsup_eq_iInf_iSup (u := v),
    ENNReal.iInf₂_add]
  simp_rw [ENNReal.add_iInf₂]
  refine le_iInf₂ fun s hs => le_iInf₂ fun t ht => ?_
  refine limsup_le_of_le (by isBoundedDefault) ?_
  filter_upwards [hs, ht] with i hi hj
  exact add_le_add (le_iSup₂_of_le i hi le_rfl) (le_iSup₂_of_le i hj le_rfl)


/-- Applying finite-prefix reversal twice restores the sequence. -/
theorem revSeq_involutive (k : ℕ) : Function.Involutive (revSeq k) := by
  intro ω
  funext i
  unfold revSeq
  split_ifs <;> congr 1 <;> omega

/-- Every fixed finite reflected-band count is measurable. -/
theorem measurable_bandCount (k : ℕ) (a : ℝ) : Measurable (fun ω => bandCount ω k a) := by
  have he : (fun ω => bandCount ω k a) = fun ω => discreteCount (revSeq k ω) k a := by
    funext ω
    rw [discreteCount_eq_bandCount, revSeq_involutive k ω]
  rw [he]
  exact (measurable_discreteCount k a).comp (measurable_revSeq k)

private theorem eventual_occupation_error_bound {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) {x η ε : ℝ}
    (_hx : 0 < x) (hη : 0 < η) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      (offspringSeqLaw μ).toMeasure
        {ω | η < |(B n / (n : ℝ)) *
          (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) -
          (1 / ((n : ℝ) * ε)) *
            (bandCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ (ε * B n) : ℝ)|} ≤
      (offspringSeqLaw μ).toMeasure
        {ω | (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ x * (n : ℝ) / B n ∧
          (η / 2) * ((n : ℝ) * ε) <
            |(bandCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ (ε * B n) : ℝ) -
              (⌈ε * B n⌉₊ : ℝ) *
                (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)|} +
      (offspringSeqLaw μ).toMeasure
        {ω | x < (B n / (n : ℝ)) *
          (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)} := by
  have hbig := (Survival.tendsto_B_atTop h).eventually_gt_atTop (2 * x / (η * ε))
  filter_upwards [eventually_ge_atTop 1, hbig] with n hn hbn
  have hB := h.pos n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hne : 0 < (n : ℝ) * ε := mul_pos hnR hε
  have hεB := mul_pos hε hB
  have hround : x * (n : ℝ) / B n ≤ (η / 2) * ((n : ℝ) * ε) := by
    have hb := (div_lt_iff₀ (mul_pos hη hε)).mp hbn
    have hxB : x / B n ≤ η * ε / 2 := (div_le_iff₀ hB).mpr (by nlinarith only [hb])
    have hm := mul_le_mul_of_nonneg_right hxB hnR.le
    convert hm using 1 <;> ring
  refine (measure_mono ?_).trans (measure_union_le _ _)
  intro ω he
  by_cases hcut : (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) ≤ x * (n : ℝ) / B n
  · left
    refine ⟨hcut, ?_⟩
    by_contra hnot
    have herr := le_of_not_gt hnot
    let H : ℝ := weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊
    let C : ℝ := bandCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ (ε * B n)
    let m : ℝ := ⌈ε * B n⌉₊
    have hH : 0 ≤ H := Nat.cast_nonneg _
    have hmlo : ε * B n ≤ m := Nat.le_ceil _
    have hmhi : m ≤ ε * B n + 1 := (Nat.ceil_lt_add_one hεB.le).le
    have hrem : |(ε * B n - m) * H| ≤ (η / 2) * ((n : ℝ) * ε) := by
      have hneg : (ε * B n - m) * H ≤ 0 := mul_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr hmlo) hH
      rw [abs_of_nonpos hneg]
      have hm := mul_le_mul_of_nonneg_right hmhi hH
      change H ≤ x * (n : ℝ) / B n at hcut
      nlinarith only [hm, hcut, hround]
    have htotal : |ε * B n * H - C| ≤ η * ((n : ℝ) * ε) := by
      have habs := abs_add_le ((ε * B n - m) * H) (m * H - C)
      have heq : (ε * B n - m) * H + (m * H - C) = ε * B n * H - C := by ring
      rw [heq, abs_sub_comm (m * H) C] at habs
      change |C - m * H| ≤ (η / 2) * ((n : ℝ) * ε) at herr
      linarith only [habs, hrem, herr]
    have heq : (B n / (n : ℝ)) * H - (1 / ((n : ℝ) * ε)) * C =
        (ε * B n * H - C) / ((n : ℝ) * ε) := by field_simp
    change η < |(B n / (n : ℝ)) * H - (1 / ((n : ℝ) * ε)) * C| at he
    rw [heq, abs_div, abs_of_pos hne] at he
    have hh := (lt_div_iff₀ hne).mp he
    exact (not_lt_of_ge htotal) hh
  · right
    have hc := lt_of_not_ge hcut
    have he := (div_lt_iff₀ hB).mp hc
    change x < (B n / (n : ℝ)) *
      (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ)
    rw [show (B n / (n : ℝ)) *
      (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) =
      (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) * B n / (n : ℝ) by ring]
    exact (lt_div_iff₀ hnR).mpr he

private theorem band_occupation_error_twoLimit {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun ε : ℝ => limsup (fun n : ℕ => (offspringSeqLaw μ).toMeasure
      {ω | η < |(B n / (n : ℝ)) *
        (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) -
        (1 / ((n : ℝ) * ε)) *
          (bandCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ (ε * B n) : ℝ)|}) atTop)
      (𝓝[>] 0) (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro e he
  by_cases het : e = ∞
  · simp only [het, le_top, eventually_true]
  let q := e.toReal / 2
  have hq : 0 < q := div_pos (ENNReal.toReal_pos he.ne' het) (by norm_num)
  have htail := (weakLadderCount_tight_ascending h t).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr hq))
  obtain ⟨x, hx, hxt⟩ := ((eventually_gt_atTop 0).and htail).exists
  have hstop := (stopped_bandCount_error h t hx (show 0 < η / 2 by positivity)).eventually
    (gt_mem_nhds (ENNReal.ofReal_pos.mpr hq))
  filter_upwards [self_mem_nhdsWithin, hstop] with ε hε hs
  have hb := limsup_le_limsup (eventual_occupation_error_bound h t hx hη hε)
  refine (hb.trans (limsup_add_le_ennreal _ _ _)).trans ?_
  have hsum := add_le_add hs.le hxt.le
  refine hsum.trans_eq ?_
  rw [← ENNReal.ofReal_add hq.le hq.le]
  have hqq : q + q = e.toReal := by dsimp [q]; ring
  rw [hqq, ENNReal.ofReal_toReal het]

/-- **Two-limit estimate.**  For a stable domain `(μ, θ, B)`, a fixed `t` and `η > 0`:
`limsup_{ε↓0} limsup_n P(|(B_n/n) H_{⌊nt⌋} - discrete ε-occupation| > η) = 0`.
No renewal-error hypothesis; ties are weak records; `t = 0` is trivial. -/
theorem occupation_error_twoLimit {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (t : ℝ≥0) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun ε : ℝ =>
        limsup (fun n : ℕ => ((offspringSeqLaw μ : ProbabilityMeasure (ℕ → ℕ)) :
          Measure (ℕ → ℕ)) {ω | η < |scaledHeight B n ω t -
            discreteOccupation B n ε ω t|}) atTop)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have he (n : ℕ) (ε : ℝ) : (offspringSeqLaw μ).toMeasure
      {ω | η < |scaledHeight B n ω t - discreteOccupation B n ε ω t|} =
      (offspringSeqLaw μ).toMeasure
        {ω | η < |(B n / (n : ℝ)) *
          (weakLadderCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ : ℝ) -
          (1 / ((n : ℝ) * ε)) *
            (bandCount ω ⌊(n : ℝ) * (t : ℝ)⌋₊ (ε * B n) : ℝ)|} := by
    let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
    have hmB : Measurable (fun ω => (bandCount ω k (ε * B n) : ℝ)) :=
      (measurable_of_countable (fun j : ℕ => (j : ℝ))).comp (measurable_bandCount k (ε * B n))
    have hmH : Measurable (fun ω => (weakLadderCount ω k : ℝ)) :=
      (measurable_of_countable (fun j : ℕ => (j : ℝ))).comp (measurable_weakLadderCount k)
    have hm : MeasurableSet {ω | η < |(B n / (n : ℝ)) * (weakLadderCount ω k : ℝ) -
        (1 / ((n : ℝ) * ε)) * (bandCount ω k (ε * B n) : ℝ)|} :=
      measurableSet_lt measurable_const (by
        have hd : Measurable (fun ω => (B n / (n : ℝ)) * (weakLadderCount ω k : ℝ) -
            (1 / ((n : ℝ) * ε)) * (bandCount ω k (ε * B n) : ℝ)) :=
          (measurable_const.mul hmH).sub (measurable_const.mul hmB)
        simpa only [Real.norm_eq_abs] using hd.norm)
    have hmap := Measure.map_apply (μ := (offspringSeqLaw μ).toMeasure) (measurable_revSeq k) hm
    rw [map_revSeq_offspringSeqLaw] at hmap
    rw [hmap]
    congr 1
    ext ω
    simp only [k, Set.mem_preimage, Set.mem_ofPred_eq, scaledHeight, discreteOccupation,
      forestHeight_eq_weakLadderCount, discreteCount_eq_bandCount]
  simp_rw [he]
  exact band_occupation_error_twoLimit h t hη

end BGW.StableTrees.DiscreteHeightApprox
