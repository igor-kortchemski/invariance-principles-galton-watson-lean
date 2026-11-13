/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ForestLocalLimitDefs
import BGW.StableTrees.StableKendall
import Mathlib.Probability.CDF

/-!
# Inclusive forest tails and passage-law convergence

The inclusive forest tail is the tail of the integer first passage time. Weak
convergence of the passage laws supplies tail convergence at positive levels.

Reference: J.-F. Le Gall, *Random trees and applications*, Probab. Surveys 2 (2005),
Section 1.
-/

@[expose] public section

open MeasureTheory Filter Set ProbabilityTheory
open scoped Topology ENNReal NNReal
open BGW.Probability.RealWalk

namespace BGW.StableTrees

private theorem extend_levels {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q ℓ : ℕ → ℕ} (hq : StrictMono q) {x : ℝ} (hx : 0 < x)
    (hscale : Tendsto (fun k => (ℓ k : ℝ) / B (q k)) atTop (𝓝 x)) :
    ∃ L : ℕ → ℕ, (∀ k, L (q k) = ℓ k) ∧
      Tendsto (fun n => (L n : ℝ) / B n) atTop (𝓝 x) := by
  classical
  let L : ℕ → ℕ := fun n => if hn : ∃ k, q k = n then ℓ hn.choose else ⌊x * B n⌋₊
  have hL (k : ℕ) : L (q k) = ℓ k := by
    dsimp only [L]
    split_ifs with hk
    · rw [hq.injective hk.choose_spec]
    · exact (hk ⟨k, rfl⟩).elim
  have hdefault : Tendsto (fun n => (⌊x * B n⌋₊ : ℝ) / B n) atTop (𝓝 x) := by
    have ht := tendsto_nat_floor_div_atTop.comp ((Scalar.tendsto_atTop h).const_mul_atTop hx)
    have ht' := ht.mul_const x
    rw [one_mul] at ht'
    refine ht'.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hB := (h.pos n hn).ne'
    dsimp only [Function.comp_apply]
    field_simp
  refine ⟨L, hL, Metric.tendsto_atTop.2 fun ε hε => ?_⟩
  obtain ⟨K, hK⟩ := Metric.tendsto_atTop.1 hscale ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 hdefault ε hε
  refine ⟨max N (q K), fun n hn => ?_⟩
  by_cases hnq : ∃ k, q k = n
  · obtain ⟨k, rfl⟩ := hnq
    rw [hL]
    exact hK k (hq.le_iff_le.1 ((le_max_right _ _).trans hn))
  · change dist ((if hn : ∃ k, q k = n then ℓ hn.choose else ⌊x * B n⌋₊ : ℕ) / B n) x < ε
    rw [dite_eq_right hnq]
    exact hN n ((le_max_left _ _).trans hn)

/-- An inclusive forest tail is the passage-time tail above the preceding integer. -/
theorem forestTail_eq_walkPassage_tail {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {ℓ r n : ℕ} (hℓ : 1 ≤ ℓ) (hr : 1 ≤ r) (hn : 1 ≤ n) :
    forestTail μ ℓ r = (walkPassageLaw μ ℓ n).real (Ioi ((r - 1 : ℕ) / (n : ℝ))) := by
  let P : Measure (ℕ → ℝ) := iidLaw (realOffspringStepLaw μ)
  let E : ℕ → Set (ℕ → ℝ) := fun k =>
    if r ≤ k then {w | walkHitTime ℓ w = (k : ℕ∞)} else ∅
  have hmeas : ∀ k, MeasurableSet (E k) := by
    intro k
    dsimp only [E]
    split_ifs
    · exact measurableSet_eq_fun (measurable_walkHitTime ℓ) measurable_const
    · exact MeasurableSet.empty
  have hdis : Pairwise (Function.onFun Disjoint E) := by
    intro i j hij
    dsimp only [E, Function.onFun]
    split_ifs <;> try simp
    apply Set.disjoint_left.2
    intro w hi hj
    exact hij (ENat.natCast_inj.1 (hi.symm.trans hj))
  have hH : Measurable (fun w : ℕ → ℝ => ((walkHitTime ℓ w).toNat : ℝ) / n) := by
    have ht : Measurable (fun w : ℕ → ℝ => (walkHitTime ℓ w).toNat) :=
      (measurable_of_countable ENat.toNat).comp (measurable_walkHitTime ℓ)
    exact ((show Measurable (fun k : ℕ => (k : ℝ)) from by fun_prop).comp ht).div_const n
  have heq : (fun w : ℕ → ℝ => ((walkHitTime ℓ w).toNat : ℝ) / n) ⁻¹'
      Ioi ((r - 1 : ℕ) / (n : ℝ)) =ᵐ[P] ⋃ k, E k := by
    filter_upwards [ae_walkHitTime_ne_top h ℓ] with w hw
    apply propext
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hcoe := ENat.natCast_toNat hw
    constructor
    · intro ht
      have ht' : r ≤ (walkHitTime ℓ w).toNat := by
        have ht' := (div_lt_div_iff_of_pos_right hnR).1 ht
        have ht'' : r - 1 < (walkHitTime ℓ w).toNat := by exact_mod_cast ht'
        omega
      exact mem_iUnion.2 ⟨_, by dsimp only [E]; rw [ite_eq_left ht']; exact hcoe.symm⟩
    · intro ht
      obtain ⟨k, hk⟩ := mem_iUnion.1 ht
      by_cases hrk : r ≤ k
      · dsimp only [E] at hk
        rw [ite_eq_left hrk] at hk
        change ((r - 1 : ℕ) : ℝ) / n < ((walkHitTime ℓ w).toNat : ℝ) / n
        rw [hk, ENat.toNat_natCast, div_lt_div_iff_of_pos_right hnR]
        exact_mod_cast (show r - 1 < k by omega)
      · simp [E, hrk] at hk
  rw [measureReal_def, walkPassageLaw, Measure.map_apply hH measurableSet_Ioi,
    measure_congr heq, measure_iUnion hdis hmeas,
    ENNReal.tsum_toReal_eq (fun _ => measure_ne_top P _)]
  unfold forestTail
  apply tsum_congr
  intro k
  by_cases hrk : r ≤ k
  · rw [Set.indicator_of_mem (show k ∈ Ici r from hrk)]
    change (BGW.forestWeight μ ℓ k).toReal =
      ((iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) (E k)).toReal
    dsimp only [E]
    rw [ite_eq_left hrk, walkHitTime_mass_eq_forestWeight μ hℓ]
  · simp [E, hrk]

private theorem cdf_fixed_of_tendsto {P : ℕ → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hPQ : Tendsto P atTop (𝓝 Q)) (c : ℝ) (hc : (Q : Measure ℝ) {c} = 0) :
    Tendsto (fun n => cdf (P n : Measure ℝ) c) atTop (𝓝 (cdf (Q : Measure ℝ) c)) := by
  have hfront : (Q : Measure ℝ) (frontier (Iic c)) = 0 :=
    measure_mono_null (frontier_Iic_subset c) hc
  have hm := ProbabilityMeasure.tendsto_measure_of_null_frontier_of_tendsto' hPQ hfront
  simpa only [cdf_eq_real, measureReal_def, Function.comp_def] using
    (ENNReal.tendsto_toReal (measure_ne_top (Q : Measure ℝ) (Iic c))).comp hm

private theorem continuousAt_cdf_of_noAtom {Q : Measure ℝ} [IsProbabilityMeasure Q] {c : ℝ}
    (hc : Q {c} = 0) : ContinuousAt (cdf Q) c := by
  have hm : Q {c} = ENNReal.ofReal (cdf Q c - Function.leftLim (cdf Q) c) := by
    calc
      Q {c} = (cdf Q).measure {c} :=
        congrArg (fun μ : Measure ℝ => μ {c}) (measure_cdf Q).symm
      _ = _ := StieltjesFunction.measure_singleton (cdf Q) c
  have hzero : ENNReal.ofReal (cdf Q c - Function.leftLim (cdf Q) c) = 0 := by
    rw [← hm, hc]
  have hle : cdf Q c - Function.leftLim (cdf Q) c ≤ 0 := ENNReal.ofReal_eq_zero.mp hzero
  have hleft : Function.leftLim (cdf Q) c = cdf Q c := by
    have hmono := Monotone.leftLim_le (monotone_cdf Q) (x := c) (y := c) le_rfl
    linarith
  exact (monotone_cdf Q).continuousAt_iff_leftLim_eq_rightLim.mpr
    (hleft.trans ((cdf Q).rightLim_eq c).symm)

private theorem tendsto_cdf_moving {P : ℕ → ProbabilityMeasure ℝ} {Q : ProbabilityMeasure ℝ}
    (hPQ : Tendsto P atTop (𝓝 Q)) {q : ℕ → ℝ} {c : ℝ}
    (hq : Tendsto q atTop (𝓝 c)) (hc : (Q : Measure ℝ) {c} = 0)
    (hfixed : ∀ z : ℝ, Tendsto (fun n => cdf (P n : Measure ℝ) z) atTop
      (𝓝 (cdf (Q : Measure ℝ) z))) :
    Tendsto (fun n => cdf (P n : Measure ℝ) (q n)) atTop (𝓝 (cdf (Q : Measure ℝ) c)) := by
  -- `hPQ` is part of the stated interface; this proof does not use it.
  have _hPQ := hPQ
  have hcont := continuousAt_cdf_of_noAtom (Q := (Q : Measure ℝ)) hc
  refine Metric.tendsto_atTop.2 ?_
  intro ε hε
  obtain ⟨δ, hδ, hδf⟩ := Metric.continuousAt_iff.mp hcont (ε / 2) (by positivity)
  let r := δ / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hdistlo : dist (c - r) c = r := by
    rw [Real.dist_eq, show c - r - c = -r by ring, abs_neg, abs_of_pos hr]
  have hdisthi : dist (c + r) c = r := by
    rw [Real.dist_eq, show c + r - c = r by ring, abs_of_pos hr]
  have hloDist := hδf (show dist (c - r) c < δ by
    rw [hdistlo]
    dsimp [r]
    linarith)
  have hhiDist := hδf (show dist (c + r) c < δ by
    rw [hdisthi]
    dsimp [r]
    linarith)
  rw [Real.dist_eq] at hloDist hhiDist
  have hloAbs := abs_lt.mp hloDist
  have hhiAbs := abs_lt.mp hhiDist
  have hloLim : cdf (Q : Measure ℝ) c - ε / 2 < cdf (Q : Measure ℝ) (c - r) := by
    linarith [hloAbs.1, hloAbs.2]
  have hhiLim : cdf (Q : Measure ℝ) (c + r) < cdf (Q : Measure ℝ) c + ε / 2 := by
    linarith [hhiAbs.1, hhiAbs.2]
  have hfinal : ∀ᶠ n in atTop, dist (cdf (P n : Measure ℝ) (q n))
      (cdf (Q : Measure ℝ) c) < ε := by
    filter_upwards [hq.eventually (Metric.ball_mem_nhds _ hr),
      (hfixed (c - r)).eventually (Ioi_mem_nhds hloLim),
      (hfixed (c + r)).eventually (Iio_mem_nhds hhiLim)] with n hn hnl hnu
    have habs : |q n - c| < r := by simpa only [Real.dist_eq] using hn
    have hqc := abs_lt.mp habs
    have hlower : c - r < q n := by linarith [hqc.1]
    have hupper : q n < c + r := by linarith [hqc.2]
    have hmono1 : cdf (P n : Measure ℝ) (c - r) ≤ cdf (P n : Measure ℝ) (q n) :=
      monotone_cdf _ hlower.le
    have hmono2 : cdf (P n : Measure ℝ) (q n) ≤ cdf (P n : Measure ℝ) (c + r) :=
      monotone_cdf _ hupper.le
    rw [Real.dist_eq, abs_lt]
    constructor <;> linarith
  exact Filter.eventually_atTop.1 hfinal

/-- Tail convergence along a strictly increasing time sequence and a convergent level sequence. -/
theorem forestTail_limit_seq {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {q ℓ r : ℕ → ℕ} (hq : StrictMono q)
    {x κ : ℝ} (hx : 0 < x) (hκ : 0 < κ)
    (hscale : Tendsto (fun k => (ℓ k : ℝ) / B (q k)) atTop (𝓝 x))
    (hratio : Tendsto (fun k => (r k : ℝ) / q k) atTop (𝓝 κ)) :
    Tendsto (fun k => forestTail μ (ℓ k) (r k)) atTop (𝓝 (sizeTailKernel θ κ x)) := by
  obtain ⟨L, hL, hLscale⟩ := extend_levels h hq hx hscale
  have hLpos : ∀ᶠ n in atTop, 1 ≤ L n := by
    filter_upwards [hLscale.eventually (lt_mem_nhds hx), eventually_ge_atTop 1] with n hn hn1
    have hpos : 0 < (L n : ℝ) := (div_pos_iff_of_pos_right (h.pos n hn1)).1 hn
    exact_mod_cast hpos
  let x' : ℝ≥0 := ⟨x, hx.le⟩
  let P : ℕ → ProbabilityMeasure ℝ := fun k =>
    ⟨walkPassageLaw μ (ℓ k) (q k), walkPassageLaw_isProbabilityMeasure h _ _⟩
  let Q : ProbabilityMeasure ℝ :=
    ⟨passageLaw θ x', passageLaw_isProbabilityMeasure h.alpha_mem x'⟩
  have hPQ : Tendsto P atTop (𝓝 Q) := by
    let Ps : ℕ → ProbabilityMeasure ℝ := fun n =>
      ⟨walkPassageLaw μ (L n) n, walkPassageLaw_isProbabilityMeasure h _ _⟩
    have ht : Tendsto Ps atTop (𝓝 Q) :=
      ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2
        (tendsto_walkPassageLaw h (show 0 < x' from hx) hLpos hLscale)
    have hteq : (fun k => Ps (q k)) = P := by
      funext k
      apply Subtype.ext
      exact congrArg (fun j => walkPassageLaw μ j (q k)) (hL k)
    simpa only [Function.comp_def, hteq] using ht.comp hq.tendsto_atTop
  have hno (c : ℝ) : (Q : Measure ℝ) {c} = 0 := by
    change passageLaw θ x' {c} = 0
    rw [passageLaw_eq_qKernel h.alpha_mem x' (show 0 < x' from hx),
      withDensity_apply _ (measurableSet_singleton c)]
    simp
  have hrpos : ∀ᶠ k in atTop, 1 ≤ r k := by
    filter_upwards [hratio.eventually (lt_mem_nhds hκ)] with k hk
    by_contra hn
    have hz : r k = 0 := by omega
    simp [hz] at hk
  have hthreshold : Tendsto (fun k => ((r k - 1 : ℕ) : ℝ) / q k) atTop (𝓝 κ) := by
    have ht := hratio.sub (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ) |>.comp
      hq.tendsto_atTop)
    rw [sub_zero] at ht
    refine ht.congr' ?_
    filter_upwards [hrpos] with k hk
    rw [Nat.cast_sub hk, Nat.cast_one, sub_div]
    rfl
  have hlim := tendsto_cdf_moving hPQ hthreshold (hno κ)
    (fun c => cdf_fixed_of_tendsto hPQ c (hno c))
  have htail (k : ℕ) (hk : 1 ≤ r k) (hqk : 1 ≤ q k) (hℓk : 1 ≤ ℓ k) :
      forestTail μ (ℓ k) (r k) = 1 - cdf (P k : Measure ℝ)
        (((r k - 1 : ℕ) : ℝ) / q k) := by
    rw [forestTail_eq_walkPassage_tail h hℓk hk hqk, cdf_eq_real]
    change (P k : Measure ℝ).real (Ioi _) = _
    rw [← compl_Iic, measureReal_compl measurableSet_Iic, probReal_univ]
  have hQtail : 1 - cdf (Q : Measure ℝ) κ = sizeTailKernel θ κ x := by
    rw [cdf_eq_real, ← probReal_univ (μ := (Q : Measure ℝ)),
      ← measureReal_compl measurableSet_Iic, compl_Iic]
    change (passageLaw θ x' (Ioi κ)).toReal = _
    rw [← sizeTailKernelENN_eq_passageLaw h.alpha_mem hκ.le x' (show 0 < x' from hx)]
    change (sizeTailKernelENN θ κ x).toReal = _
    rw [← ofReal_sizeTailKernel h.alpha_mem hκ.le hx,
      ENNReal.toReal_ofReal (sizeTailKernel_pos h.alpha_mem hκ hx).le]
  rw [← hQtail]
  refine (tendsto_const_nhds.sub hlim).congr' ?_
  filter_upwards [hrpos, hq.tendsto_atTop.eventually (eventually_ge_atTop 1),
    hq.tendsto_atTop.eventually hLpos] with k hk hqk hℓk
  rw [hL] at hℓk
  exact (htail k hk hqk hℓk).symm

/-- **Forest tail limit, compact-uniform, NO lattice condition.**  Uniformly for `r/n ∈ [a,b]`,
`j/B_n ∈ [ε,M]`: `G_j(r) - G_{r/n}(j/B_n) → 0` (`G = sizeTailKernel θ`). -/
theorem forestTailLimit_uniform {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {a b ε M : ℝ} (ha : 0 < a) (hab : a ≤ b) (hε : 0 < ε) (hεM : ε ≤ M) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop, ∀ r j : ℕ, a * (n : ℝ) ≤ r → (r : ℝ) ≤ b * n →
      ε ≤ (j : ℝ) / B n → (j : ℝ) / B n ≤ M →
      |forestTail μ j r - sizeTailKernel θ ((r : ℝ) / n) ((j : ℝ) / B n)| ≤ η := by
  -- `hab` and `hεM` are part of the stated interface; this proof does not use them.
  have _hab := hab
  have _hεM := hεM
  by_contra H
  rw [eventually_atTop] at H
  push Not at H
  choose q hq r ℓ hra hrb hℓε hℓM herr using fun n => H (n + 1)
  have hqpos (j : ℕ) : 1 ≤ q j := by have := hq j; omega
  have hqtop : Tendsto q atTop atTop := tendsto_atTop_mono
    (fun j => (Nat.le_succ j).trans (hq j)) tendsto_id
  obtain ⟨σ, hσ, hqσ⟩ := strictMono_subseq_of_tendsto_atTop hqtop
  have hrmem (j : ℕ) : (r (σ j) : ℝ) / q (σ j) ∈ Icc a b := by
    have hqR : 0 < (q (σ j) : ℝ) := by exact_mod_cast hqpos (σ j)
    exact ⟨(le_div_iff₀ hqR).2 (by simpa only [mul_comm] using hra (σ j)),
      (div_le_iff₀ hqR).2 (hrb (σ j))⟩
  have hℓmem (j : ℕ) : (ℓ (σ j) : ℝ) / B (q (σ j)) ∈ Icc ε M :=
    ⟨hℓε (σ j), hℓM (σ j)⟩
  obtain ⟨κ, hκ, φ, hφ, hκlim⟩ := isCompact_Icc.tendsto_subseq hrmem
  obtain ⟨x, hx, ψ, hψ, hxlim⟩ := isCompact_Icc.tendsto_subseq (fun j => hℓmem (φ j))
  have hκpos := ha.trans_le hκ.1
  have hxpos := hε.trans_le hx.1
  have hxlim' : Tendsto (fun j => (ℓ (σ (φ (ψ j))) : ℝ) /
      B (q (σ (φ (ψ j))))) atTop (𝓝 x) := by
    simpa only [Function.comp_def] using hxlim
  have hκlim' : Tendsto (fun j => (r (σ (φ (ψ j))) : ℝ) /
      q (σ (φ (ψ j)))) atTop (𝓝 κ) := by
    simpa only [Function.comp_def] using hκlim.comp hψ.tendsto_atTop
  have hseq := forestTail_limit_seq h (hqσ.comp (hφ.comp hψ)) hxpos hκpos hxlim' hκlim'
  have hcont : ContinuousAt (fun z : ℝ × ℝ => sizeTailKernel θ z.1 z.2) (κ, x) :=
    (continuousOn_sizeTailKernel h.alpha_mem).continuousAt
      ((isOpen_Ioi.preimage continuous_fst).inter (isOpen_Ioi.preimage continuous_snd)
        |>.mem_nhds ⟨hκpos, hxpos⟩)
  have hker := hcont.tendsto.comp (hκlim'.prodMk_nhds hxlim')
  have hlim := hseq.sub hker
  rw [sub_self] at hlim
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 hlim η hη
  have hsmall := hJ J le_rfl
  rw [Real.dist_eq, sub_zero] at hsmall
  exact (not_lt_of_ge (herr (σ (φ (ψ J)))).le) hsmall

end BGW.StableTrees
