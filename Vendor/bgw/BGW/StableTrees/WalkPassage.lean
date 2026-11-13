/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.WalkPassageLimit
import BGW.Probability.SkorokhodRepresentationReal
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.Probability.CDF

/-!
# Weak convergence of walk first-passage times

The functional central limit theorem is mapped through the J1-continuous running
infimum.  Moving levels are handled by CDF convergence and atom-freeness.  A real
quantile coupling then converts the CDF limit into convergence of all bounded
continuous integrals
(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VII;
P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley, 1999, Section 13).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Topology
open BGW.Skorokhod BGW.StableTrees BGW.Probability.RealWalk

namespace BGW.StableTrees

private noncomputable def infimumPath {T : ℝ} (g : D T ℝ) : ℝ := ⨅ s, g s

private noncomputable def stepInfLaw (ν : ProbabilityMeasure ℝ) (T : ℝ) (B : ℕ → ℝ) (n : ℕ) :
    ProbabilityMeasure ℝ := (stepPathLaw ν T B n).map infimumPath

private noncomputable def stableInfLaw (θ T : ℝ) : ProbabilityMeasure ℝ :=
  (stableProcessLaw θ T).map infimumPath

private theorem measurable_infimumPath {T : ℝ} (hT : 0 ≤ T) : Measurable (infimumPath (T := T)) :=
  (lipschitzWith_one_iInf hT).continuous.measurable

private theorem measurable_scaledWalkHit (ℓ n : ℕ) :
    Measurable (fun w : ℕ → ℝ => ((walkHitTime ℓ w).toNat : ℝ) / n) := by
  have htoNat : Measurable (fun w : ℕ → ℝ => (walkHitTime ℓ w).toNat) :=
    (measurable_of_countable ENat.toNat).comp (measurable_walkHitTime ℓ)
  exact (((by fun_prop : Measurable (fun k : ℕ => (k : ℝ))).comp htoNat).div_const n)

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

private theorem walkHit_Iic_of_noTop {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} {ℓ n : ℕ}
    {w : ℕ → ℝ} {t : ℝ} (h : StableDomain μ θ B) (hn : 1 ≤ n) (ht : 0 ≤ t)
    (hw : walkHitTime ℓ w ≠ ⊤) :
    (((walkHitTime ℓ w).toNat : ℝ) / n ≤ t) ↔
      walkHitTime ℓ w ≤ ((⌊(n : ℝ) * t⌋₊ : ℕ) : ℕ∞) := by
  -- `h` is part of the stated interface; this proof does not use it.
  have _h := h
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnt : 0 ≤ (n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) ht
  have hcoe : ((walkHitTime ℓ w).toNat : ℕ∞) = walkHitTime ℓ w := ENat.natCast_toNat hw
  constructor
  · intro htime
    have hreal : ((walkHitTime ℓ w).toNat : ℝ) ≤ (n : ℝ) * t := by
      have hh := (div_le_iff₀ hnreal).mp htime
      nlinarith
    have hnat : (walkHitTime ℓ w).toNat ≤ ⌊(n : ℝ) * t⌋₊ := Nat.le_floor hreal
    rw [← hcoe]
    exact_mod_cast hnat
  · intro hhit
    apply (div_le_iff₀ hnreal).mpr
    have hreal : ((walkHitTime ℓ w).toNat : ℝ) ≤ (⌊(n : ℝ) * t⌋₊ : ℝ) := by
      rw [← hcoe] at hhit
      exact_mod_cast hhit
    have hle := hreal.trans (Nat.floor_le hnt)
    nlinarith

private theorem walkPassageLaw_eq_stepInfLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (ℓ n : ℕ) (hn : 1 ≤ n) {t : ℝ} (ht : 0 < t) :
    walkPassageLaw μ ℓ n (Iic t) =
      ((stepInfLaw (realOffspringStepLaw μ) t B n : ProbabilityMeasure ℝ) : Measure ℝ)
        (Iic (-(ℓ : ℝ) / B n)) := by
  have hB : 0 < B n := h.pos n hn
  let H : (ℕ → ℝ) → ℝ := fun w => ((walkHitTime ℓ w).toNat : ℝ) / n
  let A : Set (ℕ → ℝ) := {w | H w ≤ t}
  let C : Set (ℕ → ℝ) := {w | walkHitTime ℓ w ≤ ((⌊(n : ℝ) * t⌋₊ : ℕ) : ℕ∞)}
  let E : Set (ℕ → ℝ) := {w |
    (⨅ s : Set.Icc (0 : ℝ) t, realStepPath t n (B n) w s) ≤ -(ℓ : ℝ) / B n}
  have hAC : A =ᵐ[(iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ))] C := by
    filter_upwards [ae_walkHitTime_ne_top h ℓ] with w hw
    apply propext
    exact walkHit_Iic_of_noTop h hn ht.le hw
  have hCE : C = E := by
    ext w
    exact walkHitTime_le_iff_iInf_stepPath_le ht.le hB w
  calc
    walkPassageLaw μ ℓ n (Iic t) =
        (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) A := by
      rw [walkPassageLaw]
      exact Measure.map_apply (measurable_scaledWalkHit ℓ n) measurableSet_Iic
    _ = (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) C := measure_congr hAC
    _ = (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) E := by rw [hCE]
    _ = ((stepPathLaw (realOffspringStepLaw μ) t B n : ProbabilityMeasure (D t ℝ)) :
        Measure (D t ℝ)) {g | infimumPath g ≤ -(ℓ : ℝ) / B n} := by
      rw [coe_stepPathLaw]
      exact (Measure.map_apply (measurable_realStepPath t n (B n))
        (measurableSet_le (measurable_infimumPath ht.le) measurable_const)).symm
    _ = ((stepInfLaw (realOffspringStepLaw μ) t B n : ProbabilityMeasure ℝ) : Measure ℝ)
        (Iic (-(ℓ : ℝ) / B n)) := by
      exact (Measure.map_apply (measurable_infimumPath ht.le) measurableSet_Iic).symm

private theorem walkPassageLaw_Iic_zero_eventually {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {ℓ : ℕ → ℕ} (hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n) :
    ∀ᶠ n in atTop, walkPassageLaw μ (ℓ n) n (Iic 0) = 0 := by
  filter_upwards [hℓ, eventually_ge_atTop 1] with n hnℓ hn
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  rw [walkPassageLaw, Measure.map_apply (measurable_scaledWalkHit (ℓ n) n) measurableSet_Iic]
  rw [show (fun w : ℕ → ℝ => ((walkHitTime (ℓ n) w).toNat : ℝ) / n) ⁻¹' Iic 0 =
      {w | ¬ 0 < ((walkHitTime (ℓ n) w).toNat : ℝ) / n} by
    ext w
    simp only [Set.mem_preimage, mem_Iic, Set.mem_ofPred_eq, not_lt], ← ae_iff]
  filter_upwards [ae_walkHitTime_ne_top h (ℓ n), ae_partialSum_walkHitTime (ℓ n)] with w hw hexact
  by_contra htime
  have htime : ((walkHitTime (ℓ n) w).toNat : ℝ) / n ≤ 0 := le_of_not_gt htime
  have hnonneg : (0 : ℝ) ≤ ((walkHitTime (ℓ n) w).toNat : ℝ) / n :=
    div_nonneg (Nat.cast_nonneg _) hnreal.le
  have hzero : ((walkHitTime (ℓ n) w).toNat : ℝ) / n = 0 := le_antisymm htime hnonneg
  have hnum : ((walkHitTime (ℓ n) w).toNat : ℝ) = 0 := by
    have hd := (div_eq_zero_iff).mp hzero
    rcases hd with hd | hd
    · exact hd
    · exact (hnreal.ne' hd).elim
  have hnat : (walkHitTime (ℓ n) w).toNat = 0 := by exact_mod_cast hnum
  have hcases := ENat.toNat_eq_zero.mp hnat
  rcases hcases with hzeroHit | htop
  · have hexact0 := hexact 0 hzeroHit
    have hzeroSum : (0 : ℝ) ≤ -(ℓ n : ℝ) := by simpa [partialSum] using hexact0.le
    have hpos : (0 : ℝ) < ℓ n := by exact_mod_cast hnℓ
    linarith
  · exact (hw htop).elim

private theorem map_runningInf_stableInfLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    (stableLocalLaw θ : Measure DLoc).map (fun f => runningInfLoc f t) =
      ((stableInfLaw θ (t : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ) := by
  rw [stableInfLaw, ProbabilityMeasure.toMeasure_map, ← map_restrict_stableLocalLaw hθ ht]
  have heq : (fun f : DLoc => runningInfLoc f t) = infimumPath ∘ DLoc.restrict t := by
    funext f
    exact (iInf_restrict_stablePath f t).symm
  exact (congrArg (fun g => (stableLocalLaw θ : Measure DLoc).map g) heq).trans
    (Measure.map_map (measurable_infimumPath t.2) (DLoc.measurable_restrict t)).symm

private theorem cdf_passage_eq_stableInf {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    {t : ℝ≥0} (ht : 0 < t) :
    cdf (passageLaw θ x) (t : ℝ) = cdf (stableInfLaw θ (t : ℝ) : Measure ℝ) (-(x : ℝ)) := by
  let _ : IsProbabilityMeasure (passageLaw θ x) := passageLaw_isProbabilityMeasure hθ x
  rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def]
  change (passageLaw θ x (Iic (t : ℝ))).toReal =
    (((stableInfLaw θ (t : ℝ) : ProbabilityMeasure ℝ) : Measure ℝ) (Iic (-(x : ℝ)))).toReal
  calc
    (passageLaw θ x (Iic (t : ℝ))).toReal =
        ((stableLocalLaw θ : Measure DLoc) {f | runningInfLoc f t ≤ -(x : ℝ)}).toReal :=
      congrArg ENNReal.toReal (passageLaw_Iic_eq_runningInf hθ x ht).1
    _ = ((stableLocalLaw θ : Measure DLoc).map (fun f => runningInfLoc f t)
        (Iic (-(x : ℝ)))).toReal := by
      exact (congrArg ENNReal.toReal (Measure.map_apply
        (measurable_runningInfLoc_uncurry.comp (measurable_const.prodMk measurable_id))
        measurableSet_Iic)).symm
    _ = _ := by rw [map_runningInf_stableInfLaw hθ ht]

private theorem cdf_walkPassage_tendsto_of_pos {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {x : ℝ≥0} {ℓ : ℕ → ℕ}
    (hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 (x : ℝ)))
    {t : ℝ} (ht : 0 < t) :
    Tendsto (fun n => cdf (walkPassageLaw μ (ℓ n) n) t) atTop
      (𝓝 (cdf (passageLaw θ x) t)) := by
  have hlim : Tendsto (fun n => stepInfLaw (realOffspringStepLaw μ) t B n) atTop
      (𝓝 (stableInfLaw θ t)) := by
    have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => stepPathLaw (realOffspringStepLaw μ) t B n) (stableProcessLaw θ t)
      (h.tendsto_stepPathLaw ht) (lipschitzWith_one_iInf ht.le).continuous
    change Tendsto (fun n => (stepPathLaw (realOffspringStepLaw μ) t B n).map
      (fun g => ⨅ s, g s)) atTop (𝓝 ((stableProcessLaw θ t).map (fun g => ⨅ s, g s))) at hm
    exact hm
  have hno (c : ℝ) : ((stableInfLaw θ t : ProbabilityMeasure ℝ) : Measure ℝ) {c} = 0 := by
    rw [stableInfLaw, ProbabilityMeasure.toMeasure_map,
      Measure.map_apply (measurable_infimumPath ht.le) (measurableSet_singleton c)]
    exact iInf_noAtoms_stableProcessLaw h.alpha_mem ht c
  have hq : Tendsto (fun n : ℕ => -(ℓ n : ℝ) / B n) atTop (𝓝 (-(x : ℝ))) := by
    convert hscale.neg using 1
    · funext n
      ring
  have hmoving := tendsto_cdf_moving hlim hq (hno (-(x : ℝ)))
    (fun c => cdf_fixed_of_tendsto hlim c (hno c))
  have heq : ∀ᶠ n in atTop, cdf (walkPassageLaw μ (ℓ n) n) t =
      cdf ((stepInfLaw (realOffspringStepLaw μ) t B n : ProbabilityMeasure ℝ) : Measure ℝ)
        (-(ℓ n : ℝ) / B n) := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    let _ : IsProbabilityMeasure (walkPassageLaw μ (ℓ n) n) :=
      walkPassageLaw_isProbabilityMeasure h (ℓ n) n
    rw [cdf_eq_real, cdf_eq_real, measureReal_def, measureReal_def,
      walkPassageLaw_eq_stepInfLaw h (ℓ n) n hn ht]
  have hwalk := Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) hmoving
  have hpass := cdf_passage_eq_stableInf h.alpha_mem x (Real.toNNReal_pos.mpr ht)
  rw [Real.coe_toNNReal t ht.le] at hpass
  rw [hpass]
  exact hwalk

/-- **Walk first passage converges to the stable passage law.**
For a `StableDomain μ θ B` witness, integers
`ℓ n ≥ 1` eventually, and `ℓ n / B n → x > 0`: `walkHitTime (ℓ n) / n ⟹ T_x` in law. Stated for
bounded continuous test functions on `ℝ` (all measures involved are probability measures). -/
theorem tendsto_walkPassageLaw {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {x : ℝ≥0} (hx : 0 < x) {ℓ : ℕ → ℕ} (hℓ : ∀ᶠ n in atTop, 1 ≤ ℓ n)
    (hscale : Tendsto (fun n : ℕ => (ℓ n : ℝ) / B n) atTop (𝓝 (x : ℝ))) :
    ∀ f : BoundedContinuousFunction ℝ ℝ,
      Tendsto (fun n : ℕ => ∫ t, f t ∂(walkPassageLaw μ (ℓ n) n)) atTop
        (𝓝 (∫ t, f t ∂(passageLaw θ x))) := by
  intro f
  let P : ℕ → ProbabilityMeasure ℝ := fun n =>
    ⟨walkPassageLaw μ (ℓ n) n, walkPassageLaw_isProbabilityMeasure h (ℓ n) n⟩
  let Q : ProbabilityMeasure ℝ := ⟨passageLaw θ x, passageLaw_isProbabilityMeasure h.alpha_mem x⟩
  have hzero := walkPassageLaw_Iic_zero_eventually h hℓ
  have hcdf (t : ℝ) : Tendsto (fun n => cdf (P n : Measure ℝ) t) atTop
      (𝓝 (cdf (Q : Measure ℝ) t)) := by
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · have hQzero : passageLaw θ x (Iic t) = 0 :=
        measure_mono_null (Iic_subset_Iic.mpr ht.le) (passageLaw_Iic_zero h.alpha_mem hx)
      have heq : ∀ᶠ n in atTop, cdf (P n : Measure ℝ) t = 0 := by
        filter_upwards [hzero] with n hn
        rw [cdf_eq_real, measureReal_def]
        have hnull : walkPassageLaw μ (ℓ n) n (Iic t) = 0 :=
          measure_mono_null (Iic_subset_Iic.mpr ht.le) hn
        change (walkPassageLaw μ (ℓ n) n (Iic t)).toReal = 0
        rw [hnull]
        rfl
      have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
      have hlim := Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) hconst
      have hQreal : cdf (Q : Measure ℝ) t = 0 := by
        change cdf (passageLaw θ x) t = 0
        let _ : IsProbabilityMeasure (passageLaw θ x) :=
          passageLaw_isProbabilityMeasure h.alpha_mem x
        rw [cdf_eq_real, measureReal_def, hQzero]
        rfl
      rw [hQreal]
      exact hlim
    · have heq : ∀ᶠ n in atTop, cdf (P n : Measure ℝ) 0 = 0 := by
        filter_upwards [hzero] with n hn
        rw [cdf_eq_real, measureReal_def]
        change (walkPassageLaw μ (ℓ n) n (Iic 0)).toReal = 0
        rw [hn]
        rfl
      have hconst : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
      have hlim := Filter.Tendsto.congr' (Filter.EventuallyEq.symm heq) hconst
      have hQzero : cdf (Q : Measure ℝ) 0 = 0 := by
        change cdf (passageLaw θ x) 0 = 0
        let _ : IsProbabilityMeasure (passageLaw θ x) :=
          passageLaw_isProbabilityMeasure h.alpha_mem x
        rw [cdf_eq_real, measureReal_def, passageLaw_Iic_zero h.alpha_mem hx]
        rfl
      rw [hQzero]
      exact hlim
    · exact cdf_walkPassage_tendsto_of_pos h hscale ht
  obtain ⟨X, Y, hX, hY, hYlaw, hXY⟩ :=
    BGW.Probability.RealCoupling.exists_measurable_real_coupling
      (fun n => (P n : Measure ℝ)) (Q : Measure ℝ) dense_univ (fun t _ => hcdf t)
  have hlim : Tendsto (fun n => ∫ u, f (X n u) ∂BGW.Probability.RealCoupling.unitProbability)
      atTop (𝓝 (∫ u, f (Y u) ∂BGW.Probability.RealCoupling.unitProbability)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => ‖f‖)
    · intro n
      exact (f.continuous.measurable.comp (hX n).1).aestronglyMeasurable
    · exact integrable_const _
    · intro n
      exact Eventually.of_forall fun u => f.norm_coe_le_norm (X n u)
    · filter_upwards [hXY] with u hu
      exact f.continuous.continuousAt.tendsto.comp hu
  have heq (n : ℕ) : ∫ u, f (X n u) ∂BGW.Probability.RealCoupling.unitProbability =
      ∫ t, f t ∂walkPassageLaw μ (ℓ n) n := by
    calc
      _ = ∫ t, f t ∂(BGW.Probability.RealCoupling.unitProbability.map (X n)) :=
        (integral_map (hX n).1.aemeasurable f.continuous.aestronglyMeasurable).symm
      _ = ∫ t, f t ∂(P n : Measure ℝ) := by rw [(hX n).2]
      _ = _ := rfl
  have heqY : ∫ u, f (Y u) ∂BGW.Probability.RealCoupling.unitProbability =
      ∫ t, f t ∂passageLaw θ x := by
    calc
      _ = ∫ t, f t ∂(BGW.Probability.RealCoupling.unitProbability.map Y) :=
        (integral_map hY.aemeasurable f.continuous.aestronglyMeasurable).symm
      _ = ∫ t, f t ∂(Q : Measure ℝ) := by rw [hYlaw]
      _ = _ := rfl
  simpa only [heq, heqY] using hlim

end BGW.StableTrees
