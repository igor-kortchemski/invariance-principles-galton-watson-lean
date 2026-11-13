/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.Attraction.StableDomainTail
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # An explicit regularly varying offspring law for every stable index

The witness has a Pareto tail `μ[j,∞) = j^{-θ} / ζ(θ)`; it lies in the stable domain by the ported
tail criterion (Feller, vol. II, XVII.5).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal

namespace BGW.StableTrees

private noncomputable def paretoTail (θ : ℝ) (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (-θ)

private noncomputable def paretoDiff (θ : ℝ) (n : ℕ) : ℝ :=
  paretoTail θ n - paretoTail θ (n + 1)

private theorem paretoTail_summable {θ : ℝ} (hθ : 1 < θ) :
    Summable (paretoTail θ) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-θ)) := by
    apply Real.summable_nat_rpow.mpr
    linarith
  have hs := (summable_nat_add_iff (f := fun n : ℕ => (n : ℝ) ^ (-θ)) 1).2 h
  exact hs.congr fun n => by simp [paretoTail, Nat.cast_add]

private theorem paretoTail_nonneg (θ : ℝ) (n : ℕ) : 0 ≤ paretoTail θ n := by
  exact (Real.rpow_pos_of_pos (by positivity) _).le

private theorem paretoTail_antitone {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    paretoTail θ (n + 1) ≤ paretoTail θ n := by
  apply Real.rpow_le_rpow_of_nonpos (by positivity) ?_ (by linarith)
  norm_num [paretoTail]

private theorem paretoDiff_nonneg {θ : ℝ} (hθ : 0 < θ) (n : ℕ) :
    0 ≤ paretoDiff θ n := by
  exact sub_nonneg.mpr (paretoTail_antitone hθ n)

private theorem paretoDiff_summable {θ : ℝ} (hθ : 1 < θ) :
    Summable (paretoDiff θ) := by
  have h := paretoTail_summable hθ
  have hshift : Summable (fun n : ℕ => paretoTail θ (n + 1)) :=
    (summable_nat_add_iff (f := paretoTail θ) 1).2 h
  exact h.sub hshift

private theorem paretoDiff_tsum {θ : ℝ} (hθ : 1 < θ) :
    ∑' n, paretoDiff θ n = 1 := by
  have h := paretoTail_summable hθ
  have hshift : Summable (fun n : ℕ => paretoTail θ (n + 1)) :=
    (summable_nat_add_iff (f := paretoTail θ) 1).2 h
  have hsum := h.sum_add_tsum_nat_add 1
  have hhead : ∑ n ∈ Finset.range 1, paretoTail θ n = 1 := by
    simp [paretoTail]
  have htail : ∑' n, paretoTail θ (n + 1) = ∑' n, paretoTail θ n - 1 := by
    rw [← hhead]
    linarith
  rw [show paretoDiff θ = fun n => paretoTail θ n - paretoTail θ (n + 1) by rfl,
    Summable.tsum_sub h hshift, htail]
  simp

private theorem paretoWeightedDiff_sum_range (θ : ℝ) (N : ℕ) :
    (∑ n ∈ Finset.range N, (((n : ℝ) + 1) * paretoDiff θ n)) =
      (∑ n ∈ Finset.range N, paretoTail θ n) - (N : ℝ) * paretoTail θ N := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      rw [ih]
      dsimp [paretoDiff]
      push_cast
      ring

private theorem paretoBoundary_tendsto {θ : ℝ} (hθ : 1 < θ) :
    Tendsto (fun n : ℕ => (n : ℝ) * paretoTail θ n) atTop (𝓝 0) := by
  have hpow : Tendsto (fun n : ℕ => ((n : ℝ) + 1) ^ (-(θ - 1))) atTop (𝓝 0) := by
    exact (tendsto_rpow_neg_atTop (sub_pos.mpr hθ)).comp
      (tendsto_atTop_mono (fun n : ℕ => le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1))
        tendsto_natCast_atTop_atTop)
  have hmul : ∀ᶠ n : ℕ in atTop, 0 ≤ (n : ℝ) * paretoTail θ n :=
    Eventually.of_forall fun n => mul_nonneg (by positivity) (paretoTail_nonneg _ _)
  have hbound : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) * paretoTail θ n ≤ ((n : ℝ) + 1) ^ (-(θ - 1)) :=
    Eventually.of_forall fun n => by
      have hn : (n : ℝ) ≤ (n : ℝ) + 1 :=
        le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)
      have hb : 0 < (n : ℝ) + 1 := by positivity
      calc
        (n : ℝ) * paretoTail θ n ≤ ((n : ℝ) + 1) * paretoTail θ n :=
          mul_le_mul_of_nonneg_right hn (paretoTail_nonneg _ _)
        _ = ((n : ℝ) + 1) ^ (-(θ - 1)) := by
          rw [paretoTail, show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num]
          calc
            _ = ((n : ℝ) + 1) ^ 1 * ((n : ℝ) + 1) ^ (-θ) := by rw [Real.rpow_one]
            _ = ((n : ℝ) + 1) ^ (1 + -θ) := (Real.rpow_add hb _ _).symm
            _ = ((n : ℝ) + 1) ^ (-(θ - 1)) := by congr 1; ring
  exact squeeze_zero' hmul hbound hpow

private theorem paretoWeightedDiff_hasSum {θ : ℝ} (hθ : 1 < θ) :
    HasSum (fun n : ℕ => ((n : ℝ) + 1) * paretoDiff θ n)
      (∑' n : ℕ, paretoTail θ n) := by
  have htail := paretoTail_summable hθ
  have hboundary := paretoBoundary_tendsto hθ
  have hpartial : Tendsto (fun N : ℕ =>
      ∑ n ∈ Finset.range N, (((n : ℝ) + 1) * paretoDiff θ n)) atTop
      (𝓝 (∑' n : ℕ, paretoTail θ n)) := by
    have hsum := htail.hasSum.tendsto_sum_nat
    have hsub := hsum.sub hboundary
    convert hsub using 1
    · exact funext fun N => paretoWeightedDiff_sum_range θ N
    · simp
  have hnn : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) * paretoDiff θ n := by
    intro n
    exact mul_nonneg (by positivity) (paretoDiff_nonneg (by linarith) n)
  exact (hasSum_iff_tendsto_nat_of_nonneg hnn _).2 hpartial

private theorem paretoWeightedDiff_tsum {θ : ℝ} (hθ : 1 < θ) :
    ∑' n : ℕ, (((n : ℝ) + 1) * paretoDiff θ n) = ∑' n : ℕ, paretoTail θ n := by
  exact (paretoWeightedDiff_hasSum hθ).tsum_eq

private noncomputable def paretoZ (θ : ℝ) : ℝ := ∑' n : ℕ, paretoTail θ n

private theorem paretoZ_ge_one {θ : ℝ} (hθ : 1 < θ) : 1 ≤ paretoZ θ := by
  have hs := paretoTail_summable hθ
  have hsum := hs.sum_add_tsum_nat_add 1
  have hhead : ∑ n ∈ Finset.range 1, paretoTail θ n = 1 := by simp [paretoTail]
  have hrest : 0 ≤ ∑' n, paretoTail θ (n + 1) := tsum_nonneg fun n => paretoTail_nonneg θ _
  dsimp [paretoZ]
  rw [hhead] at hsum
  linarith

private theorem paretoZ_gt_one {θ : ℝ} (hθ : 1 < θ) : 1 < paretoZ θ := by
  have hs := paretoTail_summable hθ
  have hsum := hs.sum_add_tsum_nat_add 2
  have hhead : ∑ n ∈ Finset.range 2, paretoTail θ n = 1 + paretoTail θ 1 := by
    norm_num [paretoTail, Finset.sum_range_succ, Real.one_rpow]
  have hrest : 0 ≤ ∑' n, paretoTail θ (n + 2) :=
    tsum_nonneg fun n => paretoTail_nonneg θ _
  dsimp [paretoZ]
  rw [hhead] at hsum
  have hu : 0 < paretoTail θ 1 := Real.rpow_pos_of_pos (by positivity) _
  linarith

private noncomputable def paretoRaw (θ : ℝ) : ℕ → ℝ≥0∞ := fun n =>
  match n with
  | 0 => ENNReal.ofReal (paretoZ θ - 1)
  | n + 1 => ENNReal.ofReal (paretoDiff θ n)

private def natSuccEquiv : ℕ ≃ {n : ℕ // n ≠ 0} where
  toFun n := ⟨n + 1, Nat.succ_ne_zero _⟩
  invFun n := n.val - 1
  left_inv n := by simp
  right_inv n := by
    rcases n with ⟨n, hn⟩
    have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    apply Subtype.ext
    simp [Nat.sub_add_cancel hnpos]

private def natAddEquiv (k : ℕ) : ℕ ≃ {n : ℕ // k ≤ n} where
  toFun n := ⟨n + k, by omega⟩
  invFun n := n.val - k
  left_inv n := by simp
  right_inv n := by
    rcases n with ⟨n, hn⟩
    apply Subtype.ext
    exact Nat.sub_add_cancel hn

private theorem tsum_nat_succ_eq_tsum_ne_zero (f : ℕ → ℝ≥0∞) :
    ∑' n : ℕ, f (n + 1) = ∑' n : ℕ, if n = 0 then 0 else f n := by
  classical
  calc
    ∑' n : ℕ, f (n + 1) = ∑' n : {n : ℕ // n ≠ 0}, f n.val := by
      simpa [natSuccEquiv] using
        (natSuccEquiv.tsum_eq (fun n : {n : ℕ // n ≠ 0} => f n.val))
    _ = ∑' n : ℕ, if n = 0 then 0 else f n := by
      calc
        _ = ∑' n : ℕ, {n : ℕ | n ≠ 0}.indicator (fun n => f n) n := tsum_subtype _ _
        _ = _ := by
          congr 1
          funext n
          by_cases hn : n = 0 <;> simp [hn]

private theorem paretoRaw_tsum {θ : ℝ} (hθ : 1 < θ) :
    ∑' n, paretoRaw θ n = ENNReal.ofReal (paretoZ θ) := by
  classical
  have hdiff := ENNReal.ofReal_tsum_of_nonneg
    (fun n => paretoDiff_nonneg (by linarith) n) (paretoDiff_summable hθ)
  rw [paretoDiff_tsum hθ] at hdiff
  have hshift := tsum_nat_succ_eq_tsum_ne_zero (paretoRaw θ)
  have hrawsucc : ∑' n : ℕ, paretoRaw θ (n + 1) = ENNReal.ofReal 1 := by
    simpa [paretoRaw] using hdiff.symm
  calc
    ∑' n : ℕ, paretoRaw θ n = paretoRaw θ 0 +
        ∑' n : ℕ, if n = 0 then 0 else paretoRaw θ n :=
      by
        exact ENNReal.summable.tsum_eq_add_tsum_ite' 0
    _ = ENNReal.ofReal (paretoZ θ - 1) + ∑' n : ℕ, paretoRaw θ (n + 1) := by
      rw [← hshift]
      simp [paretoRaw]
    _ = ENNReal.ofReal (paretoZ θ) := by
      rw [hrawsucc, ← ENNReal.ofReal_add (sub_nonneg.mpr (paretoZ_ge_one hθ))
        (by norm_num : (0 : ℝ) ≤ 1)]
      rw [sub_add_cancel]

private noncomputable def paretoOffspring (θ : ℝ) (hθ : 1 < θ) : PMF ℕ :=
  PMF.normalize (paretoRaw θ)
    (by
      rw [paretoRaw_tsum hθ]
      exact ne_of_gt (ENNReal.ofReal_pos.mpr
        (lt_of_lt_of_le zero_lt_one (paretoZ_ge_one hθ))))
    (by rw [paretoRaw_tsum hθ]; exact ENNReal.ofReal_ne_top)

private theorem paretoOffspring_apply_succ {θ : ℝ} (hθ : 1 < θ) (n : ℕ) :
    paretoOffspring θ hθ (n + 1) =
      ENNReal.ofReal (paretoDiff θ n) * (ENNReal.ofReal (paretoZ θ))⁻¹ := by
  change PMF.normalize (paretoRaw θ) _ _ (n + 1) = _
  rw [PMF.normalize_apply, paretoRaw_tsum hθ]
  simp [paretoRaw]

private theorem paretoOffspring_zero_ne_zero {θ : ℝ} (hθ : 1 < θ) :
    paretoOffspring θ hθ 0 ≠ 0 := by
  change PMF.normalize (paretoRaw θ) _ _ 0 ≠ 0
  rw [PMF.normalize_apply, paretoRaw_tsum hθ, paretoRaw]
  apply mul_ne_zero
  · exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr (paretoZ_gt_one hθ)))
  · exact ENNReal.inv_ne_zero.mpr ENNReal.ofReal_ne_top

private theorem paretoOffspring_nondegenerate {θ : ℝ} (hθ : 1 < θ) :
    paretoOffspring θ hθ 1 ≠ 1 := by
  intro h
  have hsupp := (paretoOffspring θ hθ).apply_eq_one_iff 1 |>.mp h
  have hzero : paretoOffspring θ hθ 0 = 0 := by
    have : 0 ∉ (paretoOffspring θ hθ).support := by rw [hsupp]; simp
    exact (paretoOffspring θ hθ).apply_eq_zero_iff 0 |>.mpr this
  exact paretoOffspring_zero_ne_zero hθ hzero

private theorem paretoOffspring_critical {θ : ℝ} (hθ : 1 < θ) :
    IsCritical (paretoOffspring θ hθ) := by
  classical
  unfold IsCritical
  let μ := paretoOffspring θ hθ
  have hweight_nonneg : ∀ n : ℕ, 0 ≤ ((n : ℝ) + 1) * paretoDiff θ n := by
    intro n
    exact mul_nonneg (by positivity) (paretoDiff_nonneg (by linarith) n)
  have hweight := ENNReal.ofReal_tsum_of_nonneg hweight_nonneg
    (paretoWeightedDiff_hasSum hθ).summable
  rw [paretoWeightedDiff_tsum hθ] at hweight
  change ENNReal.ofReal (paretoZ θ) =
    ∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) * paretoDiff θ n) at hweight
  have hsplit : (∑' n : ℕ, (n : ℝ≥0∞) * μ n) =
      ∑' n : ℕ, if n = 0 then 0 else (n : ℝ≥0∞) * μ n := by
    calc
      _ = (0 : ℝ≥0∞) * μ 0 +
          ∑' n : ℕ, if n = 0 then 0 else (n : ℝ≥0∞) * μ n :=
        by
          simpa using (ENNReal.summable.tsum_eq_add_tsum_ite'
            (f := fun n : ℕ => (n : ℝ≥0∞) * μ n) 0)
      _ = _ := by simp
  have hshift := tsum_nat_succ_eq_tsum_ne_zero (fun n : ℕ => (n : ℝ≥0∞) * μ n)
  calc
    ∑' n : ℕ, (n : ℝ≥0∞) * μ n =
        ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * μ (n + 1) := by
      rw [hsplit]
      exact hshift.symm
    _ = ∑' n : ℕ,
        ENNReal.ofReal (((n : ℝ) + 1) * paretoDiff θ n) *
          (ENNReal.ofReal (paretoZ θ))⁻¹ := by
      apply tsum_congr
      intro n
      rw [paretoOffspring_apply_succ hθ n]
      have hcast : ((n + 1 : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((n : ℝ) + 1) := by
        rw [ENNReal.ofReal_add (by positivity : 0 ≤ (n : ℝ)) (by norm_num : (0 : ℝ) ≤ 1)]
        simp [ENNReal.ofReal_natCast]
      rw [hcast, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity : 0 ≤ (n : ℝ) + 1)]
    _ = (∑' n : ℕ, ENNReal.ofReal (((n : ℝ) + 1) * paretoDiff θ n)) *
        (ENNReal.ofReal (paretoZ θ))⁻¹ := ENNReal.tsum_mul_right
    _ = ENNReal.ofReal (paretoZ θ) * (ENNReal.ofReal (paretoZ θ))⁻¹ := by
      rw [hweight.symm]
    _ = 1 := ENNReal.mul_inv_cancel
      (ne_of_gt (ENNReal.ofReal_pos.mpr (lt_of_lt_of_le zero_lt_one (paretoZ_ge_one hθ))))
      ENNReal.ofReal_ne_top

private theorem paretoDiff_tail_tsum {θ : ℝ} (hθ : 1 < θ) (k : ℕ) :
    ∑' n : ℕ, paretoDiff θ (n + k) = paretoTail θ k := by
  have hu := paretoTail_summable hθ
  have huk : Summable (fun n : ℕ => paretoTail θ (n + k)) :=
    (summable_nat_add_iff (f := paretoTail θ) k).2 hu
  have huk1 : Summable (fun n : ℕ => paretoTail θ (n + (k + 1))) :=
    (summable_nat_add_iff (f := paretoTail θ) (k + 1)).2 hu
  have hsumk := hu.sum_add_tsum_nat_add k
  have hsumk1 := hu.sum_add_tsum_nat_add (k + 1)
  have hprefix : (∑ n ∈ Finset.range (k + 1), paretoTail θ n) =
      (∑ n ∈ Finset.range k, paretoTail θ n) + paretoTail θ k := by
    rw [Finset.sum_range_succ]
  have hsub : ∑' n : ℕ,
      (paretoTail θ (n + k) - paretoTail θ (n + (k + 1))) = paretoTail θ k := by
    rw [Summable.tsum_sub huk huk1]
    rw [hprefix] at hsumk1
    linarith
  convert hsub using 1
  · apply tsum_congr
    intro n
    simp only [paretoDiff]
    congr 1

private theorem paretoDiff_tail_ennreal {θ : ℝ} (hθ : 1 < θ) (k : ℕ) :
    ∑' n : ℕ, ENNReal.ofReal (paretoDiff θ (n + k)) =
      ENNReal.ofReal (paretoTail θ k) := by
  have hdiff : Summable (fun n : ℕ => paretoDiff θ (n + k)) :=
    (summable_nat_add_iff (f := paretoDiff θ) k).2 (paretoDiff_summable hθ)
  have h := ENNReal.ofReal_tsum_of_nonneg
    (fun n => paretoDiff_nonneg (by linarith) _) hdiff
  rw [paretoDiff_tail_tsum hθ k] at h
  exact h.symm

private theorem paretoOffspring_measure_Ici_succ {θ : ℝ} (hθ : 1 < θ) (k : ℕ) :
    (paretoOffspring θ hθ).toMeasure (Set.Ici (k + 1)) =
      ENNReal.ofReal (paretoTail θ k) * (ENNReal.ofReal (paretoZ θ))⁻¹ := by
  let μ := paretoOffspring θ hθ
  let f : ℕ → ℝ≥0∞ := fun n => (Set.Ici (k + 1)).indicator (μ : ℕ → ℝ≥0∞) n
  have hf0 : f 0 = 0 := by simp [f, Set.indicator]
  have hsplit : (∑' n : ℕ, f n) = ∑' n : ℕ, f (n + 1) := by
    calc
      _ = f 0 + ∑' n : ℕ, if n = 0 then 0 else f n :=
        ENNReal.summable.tsum_eq_add_tsum_ite' (f := f) 0
      _ = ∑' n : ℕ, if n = 0 then 0 else f n := by rw [hf0, zero_add]
      _ = _ := (tsum_nat_succ_eq_tsum_ne_zero f).symm
  have htailSum : (∑' n : ℕ, f n) =
      ENNReal.ofReal (paretoTail θ k) *
        (ENNReal.ofReal (paretoZ θ))⁻¹ := by
    calc
      _ = ∑' n : ℕ, if k ≤ n then μ (n + 1) else 0 := by
        rw [hsplit]
        apply tsum_congr
        intro n
        simp [f, Set.indicator]
      _ = _ := by
        rw [show (fun n : ℕ => if k ≤ n then μ (n + 1) else 0) =
            fun n => (if k ≤ n then ENNReal.ofReal (paretoDiff θ n) else 0) *
              (ENNReal.ofReal (paretoZ θ))⁻¹ by
          funext n
          by_cases hkn : k ≤ n <;> simp [hkn, μ, paretoOffspring_apply_succ hθ n]]
        rw [ENNReal.tsum_mul_right]
        have hsub : (∑' n : ℕ, if k ≤ n then ENNReal.ofReal (paretoDiff θ n) else 0) =
            ∑' n : {n : ℕ // k ≤ n}, ENNReal.ofReal (paretoDiff θ n.val) := by
          calc
            _ = ∑' n : ℕ, ({n : ℕ | k ≤ n}.indicator
                (fun n => ENNReal.ofReal (paretoDiff θ n))) n := by
              apply tsum_congr
              intro n
              simp [Set.indicator]
            _ = _ := (tsum_subtype (s := {n : ℕ | k ≤ n})
              (fun n : ℕ => ENNReal.ofReal (paretoDiff θ n))).symm
        rw [hsub, ← (natAddEquiv k).tsum_eq
          (fun n : {n : ℕ // k ≤ n} => ENNReal.ofReal (paretoDiff θ n.val))]
        exact congrArg (fun q : ℝ≥0∞ => q * (ENNReal.ofReal (paretoZ θ))⁻¹)
          (by simpa [natAddEquiv] using paretoDiff_tail_ennreal hθ k)
  rw [PMF.toMeasure_apply_eq_tsum μ (Set.Ici (k + 1))]
  simpa [f] using htailSum

private theorem paretoOffspring_tail {θ : ℝ} (hθ : 1 < θ) {j : ℕ} (hj : 1 ≤ j) :
    ((paretoOffspring θ hθ).toMeasure (Set.Ici j)).toReal =
      (j : ℝ) ^ (-θ) * (1 / paretoZ θ) := by
  let k := j - 1
  have hk : k + 1 = j := Nat.sub_add_cancel hj
  rw [show j = k + 1 by exact hk.symm, paretoOffspring_measure_Ici_succ hθ k]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_inv]
  rw [ENNReal.toReal_ofReal (paretoTail_nonneg θ k), ENNReal.toReal_ofReal
    (le_of_lt (lt_of_lt_of_le zero_lt_one (paretoZ_ge_one hθ)))]
  simp [paretoTail, k, hk]

/-- An explicit critical offspring law with a Pareto tail in the normalized stable domain. -/
theorem existsStableDomain_pareto {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ (μ : PMF ℕ) (a : ℕ → ℝ), StableDomain μ θ a := by
  let μ := paretoOffspring θ hθ.1
  let L : ℝ → ℝ := fun _ => 1 / paretoZ θ
  have hZ : 0 < paretoZ θ := lt_of_lt_of_le zero_lt_one (paretoZ_ge_one hθ.1)
  have hLslow : SlowlyVarying L := by
    intro c hc
    have hfun : (fun x : ℝ => L (c * x) / L x) = fun _ => 1 := by
      funext x
      simp [L, ne_of_gt hZ]
    rw [hfun]
    exact tendsto_const_nhds
  have hLmeas : Measurable L := measurable_const
  have hLnonneg : ∀ x, 0 < x → 0 ≤ L x := fun _ _ => (one_div_pos.mpr hZ).le
  obtain ⟨a, ha⟩ := Attraction.exists_stableDomain_of_tail
    (paretoOffspring_critical hθ.1) (paretoOffspring_nondegenerate hθ.1) hθ
    hLmeas hLnonneg hLslow (fun j hj => by
      simpa [L] using paretoOffspring_tail hθ.1 hj)
  exact ⟨μ, a, ha⟩

end BGW.StableTrees
