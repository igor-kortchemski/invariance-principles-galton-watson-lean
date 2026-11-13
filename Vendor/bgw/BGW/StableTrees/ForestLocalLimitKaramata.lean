/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.RegularVariation.Karamata
import BGW.StableTrees.RegularVariation.Consequences
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.Floor

/-!
# Exact Karamata tails on a residue class

A monotone extension of the discrete summand brackets sums on arithmetic progressions
between their step integrals. Regular variation identifies the integral on compact
windows; Potter bounds supply an integrable tail bound.

Reference: J.-F. Le Gall, *Random trees and applications*, Probab. Surveys 2 (2005),
Section 1.
-/

@[expose] public section

open MeasureTheory Filter Set
open scoped Topology

namespace BGW.StableTrees

private noncomputable def invNorm (B : ℕ → ℝ) (x : ℝ) : ℝ :=
  1 / (x * B ⌊x⌋₊)

private theorem measurable_invNorm (B : ℕ → ℝ) : Measurable (invNorm B) := by
  unfold invNorm
  exact measurable_const.div (measurable_id.mul
    ((measurable_of_countable B).comp Nat.measurable_floor))

private theorem invNorm_nonneg {B : ℕ → ℝ} (hpos : ∀ n, 1 ≤ n → 0 < B n)
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ invNorm B x := by
  have hf : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx)
  exact one_div_nonneg.2 (mul_nonneg (by linarith) (hpos _ hf).le)

private theorem invNorm_antitone {B : ℕ → ℝ} (hmono : Monotone B)
    (hpos : ∀ n, 1 ≤ n → 0 < B n) : AntitoneOn (invNorm B) (Ici 1) := by
  intro x hx y hy hxy
  change (1 : ℝ) ≤ x at hx
  change (1 : ℝ) ≤ y at hy
  have hxB := hpos _ (Nat.le_floor (by simpa using hx))
  have hyB := hpos _ (Nat.le_floor (by simpa using hy))
  apply one_div_le_one_div_of_le (mul_pos (by linarith) hxB)
  exact mul_le_mul hxy (hmono (Nat.floor_mono hxy)) hxB.le (by linarith)

private theorem integral_invNorm_limit {ρ : ℝ} {B : ℕ → ℝ}
    (hrv : RegularlyVaryingSeq ρ B) (hmono : Monotone B)
    (hpos : ∀ n, 1 ≤ n → 0 < B n) (hρ : 0 < ρ) :
    Tendsto (fun n : ℕ => B n * ∫ x in Ioi (n : ℝ), invNorm B x)
      atTop (𝓝 (1 / ρ)) := by
  obtain ⟨C, hC, hpot⟩ := hrv.exists_potter_global hmono hpos hρ.le (half_pos hρ)
  let s : ℝ := ρ / 2
  have hs : 0 < s := half_pos hρ
  let D : ℝ → ℝ := fun t => (C * 2 ^ s) * t ^ (-s - 1)
  have hD : IntegrableOn D (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -s - 1 < -1) zero_lt_one).const_mul _
  have hbound (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : 1 < t) :
      ‖B n / (t * B ⌊t * n⌋₊)‖ ≤ D t := by
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have ht0 : 0 < t := by linarith
    have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnt : 1 ≤ t * n := by nlinarith
    have hmn : n ≤ ⌊t * n⌋₊ := Nat.le_floor (by nlinarith)
    have hBn := hpos n hn
    have hBm := hpos _ (hn.trans hmn)
    have hpow := (hpot n ⌊t * n⌋₊ hn hmn).2
    change ((⌊t * n⌋₊ : ℝ) / n) ^ (ρ - ρ / 2) * B n ≤ C * B ⌊t * n⌋₊ at hpow
    rw [show ρ - ρ / 2 = s by dsimp [s]; ring] at hpow
    have hhalf : t / 2 ≤ (⌊t * n⌋₊ : ℝ) / n := by
      rw [le_div_iff₀ hnR]
      nlinarith [half_le_natFloor hnt]
    have hl : (t / 2) ^ s * B n ≤ C * B ⌊t * n⌋₊ :=
      (mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (by positivity) hhalf hs.le) hBn.le).trans hpow
    rw [Real.div_rpow ht0.le (by norm_num)] at hl
    have hts := Real.rpow_pos_of_pos ht0 s
    have htwo : 0 < (2 : ℝ) ^ s := by positivity
    have hl' : t ^ s * B n ≤ C * 2 ^ s * B ⌊t * n⌋₊ := by
      have hh := mul_le_mul_of_nonneg_right hl htwo.le
      field_simp at hh
      nlinarith [hh]
    rw [Real.norm_eq_abs, abs_of_pos (div_pos hBn (mul_pos ht0 hBm))]
    change B n / (t * B ⌊t * n⌋₊) ≤ C * 2 ^ s * t ^ (-s - 1)
    rw [Real.rpow_sub_one ht0.ne', Real.rpow_neg ht0.le]
    apply (div_le_iff₀ (mul_pos ht0 hBm)).2
    field_simp
    simpa only [mul_comm (B n)] using hl'
  have hlim : Tendsto (fun n : ℕ => ∫ t in Ioi (1 : ℝ), B n / (t * B ⌊t * n⌋₊))
      atTop (𝓝 (∫ t in Ioi (1 : ℝ), t ^ (-ρ - 1))) := by
    apply tendsto_integral_filter_of_dominated_convergence D
    · exact Eventually.of_forall fun n =>
        (measurable_const.div (measurable_id.mul
          ((measurable_of_countable B).comp
            (Nat.measurable_floor.comp (measurable_id.mul_const (n : ℝ)))))).aestronglyMeasurable
    · filter_upwards [eventually_ge_atTop 1] with n hn
      exact (ae_restrict_mem measurableSet_Ioi).mono fun t ht => hbound n hn t ht
    · exact hD
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := by linarith [show 1 < t from ht]
      have H := (tendsto_const_nhds (x := (1 : ℝ))).div
        ((hrv t ht0).const_mul t) (mul_pos ht0 (Real.rpow_pos_of_pos ht0 _)).ne'
      have H' : 1 / (t * t ^ ρ) = t ^ (-ρ - 1) := by
        rw [Real.rpow_sub_one ht0.ne', Real.rpow_neg ht0.le]
        ring
      rw [H'] at H
      refine H.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hBn := (hpos n hn).ne'
      change 1 / (t * (B ⌊t * n⌋₊ / B n)) = _
      field_simp
  have heval : (∫ t in Ioi (1 : ℝ), t ^ (-ρ - 1)) = 1 / ρ := by
    rw [integral_Ioi_rpow_of_lt (by linarith : -ρ - 1 < -1) zero_lt_one]
    simp only [Real.one_rpow]
    field_simp [hρ.ne']
    ring
  rw [heval] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hchange := integral_comp_mul_left_Ioi' (invNorm B) (1 : ℝ) hnR
  simp only [smul_eq_mul, mul_one] at hchange
  rw [← hchange]
  rw [← integral_const_mul, ← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ fun t => by
    dsimp only [invNorm]
    field_simp

private theorem affine_tail_integral (f : ℝ → ℝ) (s : ℝ) {d : ℝ} (hd : 0 < d) :
    (∫ t in Ioi (0 : ℝ), f (s + d * t)) =
      d⁻¹ * ∫ x in Ioi s, f x := by
  rw [integral_comp_mul_left_Ioi (fun x => f (s + x)) 0 hd]
  simp only [mul_zero, smul_eq_mul]
  congr 1
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi]
  have heq : (fun t => (Ioi (0 : ℝ)).indicator (fun x => f (s + x)) t) =
      (fun t => (Ioi s).indicator f (s + t)) := by
    funext t
    by_cases ht : 0 < t
    · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
        indicator_of_mem (show s + t ∈ Ioi s by simpa)]
    · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from ht),
        indicator_of_notMem (show s + t ∉ Ioi s from fun h => ht (by simpa using h))]
  rw [heq, integral_add_left_eq_self]

private theorem progression_bracket {ρ : ℝ} {B : ℕ → ℝ}
    (hrv : RegularlyVaryingSeq ρ B) (hmono : Monotone B)
    (hpos : ∀ n, 1 ≤ n → 0 < B n) (hρ : 0 < ρ)
    {s d : ℕ} (hs : 1 ≤ s) (hd : 0 < d) :
    (∫ x in Ioi (s : ℝ), invNorm B x) ≤
        d * ∑' m : ℕ, 1 / (((s + d * m : ℕ) : ℝ) * B (s + d * m)) ∧
      d * ∑' m : ℕ, 1 / (((s + d * m : ℕ) : ℝ) * B (s + d * m)) ≤
        d / ((s : ℝ) * B s) + ∫ x in Ioi (s : ℝ), invNorm B x := by
  let g : ℝ → ℝ := fun t => invNorm B (s + d * t)
  have hsR : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have hdR : 0 < (d : ℝ) := by exact_mod_cast hd
  have hanti : AntitoneOn g (Ici 0) := by
    intro x hx y hy hxy
    apply invNorm_antitone hmono hpos
    · change 1 ≤ (s : ℝ) + d * x
      nlinarith [show 0 ≤ x from hx]
    · change 1 ≤ (s : ℝ) + d * y
      nlinarith [show 0 ≤ y from hy]
    · gcongr
  have hnn : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ g t := by
    intro t ht
    exact invNorm_nonneg hpos (by nlinarith [show 0 < t from ht])
  have hgnat (m : ℕ) : g m = 1 / (((s + d * m : ℕ) : ℝ) * B (s + d * m)) := by
    dsimp only [g, invNorm]
    norm_cast
    rw [Nat.floor_natCast]
  have hsumm : Summable (fun m : ℕ => g m) := by
    simp_rw [hgnat]
    apply (hrv.summable_inv_mul hmono hpos hρ).comp_injective
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hd (Nat.add_left_cancel hij)
  have hint := hanti.integrableOn_Ioi_zero_of_summable hsumm hnn
  have hlo := hanti.integral_le_tsum hsumm hnn
  have hhi := hanti.tsum_le_integral hint hnn
  have heq : (∫ t in Ioi (0 : ℝ), g t) =
      (d : ℝ)⁻¹ * ∫ x in Ioi (s : ℝ), invNorm B x :=
    affine_tail_integral (invNorm B) (s : ℝ) hdR
  rw [heq] at hlo hhi
  simp_rw [hgnat] at hlo hhi
  have hlo' := mul_le_mul_of_nonneg_left hlo hdR.le
  have hhi' := mul_le_mul_of_nonneg_left hhi hdR.le
  rw [← mul_assoc, mul_inv_cancel₀ hdR.ne', one_mul] at hlo'
  rw [mul_add, ← mul_assoc, mul_inv_cancel₀ hdR.ne', one_mul] at hhi'
  refine ⟨hlo', ?_⟩
  simpa only [g, invNorm, mul_zero, add_zero, Nat.floor_natCast, div_eq_mul_inv,
    mul_one, one_mul] using hhi'

/-- Exact Karamata tail along an arithmetic progression whose starting point is asymptotic
 to the base time. The lattice mesh cancels in the leading constant. -/
theorem regularVariation_progression_tail {ρ : ℝ} {B : ℕ → ℝ}
    (hrv : RegularlyVaryingSeq ρ B) (hmono : Monotone B)
    (hpos : ∀ n, 1 ≤ n → 0 < B n) (hρ : 0 < ρ)
    {d : ℕ} (hd : 0 < d) {s : ℕ → ℕ}
    (hs : Tendsto (fun n : ℕ => (s n : ℝ) / n) atTop (𝓝 1)) :
    Tendsto (fun n : ℕ => B n * (d *
      ∑' m : ℕ, 1 / (((s n + d * m : ℕ) : ℝ) * B (s n + d * m))))
      atTop (𝓝 (1 / ρ)) := by
  have hstop : Tendsto s atTop atTop := by
    have ht := Tendsto.pos_mul_atTop zero_lt_one hs tendsto_natCast_atTop_atTop
    have ht' : Tendsto (fun n => (s n : ℝ)) atTop atTop := by
      refine ht.congr' ?_
      filter_upwards [eventually_ge_atTop 1] with n hn
      have hnR : (n : ℝ) ≠ 0 := by positivity
      field_simp
    exact tendsto_natCast_atTop_iff.1 ht'
  have hrat := (hrv.tendsto_ratio_of_tendsto_div hmono hpos zero_lt_one hs).inv₀
    (by simp)
  simp only [Real.one_rpow, inv_one, inv_div] at hrat
  have hI : Tendsto (fun n : ℕ => B n * ∫ x in Ioi (s n : ℝ), invNorm B x)
      atTop (𝓝 (1 / ρ)) := by
    have ht := hrat.mul ((integral_invNorm_limit hrv hmono hpos hρ).comp hstop)
    rw [one_mul] at ht
    refine ht.congr' ?_
    filter_upwards [hstop.eventually (eventually_ge_atTop 1)] with n hn
    have hB := (hpos (s n) hn).ne'
    dsimp only [Function.comp_apply]
    field_simp
  have hE : Tendsto (fun n : ℕ => B n * ((d : ℝ) / ((s n : ℝ) * B (s n))))
      atTop (𝓝 0) := by
    have ht := (tendsto_const_div_atTop_nhds_zero_nat (d : ℝ) |>.comp hstop).mul hrat
    rw [zero_mul] at ht
    refine ht.congr fun n => by
      dsimp only [Function.comp_apply]
      ring
  have ht := hE.add hI
  rw [zero_add] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hI ht
  · filter_upwards [eventually_ge_atTop 1, hstop.eventually (eventually_ge_atTop 1)]
      with n hn hsn
    exact mul_le_mul_of_nonneg_left (progression_bracket hrv hmono hpos hρ hsn hd).1
      (hpos n hn).le
  · filter_upwards [eventually_ge_atTop 1, hstop.eventually (eventually_ge_atTop 1)]
      with n hn hsn
    have hh := mul_le_mul_of_nonneg_left
      (progression_bracket hrv hmono hpos hρ hsn hd).2 (hpos n hn).le
    simpa only [mul_add] using hh

end BGW.StableTrees
