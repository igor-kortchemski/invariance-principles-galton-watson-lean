/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StablePositiveJumpsAnalysis
public import BGW.StableTrees.StablePositiveJumpsGrid
public import BGW.StableTrees.StablePositiveJumpsPath

import Mathlib.Data.NNRat.Encodable

import BGW.Probability.NNReal

/-!
# Positive jumps of the spectrally positive stable process

For `1 < θ < 2`, independent increments and the stable tail lower bound imply a jump in every
fixed nonempty time interval. A countable rational intersection and simultaneous spectral
positivity give positive jumps in every open interval almost surely.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

open BGW.Probability

namespace BGW.StableTrees

private theorem frequent_mesh_tail {θ c L δ : ℝ} (hθ : 0 < θ) (hc : 0 < c)
    (hL : 0 < L) (hδ : 0 < δ)
    (hfreq : ∃ᶠ x in atTop, c ≤ x ^ θ * (stableLaw θ : Measure ℝ).real (Set.Ioi x)) :
    ∃ᶠ n : ℕ in atTop, L * c * δ ^ (-θ) / 2 ≤
      (n : ℝ) * (stableLaw θ : Measure ℝ).real
        (Set.Ioi (δ * (L / (n : ℝ)) ^ (-(1 / θ)))) := by
  let z : ℝ → ℝ := fun x => L * (x / δ) ^ θ
  have hzTop : Tendsto z atTop atTop := by
    apply Tendsto.const_mul_atTop hL
    exact (_root_.tendsto_rpow_atTop hθ).comp (tendsto_id.atTop_div_const hδ)
  refine frequently_atTop.mpr fun N => ?_
  have hev : ∀ᶠ x in atTop, 0 < x ∧ max 2 (2 * (N : ℝ)) ≤ z x := by
    filter_upwards [eventually_gt_atTop (0 : ℝ),
      hzTop.eventually (eventually_ge_atTop (max 2 (2 * (N : ℝ))))] with x hx hxz
    exact ⟨hx, hxz⟩
  obtain ⟨x, hxc, hx, hxz⟩ := (hfreq.and_eventually hev).exists
  have hz2 : 2 ≤ z x := (le_max_left _ _).trans hxz
  have hzN : 2 * (N : ℝ) ≤ z x := (le_max_right _ _).trans hxz
  let n : ℕ := ⌊z x⌋₊
  have hnle : (n : ℝ) ≤ z x := Nat.floor_le (show 0 ≤ z x by linarith)
  have hzlt : z x < (n : ℝ) + 1 := by simpa [n] using Nat.lt_floor_add_one (z x)
  have hnlow : z x / 2 ≤ (n : ℝ) := by linarith
  have hnN : N ≤ n := by exact_mod_cast (show (N : ℝ) ≤ (n : ℝ) by linarith)
  have hnR : (0 : ℝ) < (n : ℝ) := by linarith
  let y : ℝ := δ * (L / (n : ℝ)) ^ (-(1 / θ))
  have hrle : (n : ℝ) / L ≤ (x / δ) ^ θ := by
    apply (div_le_iff₀ hL).mpr
    dsimp [z] at hnle
    simpa [mul_comm] using hnle
  have hpowle : ((n : ℝ) / L) ^ (1 / θ) ≤ x / δ := by
    calc
      ((n : ℝ) / L) ^ (1 / θ) ≤ ((x / δ) ^ θ) ^ (1 / θ) :=
        Real.rpow_le_rpow (z := 1 / θ) (by positivity) hrle (by positivity)
      _ = x / δ := by rw [one_div, Real.rpow_rpow_inv (by positivity) hθ.ne']
  have hyx : y ≤ x := by
    dsimp [y]
    rw [Real.rpow_neg_eq_inv_rpow, inv_div]
    calc
      δ * ((n : ℝ) / L) ^ (1 / θ) ≤ δ * (x / δ) :=
        mul_le_mul_of_nonneg_left hpowle hδ.le
      _ = x := mul_div_cancel₀ x hδ.ne'
  have hpx : (stableLaw θ : Measure ℝ).real (Set.Ioi x) ≤
      (stableLaw θ : Measure ℝ).real (Set.Ioi y) :=
    measureReal_mono (fun _ hz => hyx.trans_lt hz)
  have hxpow : 0 < x ^ θ := Real.rpow_pos_of_pos hx θ
  have hcy : c ≤ x ^ θ * (stableLaw θ : Measure ℝ).real (Set.Ioi y) :=
    hxc.trans (mul_le_mul_of_nonneg_left hpx hxpow.le)
  have hp : c / x ^ θ ≤ (stableLaw θ : Measure ℝ).real (Set.Ioi y) :=
    (div_le_iff₀ hxpow).mpr (by simpa [mul_comm] using hcy)
  have heq : z x / 2 * (c / x ^ θ) = L * c * δ ^ (-θ) / 2 := by
    dsimp [z]
    rw [Real.div_rpow hx.le hδ.le, Real.rpow_neg hδ.le]
    have hδpow : δ ^ θ ≠ 0 := (Real.rpow_pos_of_pos hδ θ).ne'
    field_simp [hxpow.ne', hδpow]
  refine ⟨n, hnN, ?_⟩
  change L * c * δ ^ (-θ) / 2 ≤ (n : ℝ) * (stableLaw θ : Measure ℝ).real (Set.Ioi y)
  calc
    L * c * δ ^ (-θ) / 2 = z x / 2 * (c / x ^ θ) := heq.symm
    _ ≤ (n : ℝ) * (stableLaw θ : Measure ℝ).real (Set.Ioi y) :=
      mul_le_mul hnlow hp (div_nonneg hc.le hxpow.le) (Nat.cast_nonneg _)

private def gridSet (a : ℝ≥0) (h : ℝ≥0) (n : ℕ) (δ : ℝ) : Set DLoc :=
  {f | ∀ k < n, f.1 (a + ((k : ℝ≥0) + 1) * h) - f.1 (a + (k : ℝ≥0) * h) ≤ δ}

private theorem measurableSet_gridSet (a : ℝ≥0) (h : ℝ≥0) (n : ℕ) (δ : ℝ) :
    MeasurableSet (gridSet a h n δ) := by
  have heq : gridSet a h n δ = ⋂ k : ℕ, ⋂ (_ : k < n),
      {f : DLoc | f.1 (a + ((k : ℝ≥0) + 1) * h) - f.1 (a + (k : ℝ≥0) * h) ≤ δ} := by
    ext f
    simp [gridSet]
  rw [heq]
  apply MeasurableSet.iInter
  intro k
  apply MeasurableSet.iInter
  intro _
  exact measurableSet_le ((DLoc.measurable_eval _).sub (DLoc.measurable_eval _)) measurable_const

private theorem measureReal_gridSet {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) {h : ℝ≥0}
    (hh : 0 < h) (n : ℕ) (δ : ℝ) :
    (stableLocalLaw θ : Measure DLoc).real (gridSet a h n δ) =
      (stableLaw θ : Measure ℝ).real (Set.Iic (δ * (h : ℝ) ^ (-(1 / θ)))) ^ n := by
  rw [measureReal_def, gridSet, measure_grid_increments_le hθ a hh n δ]
  simp [measureReal_def]

private theorem measureReal_gridSet_le_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {a b : ℝ≥0} (hab : a < b) {c δ : ℝ} {n : ℕ} (hn : 0 < n)
    (hnTail : ((b - a : ℝ≥0) : ℝ) * c * δ ^ (-θ) / 2 ≤
      (n : ℝ) * (stableLaw θ : Measure ℝ).real
        (Set.Ioi (δ * (((b - a : ℝ≥0) : ℝ) / (n : ℝ)) ^ (-(1 / θ))))) :
    (stableLocalLaw θ : Measure DLoc).real (gridSet a ((b - a) / (n : ℝ≥0)) n δ) ≤
      Real.exp (-(((b - a : ℝ≥0) : ℝ) * c * δ ^ (-θ) / 2)) := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hmesh : (((b - a) / (n : ℝ≥0) : ℝ≥0) : ℝ) = ((b - a : ℝ≥0) : ℝ) / (n : ℝ) := by
    simp [NNReal.coe_sub hab.le]
  have hh : 0 < (b - a) / (n : ℝ≥0) := by
    apply div_pos
    · exact tsub_pos_iff_lt.mpr hab
    · exact_mod_cast hn
  rw [measureReal_gridSet hθ a hh n δ, hmesh]
  let y : ℝ := δ * (((b - a : ℝ≥0) : ℝ) / (n : ℝ)) ^ (-(1 / θ))
  let p : ℝ := (stableLaw θ : Measure ℝ).real (Set.Iic y)
  let q : ℝ := (stableLaw θ : Measure ℝ).real (Set.Ioi y)
  have hpq : p = 1 - q := by
    have hcompl := probReal_compl_eq_one_sub (μ := (stableLaw θ : Measure ℝ))
      (s := Set.Iic y) measurableSet_Iic
    rw [Set.compl_Iic] at hcompl
    dsimp [p, q]
    linarith
  change _ ≤ (n : ℝ) * q at hnTail
  have hq1 : q ≤ 1 := measureReal_le_one
  have hpow := pow_le_pow_left₀ (sub_nonneg.mpr hq1) (Real.one_sub_le_exp_neg q) n
  change p ^ n ≤ _
  rw [hpq]
  calc
    (1 - q) ^ n ≤ (Real.exp (-q)) ^ n := hpow
    _ = Real.exp (-((n : ℝ) * q)) := by rw [← Real.exp_nat_mul]; congr 1; ring
    _ ≤ Real.exp (-(((b - a : ℝ≥0) : ℝ) * c * δ ^ (-θ) / 2)) := by
      apply Real.exp_le_exp.mpr
      exact neg_le_neg hnTail

private theorem noJump_real_le_exp {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2)
    {a b : ℝ≥0} (hab : a < b) {c δ : ℝ} (hc : 0 < c) (hδ : 0 < δ)
    (hfreq : ∃ᶠ x in atTop, c ≤ x ^ θ * (stableLaw θ : Measure ℝ).real (Set.Ioi x)) :
    (stableLocalLaw θ : Measure DLoc).real
        {f | ∀ s ∈ Set.Ioc a b, Function.leftLim f.1 s = f.1 s} ≤
      Real.exp (-(((b - a : ℝ≥0) : ℝ) * c * δ ^ (-θ) / 2)) := by
  let A : ℕ → Set DLoc := fun n => gridSet a ((b - a) / (n : ℝ≥0)) n δ
  let B : ℕ → Set DLoc := fun N => ⋂ n : ℕ, ⋂ (_ : N ≤ n), A n
  let U : Set DLoc := ⋃ N, B N
  have hmono : Monotone B := by
    intro N M hNM f hf
    simp only [B, Set.mem_iInter] at hf ⊢
    intro n hn
    exact hf n (hNM.trans hn)
  have hsub : {f : DLoc | ∀ s ∈ Set.Ioc a b, Function.leftLim f.1 s = f.1 s} ⊆ U := by
    intro f hf
    obtain ⟨N, hN⟩ := eventually_atTop.mp (eventually_grid_increments_le hab hf hδ)
    apply Set.mem_iUnion.mpr ⟨N, ?_⟩
    simp only [B, Set.mem_iInter]
    intro n hn
    exact hN n hn
  have hB : ∀ N, (stableLocalLaw θ : Measure DLoc).real (B N) ≤
      Real.exp (-(((b - a : ℝ≥0) : ℝ) * c * δ ^ (-θ) / 2)) := by
    intro N
    obtain ⟨n, hnN, hnTail⟩ := frequently_atTop'.mp
      (frequent_mesh_tail (by linarith [hθ.1]) hc (show (0 : ℝ) < ((b - a : ℝ≥0) : ℝ) by
          rw [NNReal.coe_sub hab.le]
          exact sub_pos.mpr (show (a : ℝ) < (b : ℝ) by exact_mod_cast hab))
        hδ hfreq) N
    have hn : 0 < n := (Nat.zero_le N).trans_lt hnN
    apply (measureReal_mono (Set.iInter₂_subset n hnN.le) (measure_ne_top _ _)).trans
    exact measureReal_gridSet_le_exp hθ hab hn hnTail
  have hlim : Tendsto (fun N => (stableLocalLaw θ : Measure DLoc).real (B N)) atTop
      (𝓝 ((stableLocalLaw θ : Measure DLoc).real U)) := by
    have hlim := (ENNReal.tendsto_toReal (measure_ne_top (stableLocalLaw θ : Measure DLoc) U)).comp
      (tendsto_measure_iUnion_atTop (μ := (stableLocalLaw θ : Measure DLoc)) hmono)
    simpa [Function.comp_def, measureReal_def, U] using hlim
  exact (measureReal_mono hsub (measure_ne_top _ _)).trans
    (le_of_tendsto hlim (Eventually.of_forall hB))

/-- For `1 < θ < 2` and a fixed interval `(a, b]`, the stable process jumps in `(a, b]` almost
surely. -/
theorem ae_exists_jump_Ioc {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) {a b : ℝ≥0}
    (hab : a < b) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∃ s ∈ Set.Ioc a b, Function.leftLim f.1 s ≠ f.1 s := by
  obtain ⟨c, hc, hfreq⟩ := frequently_le_rpow_mul_stableLaw_Ioi hθ hθ2
  let L : ℝ := ((b - a : ℝ≥0) : ℝ)
  have hL : 0 < L := by
    dsimp [L]
    rw [NNReal.coe_sub hab.le]
    exact sub_pos.mpr (show (a : ℝ) < (b : ℝ) by exact_mod_cast hab)
  have hbound (n : ℕ) : (stableLocalLaw θ : Measure DLoc).real
      {f | ∀ s ∈ Set.Ioc a b, Function.leftLim f.1 s = f.1 s} ≤
      Real.exp (-(L * c * ((n + 1 : ℝ)⁻¹) ^ (-θ) / 2)) := by
    apply noJump_real_le_exp hθ hθ2 hab hc (by positivity)
    exact hfreq
  have hnTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hrpowTop : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ θ) atTop atTop :=
    (_root_.tendsto_rpow_atTop (by linarith [hθ.1])).comp hnTop
  have hmulTop : Tendsto (fun n : ℕ => L * c / 2 * ((n + 1 : ℕ) : ℝ) ^ θ) atTop atTop :=
    hrpowTop.const_mul_atTop (by positivity)
  have harg : Tendsto (fun n : ℕ => -(L * c * (((n + 1 : ℕ) : ℝ)) ^ θ / 2)) atTop atBot := by
    convert tendsto_neg_atTop_atBot.comp hmulTop using 1
    ext n
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hexp : Tendsto (fun n : ℕ =>
      Real.exp (-(L * c * ((n + 1 : ℝ)⁻¹) ^ (-θ) / 2))) atTop (𝓝 0) := by
    apply Real.tendsto_exp_atBot.comp
    convert harg using 1
    ext n
    congr 3
    push_cast
    rw [Real.rpow_neg (by positivity), ← Real.inv_rpow (by positivity), inv_inv]
  have hreal0 : (stableLocalLaw θ : Measure DLoc).real
      {f | ∀ s ∈ Set.Ioc a b, Function.leftLim f.1 s = f.1 s} = 0 :=
    le_antisymm (ge_of_tendsto hexp (Eventually.of_forall hbound)) measureReal_nonneg
  rw [ae_iff]
  have hnull := (measureReal_eq_zero_iff (μ := (stableLocalLaw θ : Measure DLoc))).mp hreal0
  simpa only [not_exists, not_and, not_ne_iff] using hnull

/-- **Host jumps (C22 E3, host level).**  For `1 < θ < 2`, almost surely the stable process has a
positive jump in every nonempty open time interval, simultaneously for all intervals. -/
theorem ae_forall_exists_pos_jump {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ a b : ℝ≥0, a < b →
      ∃ s ∈ Set.Ioo a b, Function.leftLim f.1 s < f.1 s := by
  have hrat : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q r : ℚ≥0,
      (q : ℝ≥0) < (r : ℝ≥0) → ∃ s ∈ Set.Ioc (q : ℝ≥0) (r : ℝ≥0),
        Function.leftLim f.1 s ≠ f.1 s := by
    apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro r
    by_cases hqr : (q : ℝ≥0) < (r : ℝ≥0)
    · filter_upwards [ae_exists_jump_Ioc hθ hθ2 hqr] with f hf
      exact fun _ => hf
    · filter_upwards [] with f
      exact fun h => (hqr h).elim
  filter_upwards [hrat, ae_leftLim_le_stableLocalLaw hθ] with f hf hspec
  intro a b hab
  obtain ⟨q, haq, hq⟩ := exists_nnrat_btwn hab
  obtain ⟨r, hqr, hrb⟩ := exists_nnrat_btwn hq
  obtain ⟨s, hs, hjump⟩ := hf q r hqr
  refine ⟨s, ⟨haq.trans hs.1, hs.2.trans_lt hrb⟩, ?_⟩
  exact (hspec s).lt_of_ne hjump

end BGW.StableTrees
