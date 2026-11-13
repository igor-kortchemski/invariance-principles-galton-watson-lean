/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessIdentification

/-!
# Index-two height normalization

The two ladder-height Laplace moments force the Brownian ladder height to equal its level.
Monotonicity and inversion identify the supremum clock with the running supremum, and
prefix reversal gives the height as the terminal value minus the running infimum.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- At index two, the ladder height at each deterministic level is that level. -/
theorem ae_supLadderHeight_two_level (z : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), supLadderHeight 2 z f = (z : ℝ) := by
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  let μ := (stableLocalLaw 2 : Measure DLoc)
  let Y : DLoc → ℝ := fun f => Real.exp (-supLadderHeight 2 z f)
  let c : ℝ := Real.exp (-(z : ℝ))
  have hy : Integrable Y μ := by
    simpa only [Y, μ, neg_zero, zero_mul, zero_sub, one_mul, neg_mul, neg_one_mul] using
      (integrable_exp_neg_supLadder hθ (q := 0) (lam := 1) (by norm_num) (by norm_num) z)
  have hy2 : Integrable (fun f => (Y f) ^ 2) μ := by
    have hi := integrable_exp_neg_supLadder hθ (q := 0) (lam := 2)
      (by norm_num) (by norm_num) z
    apply hi.congr
    filter_upwards with f
    simp only [Y, zero_mul, neg_mul, pow_two, ← Real.exp_add]
    congr 1
    ring
  have hi1 : (∫ f, Y f ∂μ) = c := by
    have hi := (integral_exp_neg_supLadder hθ z (q := 0) (lam := 1)
      (by norm_num) (by norm_num)).2.2
    norm_num at hi
    simpa only [Y, c, neg_one_mul] using hi
  have hi2 : (∫ f, (Y f) ^ 2 ∂μ) = c ^ 2 := by
    have hi := (integral_exp_neg_supLadder hθ z (q := 0) (lam := 2)
      (by norm_num) (by norm_num)).2.2
    norm_num at hi
    calc
      _ = ∫ f, Real.exp (-2 * supLadderHeight 2 z f) ∂μ := by
        apply integral_congr_ae
        filter_upwards with f
        simp only [Y, pow_two, ← Real.exp_add]
        congr 1
        ring
      _ = Real.exp (-(z : ℝ) * 2) := by simpa only [μ, neg_mul] using hi
      _ = c ^ 2 := by
        simp only [c, pow_two, ← Real.exp_add]
        congr 1
        ring
  have hform (f : DLoc) : (Y f - c) ^ 2 = (Y f) ^ 2 - (2 * c) * Y f + c ^ 2 := by ring
  have hfi : Integrable (fun f => (Y f - c) ^ 2) μ := by
    apply ((hy2.sub (hy.const_mul (2 * c))).add (integrable_const (c ^ 2))).congr
    exact Eventually.of_forall fun f => (hform f).symm
  have hz : (∫ f, (Y f - c) ^ 2 ∂μ) = 0 := by
    calc
      _ = ∫ f, (Y f) ^ 2 - (2 * c) * Y f + c ^ 2 ∂μ :=
        integral_congr_ae (Eventually.of_forall hform)
      _ = c ^ 2 - (2 * c) * c + c ^ 2 := by
        erw [integral_add (f := fun f => (Y f) ^ 2 - (2 * c) * Y f)
          (g := fun _ : DLoc => c ^ 2)
          (hy2.sub (hy.const_mul (2 * c))) (integrable_const (c ^ 2)),
          integral_sub hy2 (hy.const_mul (2 * c)), integral_const_mul, hi1, hi2]
        simp only [integral_const, probReal_univ, one_smul]
      _ = 0 := by ring
  have he := (integral_eq_zero_iff_of_nonneg (fun f => sq_nonneg (Y f - c)) hfi).mp hz
  filter_upwards [he] with f hf
  have hsq : (Y f - c) ^ 2 = 0 := hf
  have hY : Y f = c := sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  have harg : -supLadderHeight 2 z f = -(z : ℝ) := Real.exp_injective hY
  linarith only [harg]

/-- The index-two ladder height is the identity simultaneously at every level. -/
theorem ae_supLadderHeight_two :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), ∀ z : ℝ≥0,
      supLadderHeight 2 z f = (z : ℝ) := by
  have hq : ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), ∀ q : ℚ,
      supLadderHeight 2 (q : ℝ).toNNReal f = ((q : ℝ).toNNReal : ℝ) :=
    ae_all_iff.mpr (fun q => ae_supLadderHeight_two_level (q : ℝ).toNNReal)
  filter_upwards [hq, ae_supLadder_spec (show 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 by norm_num)]
    with f hq hs
  have hmono : Monotone (fun z => supLadderHeight 2 z f) := hs.2.2.2.2.1
  have h0 : supLadderHeight 2 0 f = 0 := by simpa using hq 0
  intro z
  have hnon : 0 ≤ supLadderHeight 2 z f := by
    simpa only [h0] using hmono (show (0 : ℝ≥0) ≤ z from zero_le)
  apply le_antisymm
  · by_contra hn
    obtain ⟨q, hzq, hqB⟩ := exists_rat_btwn (not_le.mp hn)
    have hq0 : 0 ≤ (q : ℝ) := z.2.trans hzq.le
    have hle := hmono (show z ≤ (q : ℝ).toNNReal from by
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
      exact hzq.le)
    dsimp only at hle
    rw [hq q, Real.coe_toNNReal _ hq0] at hle
    exact (not_le_of_gt hqB) hle
  · by_contra hn
    obtain ⟨q, hBq, hqz⟩ := exists_rat_btwn (not_le.mp hn)
    have hq0 : 0 ≤ (q : ℝ) := hnon.trans hBq.le
    have hle := hmono (show (q : ℝ).toNNReal ≤ z from
      Real.toNNReal_le_iff_le_coe.mpr hqz.le)
    dsimp only at hle
    rw [hq q, Real.coe_toNNReal _ hq0] at hle
    exact (not_le_of_gt hBq) hle

/-- Brownian normalization: the supremum local time equals the running supremum. -/
theorem ae_supLocalTime_two :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), ∀ t : ℝ≥0,
      supLocalTime 2 f t = supRunning f t := by
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  filter_upwards [ae_supLadderHeight_two, ae_supLadder_spec hθ, ae_supLocalTime_spec hθ,
    ae_eval_zero_stableLocalLaw hθ] with f hb ha hm hf0
  intro t
  have hM : 0 ≤ supLocalTime 2 f t := by
    simpa only [hm.1] using hm.2.1 (show (0 : ℝ≥0) ≤ t from zero_le)
  have hS : 0 ≤ supRunning f t := by
    simpa only [hf0] using eval_le_supRunning f (u := 0) (show (0 : ℝ≥0) ≤ t from zero_le)
  let z : ℝ≥0 := ⟨(supLocalTime 2 f t + supRunning f t) / 2, by linarith only [hM, hS]⟩
  have hAz : supLocalTime 2 f (supLadderTime 2 z f) = (z : ℝ) := ha.2.2.2.2.2 z
  have hBz : supRunning f (supLadderTime 2 z f) = (z : ℝ) := hb z
  have hz : (z : ℝ) = (supLocalTime 2 f t + supRunning f t) / 2 := rfl
  apply le_antisymm
  · by_contra hn
    have hzt : (z : ℝ) < supLocalTime 2 f t := by linarith only [hz, not_le.mp hn]
    have hAt : supLadderTime 2 z f ≤ t := by
      by_contra hnAt
      have hh := hm.2.1 (le_of_lt (not_le.mp hnAt))
      rw [hAz] at hh
      exact (not_le_of_gt hzt) hh
    have hh := monotone_supRunning f hAt
    rw [hBz] at hh
    linarith only [hh, hz, not_le.mp hn]
  · by_contra hn
    have htz : supLocalTime 2 f t < (z : ℝ) := by linarith only [hz, not_le.mp hn]
    have htA : t ≤ supLadderTime 2 z f := by
      by_contra hnAt
      have hh := hm.2.1 (le_of_lt (not_le.mp hnAt))
      rw [hAz] at hh
      exact (not_le_of_gt htz) hh
    have hh := monotone_supRunning f htA
    rw [hBz] at hh
    linarith only [hh, hz, not_le.mp hn]

/-- The running supremum is measurable from the prefix at its horizon. -/
theorem measurable_supRunning_prefix (t : ℝ≥0) :
    Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      (fun f : DLoc => supRunning f t) := by
  let _ : Nonempty (univ : Set (Icc (0 : ℝ) (t : ℝ))) :=
    ⟨⟨⟨0, le_rfl, t.2⟩, mem_univ _⟩⟩
  have hm : Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      (fun f : DLoc => ⨆ s : (univ : Set (Icc (0 : ℝ) (t : ℝ))), DLoc.restrict t f s) :=
    (measurable_iSup_eval (T := (t : ℝ)) (J := univ) ordConnected_univ).comp
      (comap_measurable (DLoc.restrict t))
  have he (f : DLoc) : supRunning f t =
      ⨆ s : (univ : Set (Icc (0 : ℝ) (t : ℝ))), DLoc.restrict t f s := by
    apply le_antisymm
    · apply supRunning_le
      intro u
      exact le_ciSup (f := fun s : (univ : Set (Icc (0 : ℝ) (t : ℝ))) =>
          DLoc.restrict t f s)
        ((isBounded_range (DLoc.restrict t f)).bddAbove.mono (by
          rintro _ ⟨s, rfl⟩
          exact ⟨s.1, rfl⟩))
        ⟨⟨(u : ℝ), u.1.2, by exact_mod_cast u.2⟩, mem_univ _⟩
    · apply ciSup_le
      intro s
      exact eval_le_supRunning f (u := ⟨s.1, s.1.2.1⟩) (by exact_mod_cast s.1.2.2)
  convert hm using 1
  funext f
  exact he f

/-- **θ = 2**: `H_t = X_t - I_t` a.s. for each fixed `t` (uses the H01 normalization). -/
theorem ae_height_two (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw 2 : Measure DLoc), height 2 f t = f.1 t - futureInf f t 0 := by
  have hθ : 1 < (2 : ℝ) ∧ (2 : ℝ) ≤ 2 := by norm_num
  by_cases ht : t = 0
  · subst t
    filter_upwards with f
    simp only [height_zero, futureInf_self, sub_self]
  have hp : MeasurableSet[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      {f | supLocalTime 2 f t = supRunning f t} := by
    let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict t) inferInstance
    exact measurableSet_eq_fun (measurable_supLocalTime_prefix 2 t)
      (measurable_supRunning_prefix t)
  have hr := ae_reversedAt_of_prefix hθ (pos_iff_ne_zero.mpr ht) hp
    (ae_supLocalTime_two.mono fun _ hf => hf t)
  filter_upwards [hr, ae_leftLim_le_stableLocalLaw hθ] with f hf hj
  change supLocalTime 2 (reversedAt t f) t = _
  rw [hf]
  have hs : Function.leftLim f.1 0 = f.1 0 :=
    leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ => zero_le)
  simpa only [tsub_zero] using
    supRunning_reversedAt_window f (show (0 : ℝ≥0) ≤ t from zero_le) hj hs

end BGW.StableTrees
