/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StraddlingExcursion
public import BGW.Skorokhod.Jump
public import BGW.StableTrees.StablePositiveJumps

import BGW.StableTrees.BrownianExcursion
import BGW.Skorokhod.ContinuousEmbedding
import BGW.StableTrees.UnitExcursionDensityTransfer

/-!
# Jumps of the normalized stable excursion

At stability index below two, positive jumps of the host inside a valid excursion window give a
positive jump of the normalized excursion. The straddling-excursion identity transfers this to
the normalized Itô excursion. At index two, the Brownian identification gives a continuous path,
whose largest jump is zero.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-! ## Transfer to the normalized excursion -/

/-- **Deterministic transfer**: a positive jump of the host strictly inside a valid cut `(g, d)`
is a positive jump of the normalized cut excursion restricted to `[0,1]`. -/
theorem maxJump_excursionRestrict_normalizeExc_pos (θ : ℝ) {g d u : ℝ≥0} {f : DLoc}
    (hcut : cutValid g d f) (hu : u ∈ Set.Ioo g d)
    (hjump : Function.leftLim f.1 u < f.1 u) :
    0 < maxJump (excursionRestrict 1 (normalizeExc θ (excursionCut g d f))) := by
  let e := excursionCut g d f
  let ζ := e.lifetime
  let s : ℝ≥0 := (u - g) / ζ
  have he : ζ = d - g := excursionCut_lifetime hcut
  have hζ : 0 < ζ := e.lifetime_pos
  have hs : 0 < s := div_pos (tsub_pos_of_lt hu.1) hζ
  have hs1 : s ≤ 1 := by
    apply (div_le_one hζ).mpr
    rw [he]
    exact tsub_le_tsub_right hu.2.le g
  have htime : g + ζ * s = u := by
    dsimp [s]
    rw [mul_div_cancel₀ _ hζ.ne']
    exact add_tsub_cancel_of_le hu.1.le
  have htime_le : g + ζ * s ≤ d := htime.le.trans hu.2.le
  let c : ℝ := ((ζ : ℝ)⁻¹) ^ (1 / θ)
  have hc : 0 < c := Real.rpow_pos_of_pos (inv_pos.mpr (NNReal.coe_pos.mpr hζ)) _
  have hinv : (((ζ : ℝ)⁻¹).toNNReal) = ζ⁻¹ := by
    rw [← NNReal.coe_inv, Real.toNNReal_coe]
  have heval : (normalizeExc θ e).path.1 s = c * (f.1 u - f.1 g) := by
    change ((ζ : ℝ)⁻¹) ^ (1 / θ) * e.path.1 (s / (((ζ : ℝ)⁻¹).toNNReal)) = _
    rw [hinv, div_inv_eq_mul, mul_comm s ζ]
    change ((ζ : ℝ)⁻¹) ^ (1 / θ) * (excursionCut g d f).path.1 (ζ * s) = _
    rw [excursionCut_eval hcut, min_eq_left htime_le, htime]
  let _ : NeBot (𝓝[<] s) := nhdsLT_neBot_of_exists_lt ⟨0, hs⟩
  have hleft : Function.leftLim (normalizeExc θ e).path.1 s =
      c * (Function.leftLim f.1 u - f.1 g) := by
    apply leftLim_eq_of_tendsto
    have hclock : Tendsto (fun v : ℝ≥0 => min (g + ζ * v) d) (𝓝[<] s) (𝓝[<] u) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · have hcont : Continuous (fun v : ℝ≥0 => min (g + ζ * v) d) :=
          (continuous_const.add (continuous_const.mul continuous_id)).min continuous_const
        have heq : min (g + ζ * s) d = u := min_eq_left htime_le |>.trans htime
        exact heq ▸ hcont.continuousAt.continuousWithinAt
      · filter_upwards [self_mem_nhdsWithin] with v hv
        have hmul : ζ * v < ζ * s := mul_lt_mul_of_pos_left hv hζ
        have hlt : g + ζ * v < u := by
          rw [← htime]
          exact add_lt_add_right hmul g
        exact lt_of_le_of_lt (min_le_left _ _) hlt
    have hfleft := (f.2.tendsto_nhdsLT_leftLim u).comp hclock
    have hscaled : Tendsto (fun v : ℝ≥0 => c * (f.1 (min (g + ζ * v) d) - f.1 g))
        (𝓝[<] s) (𝓝 (c * (Function.leftLim f.1 u - f.1 g))) :=
      (hfleft.sub_const (f.1 g)).const_mul c
    convert hscaled using 1
    funext v
    change c * e.path.1 (v / (((ζ : ℝ)⁻¹).toNNReal)) = _
    rw [hinv, div_inv_eq_mul, mul_comm v ζ]
    change c * (excursionCut g d f).path.1 (ζ * v) = _
    rw [excursionCut_eval hcut]
  let t : Set.Icc (0 : ℝ) (1 : ℝ) := ⟨s, s.2, by exact_mod_cast hs1⟩
  have hle := le_ciSup (bddAbove_maxJump (excursionRestrict 1 (normalizeExc θ e))) t
  unfold maxJump
  apply lt_of_lt_of_le _ hle
  change 0 < max ((excursionRestrict 1 (normalizeExc θ e)) t -
    Function.leftLim (excursionRestrict 1 (normalizeExc θ e)) t) 0
  change 0 < max ((normalizeExc θ e).path.1 s -
    Function.leftLim (excursionRestrict 1 (normalizeExc θ e)) t) 0
  rw [show Function.leftLim (excursionRestrict 1 (normalizeExc θ e)) t =
    Function.leftLim (normalizeExc θ e).path.1 s from leftLim_excursionRestrict 1 s hs hs1 _]
  rw [heval, hleft]
  have hpos : 0 < c * (f.1 u - Function.leftLim f.1 u) :=
    mul_pos hc (sub_pos.mpr hjump)
  have heq : c * (f.1 u - f.1 g) - c * (Function.leftLim f.1 u - f.1 g) =
      c * (f.1 u - Function.leftLim f.1 u) := by ring
  rw [heq]
  exact (lt_max_iff).mpr (Or.inl hpos)

/-- For `1 < θ < 2`, the normalized excursion straddling `t > 0` has a positive jump on `[0,1]`,
almost surely. -/
theorem ae_maxJump_straddling_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) {t : ℝ≥0}
    (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      0 < maxJump (excursionRestrict 1 (normalizeExc θ (straddlingExcursion t f))) := by
  filter_upwards [ae_straddle_spec hθ ht, ae_forall_exists_pos_jump hθ hθ2] with f hs hj
  obtain ⟨u, hu, hjump⟩ := hj (straddleStart t f) (straddleEnd t f)
    (hs.2.1.trans hs.2.2.1)
  exact maxJump_excursionRestrict_normalizeExc_pos θ hs.2.2.2.2.1 hu hjump

/-! ## C22 (E3) -/

/-- **C22 (E3), `θ < 2`.**  The normalized excursion has a positive jump: `Δ̄(X^exc) > 0` a.s. -/
theorem ae_maxJump_pos_levyExcLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hθ2 : θ < 2) :
    ∀ᵐ x ∂(levyExcLaw θ : Measure (D 1 ℝ)), 0 < maxJump x := by
  let k : DLoc → D 1 ℝ := fun f =>
    excursionRestrict 1 (normalizeExc θ (straddlingExcursion 1 f))
  have hk : AEMeasurable k (stableLocalLaw θ : Measure DLoc) :=
    (measurable_excursionRestrict 1).comp_aemeasurable (aemeasurable_straddleData hθ 1).snd
  have hopen : IsOpen {x : D 1 ℝ | 0 < maxJump x} :=
    isOpen_lt continuous_const lipschitzWith_two_maxJump.continuous
  rw [← map_straddling_restrict_eq_levyExcLaw hθ (by norm_num : (0 : ℝ≥0) < 1)]
  exact (ae_map_iff hk hopen.measurableSet).mpr
    (ae_maxJump_straddling_pos hθ hθ2 (by norm_num))

/-- **C22 (E3), `θ = 2`.**  The normalized excursion `√2 e` is continuous, so `Δ̄(X^exc) = 0`
a.s. -/
theorem ae_maxJump_eq_zero_levyExcLaw_two :
    ∀ᵐ x ∂(levyExcLaw 2 : Measure (D 1 ℝ)), maxJump x = 0 ∧ Continuous x := by
  rw [BrownianIdentification.levyExcLaw_two]
  have hmeas : AEMeasurable
      (fun e : C(unitInterval, ℝ) => ofContinuous (T := 1) (Real.sqrt 2 • e))
      (BGW.ContinuumTrees.VervaatBridge.law : Measure C(unitInterval, ℝ)) :=
    (lipschitzWith_one_ofContinuous.continuous.measurable.comp
      (continuous_id.const_smul (Real.sqrt 2)).measurable).aemeasurable
  have hsurj : Function.Surjective
      (fun e : C(unitInterval, ℝ) => Real.sqrt 2 • e) := by
    intro e
    refine ⟨(Real.sqrt 2)⁻¹ • e, ?_⟩
    ext t
    simp only [ContinuousMap.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ (Real.sqrt_ne_zero'.mpr (by norm_num)), one_mul]
  have hrange : MeasurableSet (Set.range
      (fun e : C(unitInterval, ℝ) => ofContinuous (T := 1) (Real.sqrt 2 • e))) := by
    have heq : Set.range
        (fun e : C(unitInterval, ℝ) => ofContinuous (T := 1) (Real.sqrt 2 • e)) =
        Set.range (ofContinuous (T := 1) (E := ℝ)) := by
      ext x
      constructor
      · rintro ⟨e, rfl⟩
        exact ⟨Real.sqrt 2 • e, rfl⟩
      · rintro ⟨e, rfl⟩
        obtain ⟨e, rfl⟩ := hsurj e
        exact ⟨e, rfl⟩
    rw [heq]
    exact isClosedEmbedding_ofContinuous.isClosed_range.measurableSet
  filter_upwards [ae_map_mem_range hrange hmeas] with x hx
  obtain ⟨e, rfl⟩ := hx
  refine ⟨?_, (Real.sqrt 2 • e).continuous⟩
  unfold maxJump
  apply le_antisymm
  · apply ciSup_le
    intro t
    change max ((Real.sqrt 2 • e) t - Function.leftLim (Real.sqrt 2 • e) t) 0 ≤ 0
    rw [(Real.sqrt 2 • e).continuous.continuousAt.continuousWithinAt.leftLim_eq]
    simp
  · exact (le_max_right _ _).trans (le_ciSup
      (bddAbove_maxJump (ofContinuous (Real.sqrt 2 • e))) ⟨0, by norm_num, by norm_num⟩)

/-- **C22 (E3), combined form**: for `1 < θ ≤ 2`, almost surely `Δ̄(X^exc) > 0` iff `θ < 2`. -/
theorem ae_maxJump_pos_iff_levyExcLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ x ∂(levyExcLaw θ : Measure (D 1 ℝ)), (0 < maxJump x ↔ θ < 2) := by
  by_cases hθ2 : θ < 2
  · filter_upwards [ae_maxJump_pos_levyExcLaw hθ hθ2] with x hx
    exact iff_of_true hx hθ2
  · have hθeq : θ = 2 := le_antisymm hθ.2 (le_of_not_gt hθ2)
    subst θ
    filter_upwards [ae_maxJump_eq_zero_levyExcLaw_two] with x hx
    simp [hx.1]

end BGW.StableTrees
