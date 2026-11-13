/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessRestartSource
import BGW.StableTrees.StableLocalMarkov

/-!
# Exploration restart from a common reversed clock

Capping the old source erases its top mass under the monotone ancestral height clock.
The fresh reversal agrees with the initial common reversed window, so ancestral clock
additivity translates fresh heights by the clock offset. Old and fresh source heights
lie on opposite sides of that offset. Fixed-time gap-freeness identifies it with the
surviving old support top, without evaluating height at a separately chosen crossing time.

The contact additivity used here is inherited from `height_ancestor_clock_identity`.
The fresh path law is the sealed deterministic-time Markov law. All source almost-everywhere
statements use Stieltjes ancestral concentration, with the old endpoint retained.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees


/-- The source before a fixed restart pushes forward to the erased old exploration. -/
theorem ae_exploration_old_source {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t r : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ((explorationStieltjes f (t + r)).measure.restrict (Ioc 0 (t : ℝ))).map
        (fun x : ℝ => (height θ f x.toNNReal).toNNReal) =
      eraseMass (ENNReal.ofReal (-(futureInf (DLoc.shift t f) r 0))) (exploration θ f t) := by
  by_cases ht : t = 0
  · subst t
    filter_upwards with f
    simp [exploration, eraseMass]
  filter_upwards [ae_height_ancestor_fixed hθ (pos_iff_ne_zero.mpr ht),
    ae_reversed_clock_prefix hθ (pos_iff_ne_zero.mpr ht), ae_leftLim_le_stableLocalLaw hθ]
    with f ha hg hf
  let ψ := fun x : ℝ => (supLocalTime θ (reversedAt t f) t -
    supLocalTime θ (reversedAt t f) (t - min x.toNNReal t)).toNNReal
  have hmono : Monotone ψ := by
    intro x y hxy
    have harg : t - min y.toNNReal t ≤ t - min x.toNNReal t :=
      tsub_le_tsub_left (min_le_min_right t (Real.toNNReal_mono hxy)) t
    have hm := hg.2.2.1 (show
      (⟨t - min y.toNNReal t, show t - min y.toNNReal t ≤ t from tsub_le_self⟩ : Iic t) ≤
      ⟨t - min x.toNNReal t, show t - min x.toNNReal t ≤ t from tsub_le_self⟩ from harg)
    change supLocalTime θ (reversedAt t f) (t - min y.toNNReal t) ≤
      supLocalTime θ (reversedAt t f) (t - min x.toNNReal t) at hm
    exact Real.toNNReal_mono (sub_le_sub_left hm _)
  have heq : ∀ᵐ x ∂(explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ)),
      (height θ f x.toNNReal).toNNReal = ψ x := by
    filter_upwards [ae_exploration_ancestral_times f hf t, ae_restrict_mem measurableSet_Ioc]
      with x hx hxt
    have hxt' : x.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hxt.2
    change (height θ f x.toNNReal).toNNReal = _
    dsimp only [ψ]
    rw [min_eq_left hxt', (ha x.toNNReal hxt' hx).2.2.2]
  let c := f.1 t + futureInf (DLoc.shift t f) r 0
  have hF (v : ℝ≥0) (x : ℝ) :
      explorationStieltjes f v x = futureInf f v x.toNNReal := by
    simp only [explorationStieltjes, dite_eq_left (explorationStieltjes_spec f v), futureInfFun]
  have hFt : explorationStieltjes f t (t : ℝ) = f.1 t := by
    rw [hF, Real.toNNReal_coe, futureInf_self]
  have hI : futureInf (DLoc.shift t f) r 0 ≤ 0 := by
    have hh := futureInf_le_eval (DLoc.shift t f) r 0 0 ⟨by simp, zero_le⟩
    change futureInf (DLoc.shift t f) r 0 ≤ f.1 (t + 0) - f.1 t at hh
    simpa only [add_zero, sub_self] using hh
  have hc : c ≤ explorationStieltjes f t (t : ℝ) := by
    rw [hFt]
    dsimp only [c]
    linarith only [hI]
  have hcap : ∀ x ∈ Icc (0 : ℝ) (t : ℝ),
      explorationStieltjes f (t + r) x = min (explorationStieltjes f t x) c := by
    intro x hx
    rw [hF, hF, futureInf_restart_window f t r (Real.toNNReal_le_iff_le_coe.mpr hx.2)]
  have hh := map_stieltjes_min_eq_eraseMass_of_ae t.2 hc hcap hmono.measurable hmono heq
  have hrate : explorationStieltjes f t (t : ℝ) - c =
      -(futureInf (DLoc.shift t f) r 0) := by
    rw [hFt]
    dsimp only [c]
    ring
  change _ = eraseMass (ENNReal.ofReal (explorationStieltjes f t (t : ℝ) - c))
    (exploration θ f t) at hh
  exact hh.trans (congrArg (fun m : ℝ≥0∞ => eraseMass m (exploration θ f t))
    (congrArg ENNReal.ofReal hrate))



private theorem leftLim_shift_of_leftLim_eq (f : DLoc) (t : ℝ≥0)
    (ht : Function.leftLim f.1 t = f.1 t) (v : ℝ≥0) :
    Function.leftLim (DLoc.shift t f).1 v = Function.leftLim f.1 (t + v) - f.1 t := by
  by_cases hv : v = 0
  · subst v
    rw [leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ => zero_le), add_zero, ht]
    change f.1 (t + 0) - f.1 t = f.1 t - f.1 t
    rw [add_zero]
  have hvpos : 0 < v := pos_iff_ne_zero.mpr hv
  have hmap : Tendsto (fun u : ℝ≥0 => t + u) (𝓝[<] v) (𝓝[<] (t + v)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨((continuous_const.add continuous_id).tendsto v).mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact add_lt_add_of_le_of_lt (le_refl t) (show u < v from hu)
  have : (𝓝[<] v).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hvpos⟩
  apply leftLim_eq_of_tendsto
  exact ((f.2.tendsto_nhdsLT_leftLim (t + v)).comp hmap).sub_const (f.1 t)

/-- Reversing a shifted path gives the same initial reversed window at a continuity point. -/
theorem reversedAt_shift_prefix (f : DLoc) (t r : ℝ≥0)
    (ht : Function.leftLim f.1 t = f.1 t) {u : ℝ≥0} (hu : u ≤ r) :
    (reversedAt r (DLoc.shift t f)).1 u = (reversedAt (t + r) f).1 u := by
  rw [reversedAt_apply, reversedAt_apply]
  unfold reversedPath
  rw [min_eq_left hu, min_eq_left (hu.trans (le_add_left le_rfl)),
    leftLim_shift_of_leftLim_eq f t ht]
  change f.1 (t + r) - f.1 t - (Function.leftLim f.1 (t + (r - u)) - f.1 t) = _
  rw [add_tsub_assoc_of_le hu]
  ring

/-- The clocks on a fresh reversed window agree with the common reversed clock. -/
theorem supLocalTime_reversedAt_shift_prefix (θ : ℝ) (f : DLoc) (t r : ℝ≥0)
    (ht : Function.leftLim f.1 t = f.1 t) {u : ℝ≥0} (hu : u ≤ r) :
    supLocalTime θ (reversedAt r (DLoc.shift t f)) u =
      supLocalTime θ (reversedAt (t + r) f) u := by
  unfold supLocalTime
  congr 1
  funext k
  apply supOccupation_prefix_add_const (c := 0)
  intro v hv
  rw [reversedAt_shift_prefix f t r ht (hv.trans hu), add_zero]

/-- At a fixed horizon, the source height is the terminal clock minus its reversed-age clock. -/
theorem ae_exploration_source_clock {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ᵐ x ∂(explorationStieltjes f T).measure.restrict (Ioc 0 (T : ℝ)),
        0 < x ∧ x ≤ (T : ℝ) ∧ 0 ≤ height θ f x.toNNReal ∧
        height θ f x.toNNReal = supLocalTime θ (reversedAt T f) T -
          supLocalTime θ (reversedAt T f) (T - x.toNNReal) := by
  filter_upwards [ae_height_ancestor_fixed hθ hT, ae_leftLim_le_stableLocalLaw hθ]
    with f ha hf
  filter_upwards [ae_exploration_ancestral_times f hf T, ae_restrict_mem measurableSet_Ioc]
    with x hx hxt
  have hh := ha x.toNNReal (Real.toNNReal_le_iff_le_coe.mpr hxt.2) hx
  exact ⟨hxt.1, hxt.2, hh.2.1, hh.2.2.2⟩

/-- The common reversed clock orders the old and fresh source heights around its offset. -/
theorem exploration_source_order_bounds (θ : ℝ) (f : DLoc) (t r : ℝ≥0)
    (hmono : Monotone (fun u : Iic (t + r) => supLocalTime θ (reversedAt (t + r) f) u))
    (hclock : ∀ᵐ x ∂(explorationStieltjes f (t + r)).measure.restrict
      (Ioc 0 ((t + r : ℝ≥0) : ℝ)),
      0 < x ∧ x ≤ ((t + r : ℝ≥0) : ℝ) ∧ 0 ≤ height θ f x.toNNReal ∧
      height θ f x.toNNReal = supLocalTime θ (reversedAt (t + r) f) (t + r) -
        supLocalTime θ (reversedAt (t + r) f) (t + r - x.toNNReal)) :
    let K := supLocalTime θ (reversedAt (t + r) f) (t + r) -
      supLocalTime θ (reversedAt (t + r) f) r
    (((explorationStieltjes f (t + r)).measure.restrict (Ioc 0 (t : ℝ))).map
      (fun x : ℝ => (height θ f x.toNNReal).toNNReal)) (Ioi K.toNNReal) = 0 ∧
    (((explorationStieltjes f (t + r)).measure.restrict
      (Ioc (t : ℝ) ((t + r : ℝ≥0) : ℝ))).map
      (fun x : ℝ => (height θ f x.toNNReal).toNNReal)) (Iio K.toNNReal) = 0 := by
  let T := t + r
  let g := reversedAt T f
  let K := supLocalTime θ g T - supLocalTime θ g r
  have hrT : r ≤ T := le_add_left le_rfl
  have hsubold : Ioc (0 : ℝ) (t : ℝ) ⊆ Ioc 0 (T : ℝ) := by
    intro x hx
    exact ⟨hx.1, hx.2.trans (by exact_mod_cast (le_add_right le_rfl : t ≤ T))⟩
  have hsubnew : Ioc (t : ℝ) (T : ℝ) ⊆ Ioc 0 (T : ℝ) := by
    intro x hx
    exact ⟨t.2.trans_lt hx.1, hx.2⟩
  have hold := hclock.filter_mono (ae_mono (Measure.restrict_mono_set _ hsubold))
  have hnew := hclock.filter_mono (ae_mono (Measure.restrict_mono_set _ hsubnew))
  constructor
  · rw [Measure.map_apply (measurable_exploration_heightMap θ f) measurableSet_Ioi]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hold, ae_restrict_mem measurableSet_Ioc] with x hx hxt
    intro hmem
    have hxt' : x.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hxt.2
    have hage : r ≤ T - x.toNNReal := by
      have hh := tsub_le_tsub_left hxt' T
      simpa only [T, add_tsub_cancel_left] using hh
    have hm := hmono (show (⟨r, hrT⟩ : Iic T) ≤
      ⟨T - x.toNNReal, show T - x.toNNReal ≤ T from tsub_le_self⟩ from hage)
    change supLocalTime θ g r ≤ supLocalTime θ g (T - x.toNNReal) at hm
    have hh : height θ f x.toNNReal ≤ K := by
      rw [hx.2.2.2]
      exact sub_le_sub_left hm _
    exact (not_lt_of_ge (Real.toNNReal_mono hh)) hmem
  · rw [Measure.map_apply (measurable_exploration_heightMap θ f) measurableSet_Iio]
    apply measure_eq_zero_iff_ae_notMem.mpr
    filter_upwards [hnew, ae_restrict_mem measurableSet_Ioc] with x hx hxt
    intro hmem
    have htx : t ≤ x.toNNReal := by
      exact_mod_cast (show (t : ℝ) ≤ (x.toNNReal : ℝ) by
        rw [Real.coe_toNNReal _ hx.1.le]; exact hxt.1.le)
    have hage : T - x.toNNReal ≤ r := by
      have hh := tsub_le_tsub_left htx T
      simpa only [T, add_tsub_cancel_left] using hh
    have hm := hmono (show
      (⟨T - x.toNNReal, show T - x.toNNReal ≤ T from tsub_le_self⟩ : Iic T) ≤
      ⟨r, hrT⟩ from hage)
    change supLocalTime θ g (T - x.toNNReal) ≤ supLocalTime θ g r at hm
    have hh : K ≤ height θ f x.toNNReal := by
      rw [hx.2.2.2]
      exact sub_le_sub_left hm _
    exact (not_lt_of_ge (Real.toNNReal_mono hh)) hmem

/-- The surviving old exploration has support top equal to the common-clock offset. -/
theorem ae_topHeight_erased_exploration {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t r : ℝ≥0) (hr : 0 < r) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (topHeight (eraseMass (ENNReal.ofReal (-(futureInf (DLoc.shift t f) r 0)))
        (exploration θ f t)) : ℝ) =
      supLocalTime θ (reversedAt (t + r) f) (t + r) -
        supLocalTime θ (reversedAt (t + r) f) r := by
  have hT : 0 < t + r := (show (0 : ℝ≥0) ≤ t from zero_le).trans_lt
    (lt_add_of_pos_right t hr)
  filter_upwards [ae_exploration_old_source hθ t r, ae_exploration_source_clock hθ hT,
    ae_reversed_clock_prefix hθ hT, ae_support_gapfree_fixed hθ (t + r)] with f hold hc hg hgap
  let K := supLocalTime θ (reversedAt (t + r) f) (t + r) -
    supLocalTime θ (reversedAt (t + r) f) r
  let ρ := ((explorationStieltjes f (t + r)).measure.restrict (Ioc 0 (t : ℝ))).map
    (fun x : ℝ => (height θ f x.toNNReal).toNNReal)
  let σ := ((explorationStieltjes f (t + r)).measure.restrict
    (Ioc (t : ℝ) ((t + r : ℝ≥0) : ℝ))).map
      (fun x : ℝ => (height θ f x.toNNReal).toNNReal)
  have hb := exploration_source_order_bounds θ f t r hg.2.2.1 hc
  have hK : 0 ≤ K := by
    have hm := hg.2.2.1 (show
      (⟨r, show r ≤ t + r from le_add_left le_rfl⟩ : Iic (t + r)) ≤
      ⟨t + r, show t + r ≤ t + r from le_rfl⟩ from
        (show r ≤ t + r from le_add_left le_rfl))
    change supLocalTime θ (reversedAt (t + r) f) r ≤
      supLocalTime θ (reversedAt (t + r) f) (t + r) at hm
    exact sub_nonneg.mpr hm
  have hKH : K ≤ height θ f (t + r) := sub_le_self _ (by
    rw [supLocalTime_eq_toReal]
    exact ENNReal.toReal_nonneg)
  have hsum : exploration θ f (t + r) = ρ + σ := exploration_source_split θ f t r
  have htop : (topHeight ρ : ℝ) = K := topHeight_left_of_ordered_sum hK hKH hb.1 hb.2
    (fun h hh ε hε => by rw [← hsum]; exact hgap h hh ε hε)
  exact (congrArg (fun μ : Measure ℝ≥0 => (topHeight μ : ℝ)) hold).symm.trans htop

/-- Fresh source heights add the support top of the surviving old exploration. -/
theorem ae_exploration_fresh_height_translation {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (t r : ℝ≥0) (hr : 0 < r) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ᵐ x ∂(explorationStieltjes (DLoc.shift t f) r).measure.restrict (Ioc 0 (r : ℝ)),
        (height θ f (((t : ℝ) + x).toNNReal)).toNNReal =
          (height θ (DLoc.shift t f) x.toNNReal).toNNReal +
          topHeight (eraseMass (ENNReal.ofReal (-(futureInf (DLoc.shift t f) r 0)))
            (exploration θ f t)) := by
  have hT : 0 < t + r := (show (0 : ℝ≥0) ≤ t from zero_le).trans_lt
    (lt_add_of_pos_right t hr)
  have hshiftMeas : Measurable (DLoc.shift t) :=
    DLoc.measurable_shift.comp (measurable_const.prodMk measurable_id)
  have hshift : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ᵐ x ∂(explorationStieltjes (DLoc.shift t f) r).measure.restrict (Ioc 0 (r : ℝ)),
        0 < x ∧ x ≤ (r : ℝ) ∧ 0 ≤ height θ (DLoc.shift t f) x.toNNReal ∧
        height θ (DLoc.shift t f) x.toNNReal =
          supLocalTime θ (reversedAt r (DLoc.shift t f)) r -
            supLocalTime θ (reversedAt r (DLoc.shift t f)) (r - x.toNNReal) := by
    have hh := ae_exploration_source_clock hθ hr
    rw [← map_shift_stableLocalLaw hθ t] at hh
    exact ae_of_ae_map hshiftMeas.aemeasurable hh
  filter_upwards [ae_exploration_source_clock hθ hT, hshift,
    ae_continuousAt_stableLocalLaw hθ t, ae_topHeight_erased_exploration hθ t r hr]
    with f hc hf ht htop
  have hsub : Ioc (t : ℝ) ((t + r : ℝ≥0) : ℝ) ⊆ Ioc 0 ((t + r : ℝ≥0) : ℝ) := by
    intro x hx
    exact ⟨t.2.trans_lt hx.1, hx.2⟩
  have hpart := hc.filter_mono (ae_mono (Measure.restrict_mono_set _ hsub))
  rw [← exploration_source_fresh f t r] at hpart
  have hback := ae_of_ae_map
    (show Measurable (fun x : ℝ => (t : ℝ) + x) from
      measurable_const.add measurable_id).aemeasurable
    hpart
  filter_upwards [hback, hf] with x hx hxf
  have hxr : x.toNNReal ≤ r := Real.toNNReal_le_iff_le_coe.mpr hxf.2.1
  have hsum : ((t : ℝ) + x).toNNReal = t + x.toNNReal := by
    apply NNReal.coe_injective
    change max ((t : ℝ) + x) 0 = (t : ℝ) + max x 0
    exact (max_eq_left (show (0 : ℝ) ≤ (t : ℝ) + x from add_nonneg t.2 hxf.1.le)).trans
      (congrArg (fun y : ℝ => (t : ℝ) + y)
        (max_eq_left (show (0 : ℝ) ≤ x from hxf.1.le))).symm
  have hO := hx.2.2.2
  rw [hsum, add_tsub_add_eq_tsub_left] at hO
  have hleft : Function.leftLim f.1 t = f.1 t := ht.continuousWithinAt.leftLim_eq
  have hF := hxf.2.2.2
  rw [supLocalTime_reversedAt_shift_prefix θ f t r hleft le_rfl,
    supLocalTime_reversedAt_shift_prefix θ f t r hleft
      (show r - x.toNNReal ≤ r from tsub_le_self)] at hF
  apply NNReal.coe_injective
  rw [NNReal.coe_add, Real.coe_toNNReal _ hx.2.2.1, Real.coe_toNNReal _ hxf.2.2.1, htop]
  rw [hsum]
  linarith only [hO, hF]

/-- **Restart identity** (a.s., for fixed `t` and `r`): with `f' = shift t f` the centered
future, `ρ_{t+r}(f)` is `ρ_t(f)` with the top `-inf_{[0,r]} f'` units of mass erased and the
fresh exploration `ρ_r(f')` appended above the remaining support height. -/
theorem ae_exploration_restart {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t r : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      exploration θ f (t + r) =
        concatAbove
          (eraseMass (ENNReal.ofReal (-(futureInf (DLoc.shift t f) r 0))) (exploration θ f t))
          (exploration θ (DLoc.shift t f) r) := by
  by_cases hr : r = 0
  · subst r
    filter_upwards with f
    have hzero : exploration θ (DLoc.shift t f) 0 = 0 := by
      simp [exploration]
    have hI : futureInf (DLoc.shift t f) 0 0 = 0 := by
      rw [futureInf_self]
      change f.1 (t + 0) - f.1 t = 0
      simp only [add_zero, sub_self]
    rw [add_zero, hI, neg_zero, ENNReal.ofReal_zero, eraseMass_zero,
      concatAbove, hzero, Measure.map_zero, add_zero]
  filter_upwards [ae_exploration_old_source hθ t r,
    ae_exploration_fresh_height_translation hθ t r (pos_iff_ne_zero.mpr hr)] with f hold hfresh
  rw [exploration_source_split, hold,
    exploration_fresh_source_map θ f t r _ hfresh]
  rfl

end BGW.StableTrees
