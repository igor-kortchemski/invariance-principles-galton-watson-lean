/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessExploration
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

/-!
# Reversed clocks and ancestral windows

Measurable compact occupation functions transport uniform convergence to reversed prefixes.
At every ancestral time of a fixed horizon, contact restart identifies the earlier height
as the difference of two values of that clock. Endpoint jumps are retained explicitly.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

private noncomputable def prefixOccupation (θ : ℝ) (T : ℝ≥0) (k : ℕ) (f : DLoc) :
    C(Iic T, ℝ) :=
  ⟨fun u => supOccupation (supEps θ k) f u,
    (continuous_supOccupation (supEps_pos θ k) f).comp continuous_subtype_val⟩

private theorem measurable_prefixOccupation (θ : ℝ) (T : ℝ≥0) (k : ℕ) :
    Measurable[MeasurableSpace.comap (DLoc.restrict T) inferInstance]
      (prefixOccupation θ T k) := by
  let : CompactSpace (Iic T) := isCompact_iff_compactSpace.mp (by
    simpa only [Icc, Iic, zero_le, true_and] using
      (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)))
  let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict T) inferInstance
  apply ContinuousMap.measurable_iff_eval.mpr
  intro u
  exact (measurable_rawFiltration_supOccupation (supEps θ k) u).mono
    ((DLoc.rawFiltration.mono u.2).trans (rawFiltration_le_restrict_comap T)) le_rfl

/-- The public occupation sequence has a continuous monotone clock on a reversed prefix. -/
theorem ae_reversed_clock_prefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {T : ℝ≥0} (hT : 0 < T) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ u : ℝ≥0, u ≤ T →
        Tendsto (fun k => supOccupation (supEps θ k) (reversedAt T f) u) atTop
          (𝓝 (supLocalTime θ (reversedAt T f) u))) ∧
      Continuous (fun u : Iic T => supLocalTime θ (reversedAt T f) u) ∧
      Monotone (fun u : Iic T => supLocalTime θ (reversedAt T f) u) ∧
      supLocalTime θ (reversedAt T f) 0 = 0 := by
  let : CompactSpace (Iic T) := isCompact_iff_compactSpace.mp (by
    simpa only [Icc, Iic, zero_le, true_and] using
      (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)))
  have hp : MeasurableSet[MeasurableSpace.comap (DLoc.restrict T) inferInstance]
      {f | ∃ m : C(Iic T, ℝ),
        Tendsto (fun k => prefixOccupation θ T k f) atTop (𝓝 m)} := by
    let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict T) inferInstance
    exact measurableSet_exists_tendsto (fun k => measurable_prefixOccupation θ T k)
  have ha : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∃ m : C(Iic T, ℝ), Tendsto (fun k => prefixOccupation θ T k f) atTop (𝓝 m) := by
    filter_upwards [ae_supLocalTime_spec hθ, ae_tendsto_supOccupation_uniform hθ] with f hf hu
    let m : C(Iic T, ℝ) :=
      ⟨fun u => supLocalTime θ f u, hf.2.2.1.comp continuous_subtype_val⟩
    refine ⟨m, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
    simp only [ContinuousMap.dist_eq_iSup, Real.dist_eq]
    exact hu T
  filter_upwards [ae_reversedAt_of_prefix hθ hT hp ha] with f hf
  obtain ⟨m, hm⟩ := hf
  have hlim (u : Iic T) :
      Tendsto (fun k => supOccupation (supEps θ k) (reversedAt T f) u) atTop (𝓝 (m u)) :=
    ((continuous_eval_const u : Continuous (fun g : C(Iic T, ℝ) => g u)).tendsto m).comp hm
  have he (u : Iic T) : supLocalTime θ (reversedAt T f) u = m u := (hlim u).limsup_eq
  refine ⟨fun u hu => ?_, ?_, ?_, ?_⟩
  · simpa only [he ⟨u, hu⟩] using hlim ⟨u, hu⟩
  · convert m.continuous using 1
    funext u
    exact he u
  · intro u v huv
    dsimp only
    rw [he u, he v]
    exact le_of_tendsto_of_tendsto (hlim u) (hlim v)
      (Eventually.of_forall fun k => monotone_supOccupation (supEps_pos θ k).le _ huv)
  · unfold supLocalTime
    simp only [supOccupation_zero, limsup_const]

private theorem inf_min_le_leftLim (f : DLoc) {t s r : ℝ≥0}
    (hsr : s ≤ r) (hrt : r ≤ t) :
    min (Function.leftLim f.1 s) (futureInf f t s) ≤ Function.leftLim f.1 r := by
  rcases hsr.eq_or_lt with he | hlt
  · subst r
    exact min_le_left _ _
  · have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨s, hlt⟩
    apply ge_of_tendsto (f.2.tendsto_nhdsLT_leftLim r)
    filter_upwards [Ioo_mem_nhdsLT hlt] with v hv
    exact (min_le_right _ _).trans
      (futureInf_le_eval f t s v ⟨(min_le_left _ _).trans hv.1.le, hv.2.le.trans hrt⟩)

/-- The reversed window supremum includes the original left-endpoint jump. -/
theorem supRunning_reversedAt_window_left (f : DLoc) {t s : ℝ≥0} (hst : s ≤ t)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r) :
    supRunning (reversedAt t f) (t - s) =
      f.1 t - min (Function.leftLim f.1 s) (futureInf f t s) := by
  let : Nonempty (Icc (min s t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
  apply le_antisymm
  · apply ciSup_le
    intro u
    change (reversedAt t f).1 u ≤ _
    rw [reversedAt_apply]
    unfold reversedPath
    have hut : (u : ℝ≥0) ≤ t :=
      le_trans (show (u : ℝ≥0) ≤ t - s from u.2) (show t - s ≤ t from tsub_le_self)
    rw [min_eq_left hut]
    apply sub_le_sub_left
    apply inf_min_le_leftLim f _ tsub_le_self
    calc
      s = t - (t - s) := (tsub_tsub_cancel_of_le hst).symm
      _ ≤ t - u := tsub_le_tsub_left (show (u : ℝ≥0) ≤ t - s from u.2) t
  · have hleft : f.1 t - supRunning (reversedAt t f) (t - s) ≤ Function.leftLim f.1 s := by
      have h := eval_le_supRunning (reversedAt t f) (u := t - s) (t := t - s) le_rfl
      rw [reversedAt_apply] at h
      unfold reversedPath at h
      rw [min_eq_left tsub_le_self, tsub_tsub_cancel_of_le hst] at h
      linarith only [h]
    have hinf : f.1 t - supRunning (reversedAt t f) (t - s) ≤ futureInf f t s := by
      apply le_ciInf
      intro v
      have hsv : s ≤ (v : ℝ≥0) := by simpa only [min_eq_left hst] using v.2.1
      have huv : t - (v : ℝ≥0) ≤ t - s := tsub_le_tsub_left hsv t
      have hu := eval_le_supRunning (reversedAt t f) (u := t - v) huv
      rw [reversedAt_apply] at hu
      unfold reversedPath at hu
      rw [min_eq_left tsub_le_self, tsub_tsub_cancel_of_le v.2.2] at hu
      linarith only [hu, hf v]
    have h := le_min hleft hinf
    linarith only [h]

/-- An ancestral time is a supremum contact in the reversed path. -/
theorem supReflected_reversedAt_eq_zero_of_ancestor (f : DLoc) {t s : ℝ≥0} (hst : s ≤ t)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r)
    (hs : Function.leftLim f.1 s ≤ futureInf f t s) :
    supReflected (reversedAt t f) (t - s) = 0 := by
  unfold supReflected
  rw [supRunning_reversedAt_window_left f hst hf, min_eq_left hs, reversedAt_apply]
  unfold reversedPath
  rw [min_eq_left tsub_le_self, tsub_tsub_cancel_of_le hst]
  ring

private theorem supReflected_prefix_add_const {g h : DLoc} {T : ℝ≥0} {c : ℝ}
    (hp : ∀ u : ℝ≥0, u ≤ T → g.1 u = h.1 u + c) {u : ℝ≥0} (hu : u ≤ T) :
    supReflected g u = supReflected h u := by
  have hS : supRunning g u = supRunning h u + c := by
    apply le_antisymm
    · apply supRunning_le
      intro v
      rw [hp v (v.2.trans hu)]
      exact add_le_add (eval_le_supRunning h v.2) le_rfl
    · have hh : supRunning h u ≤ supRunning g u - c := by
        apply supRunning_le
        intro v
        have he := hp v (v.2.trans hu)
        have hg := eval_le_supRunning g v.2
        linarith only [he, hg]
      linarith only [hh]
  unfold supReflected
  rw [hS, hp u hu]
  ring

/-- A constant spatial translation of a prefix preserves its occupation. -/
theorem supOccupation_prefix_add_const {g h : DLoc} {T : ℝ≥0} {c : ℝ}
    (hp : ∀ u : ℝ≥0, u ≤ T → g.1 u = h.1 u + c) (ε : ℝ) :
    supOccupation ε g T = supOccupation ε h T := by
  have he : {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧ supReflected g s.toNNReal < ε} =
      {s : ℝ | 0 ≤ s ∧ s ≤ (T : ℝ) ∧ supReflected h s.toNNReal < ε} := by
    ext s
    constructor
    · rintro ⟨hs0, hsT, hs⟩
      refine ⟨hs0, hsT, ?_⟩
      rwa [supReflected_prefix_add_const hp (Real.toNNReal_le_iff_le_coe.mpr hsT)] at hs
    · rintro ⟨hs0, hsT, hs⟩
      refine ⟨hs0, hsT, ?_⟩
      rwa [supReflected_prefix_add_const hp (Real.toNNReal_le_iff_le_coe.mpr hsT)]
  unfold supOccupation
  rw [he]

private theorem reversedAt_shift_prefix (f : DLoc) {t s : ℝ≥0} (hst : s ≤ t)
    (u : ℝ≥0) (hu : u ≤ s) :
    (reversedAt s f).1 u =
      (DLoc.shift (t - s) (reversedAt t f)).1 u + (f.1 s - Function.leftLim f.1 s) := by
  have hsum : t - s + u ≤ t := by
    calc
      t - s + u ≤ t - s + s := add_le_add le_rfl hu
      _ = t := tsub_add_cancel_of_le hst
  change (reversedAt s f).1 u =
    (reversedAt t f).1 (t - s + u) - (reversedAt t f).1 (t - s) + _
  simp only [reversedAt_apply, reversedPath, min_eq_left hu, min_eq_left hsum,
    min_eq_left (show t - s ≤ t from tsub_le_self), tsub_add_eq_tsub_tsub,
    tsub_tsub_cancel_of_le hst]
  ring

/-- Reversing at an earlier horizon is a translated prefix of the shifted reversal. -/
theorem supOccupation_reversedAt_shift (f : DLoc) {t s : ℝ≥0} (hst : s ≤ t) (ε : ℝ) :
    supOccupation ε (reversedAt s f) s =
      supOccupation ε (DLoc.shift (t - s) (reversedAt t f)) s :=
  supOccupation_prefix_add_const (reversedAt_shift_prefix f hst) ε

/-- At every ancestral time, a convergent reversed clock identifies the earlier height. -/
theorem height_ancestor_clock_identity (θ : ℝ) (f : DLoc) {t s : ℝ≥0} (hst : s ≤ t)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r)
    (hg0 : (reversedAt t f).1 0 = 0)
    (hs : Function.leftLim f.1 s ≤ futureInf f t s)
    (hp : ∀ u : ℝ≥0, u ≤ t →
      Tendsto (fun k => supOccupation (supEps θ k) (reversedAt t f) u) atTop
        (𝓝 (supLocalTime θ (reversedAt t f) u))) :
    Tendsto (fun k => heightApprox (supEps θ k) f s) atTop (𝓝 (height θ f s)) ∧
      height θ f s = supLocalTime θ (reversedAt t f) t -
        supLocalTime θ (reversedAt t f) (t - s) := by
  have hc := supReflected_reversedAt_eq_zero_of_ancestor f hst hf hs
  have he (k : ℕ) : supOccupation (supEps θ k) (reversedAt s f) s =
      supOccupation (supEps θ k) (reversedAt t f) t -
        supOccupation (supEps θ k) (reversedAt t f) (t - s) := by
    rw [supOccupation_reversedAt_shift f hst]
    simpa only [tsub_add_cancel_of_le hst] using
      (supOccupation_shift_of_contact (supEps_pos θ k) hg0 hc s).symm
  have hl := (hp t le_rfl).sub (hp (t - s) tsub_le_self)
  have hr : Tendsto (fun k => supOccupation (supEps θ k) (reversedAt s f) s) atTop
      (𝓝 (supLocalTime θ (reversedAt t f) t - supLocalTime θ (reversedAt t f) (t - s))) :=
    (tendsto_congr he).mpr hl
  have hh : height θ f s = supLocalTime θ (reversedAt t f) t -
      supLocalTime θ (reversedAt t f) (t - s) := hr.limsup_eq
  refine ⟨?_, hh⟩
  rw [hh]
  exact (tendsto_congr (fun k =>
    heightApprox_eq_supOccupation_reversed f hf s (supEps θ k))).mpr hr

/-- For a fixed horizon, all its ancestral times have finite identified height on one event. -/
theorem ae_height_ancestor_fixed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s : ℝ≥0, s ≤ t →
      Function.leftLim f.1 s ≤ futureInf f t s →
      Tendsto (fun k => heightApprox (supEps θ k) f s) atTop (𝓝 (height θ f s)) ∧
        0 ≤ height θ f s ∧
        heightRaw θ f s = ENNReal.ofReal (height θ f s) ∧
        height θ f s = supLocalTime θ (reversedAt t f) t -
          supLocalTime θ (reversedAt t f) (t - s) := by
  filter_upwards [ae_reversed_clock_prefix hθ ht, ae_leftLim_le_stableLocalLaw hθ,
    ae_continuousAt_stableLocalLaw hθ t] with f hg hf htcont
  have hg0 : (reversedAt t f).1 0 = 0 := by
    rw [reversedAt_apply]
    unfold reversedPath
    erw [zero_min, tsub_zero, htcont.continuousWithinAt.leftLim_eq]
    exact sub_self _
  intro s hst hs
  obtain ⟨hc, he⟩ := height_ancestor_clock_identity θ f hst hf hg0 hs hg.1
  have hn : 0 ≤ height θ f s := ge_of_tendsto hc (Eventually.of_forall fun k => by
    unfold heightApprox
    exact mul_nonneg (inv_nonneg.mpr (supEps_pos θ k).le) ENNReal.toReal_nonneg)
  exact ⟨hc, hn, (ENNReal.tendsto_ofReal hc).liminf_eq, he⟩

end BGW.StableTrees
