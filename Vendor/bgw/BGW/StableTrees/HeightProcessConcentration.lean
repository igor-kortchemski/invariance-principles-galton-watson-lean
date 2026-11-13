/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessRecords
import BGW.StableTrees.StableExcursionSupportOccupation

/-!
# Ancestral concentration of the exploration measure

The Stieltjes measure is carried by ancestral times: outside that set the future infimum
is locally constant. The fixed-horizon clock identity then bounds the heights seen by that
measure. Fixed-time positivity also identifies the zero-height event.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

private theorem futureInf_eq_of_lower_window (f : DLoc) {t a b : ℝ≥0}
    (hab : a ≤ b) (hbt : b ≤ t)
    (hgap : ∀ u ∈ Icc a b, futureInf f t b ≤ f.1 u) :
    futureInf f t a = futureInf f t b := by
  let : Nonempty (Icc (min a t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
  apply le_antisymm (monotone_futureInf f t hab)
  apply le_ciInf
  intro u
  have hau : a ≤ (u : ℝ≥0) := by
    simpa only [min_eq_left (hab.trans hbt)] using u.2.1
  by_cases hub : (u : ℝ≥0) ≤ b
  · exact hgap u ⟨hau, hub⟩
  · exact futureInf_le_eval f t b u ⟨(min_le_left _ _).trans (le_of_not_ge hub), u.2.2⟩

private theorem exists_flat_rational_window (f : DLoc)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r) {t : ℝ≥0} {s : ℝ}
    (hs0 : 0 < s) (hst : s ≤ (t : ℝ))
    (hbad : futureInf f t s.toNNReal < Function.leftLim f.1 s.toNNReal) :
    ∃ p q : ℚ, (p : ℝ) < s ∧ s < (q : ℝ) ∧
      futureInfFun f t p = futureInfFun f t q := by
  let x := s.toNNReal
  have hxt : x ≤ t := Real.toNNReal_le_iff_le_coe.mpr hst
  obtain ⟨a, hIa, ha⟩ := exists_between hbad
  have hax : a < f.1 x := ha.trans_le (hf x)
  have hne : Nonempty (Icc (min x t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
  let := hne
  obtain ⟨v, hv⟩ := (ciInf_lt_iff (futureInf_bddBelow f t x)).mp hIa
  have hxv : x < (v : ℝ≥0) := by
    have hle : x ≤ (v : ℝ≥0) := by simpa only [min_eq_left hxt] using v.2.1
    by_contra hn
    have he : (v : ℝ≥0) = x := le_antisymm (le_of_not_gt hn) hle
    rw [he] at hv
    exact (not_lt_of_gt hax) hv
  have hnear : ∀ᶠ r in 𝓝 x, a < f.1 r := by
    rw [← nhdsLT_sup_nhdsGE x, eventually_sup]
    constructor
    · exact (f.2.tendsto_nhdsLT_leftLim x).eventually (eventually_gt_nhds ha)
    · have hr := continuousWithinAt_Ioi_iff_Ici.mp (f.2.isRightContinuous x)
      exact hr.eventually (eventually_gt_nhds hax)
  have hnearR : ∀ᶠ r : ℝ in 𝓝 s, a < f.1 r.toNNReal :=
    (continuous_real_toNNReal.tendsto s).eventually hnear
  have hsv : s < ((v : ℝ≥0) : ℝ) := by
    have hh := NNReal.coe_lt_coe.mpr hxv
    simpa only [x, Real.coe_toNNReal _ hs0.le] using hh
  obtain ⟨l, r, hslr, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp
    (inter_mem hnearR (Ioo_mem_nhds hs0 hsv))
  obtain ⟨p, hlp, hps⟩ := exists_rat_btwn hslr.1
  obtain ⟨q, hsq, hqr⟩ := exists_rat_btwn hslr.2
  have hwin (u : ℝ) (hu : u ∈ Icc (p : ℝ) (q : ℝ)) :
      a < f.1 u.toNNReal ∧ 0 < u ∧ u < ((v : ℝ≥0) : ℝ) :=
    hsub ⟨hlp.trans_le hu.1, hu.2.trans_lt hqr⟩
  have hp0 : 0 ≤ (p : ℝ) := (hwin p ⟨le_rfl, hps.le.trans hsq.le⟩).2.1.le
  have hq0 : 0 ≤ (q : ℝ) := (hwin q ⟨hps.le.trans hsq.le, le_rfl⟩).2.1.le
  have hpq : (p : ℝ).toNNReal ≤ (q : ℝ).toNNReal := Real.toNNReal_mono (hps.le.trans hsq.le)
  have hqv : (q : ℝ).toNNReal ≤ (v : ℝ≥0) :=
    Real.toNNReal_le_iff_le_coe.mpr (hwin q ⟨hps.le.trans hsq.le, le_rfl⟩).2.2.le
  have hqb : futureInf f t (q : ℝ).toNNReal < a :=
    (futureInf_le_eval f t (q : ℝ).toNNReal v
      ⟨(min_le_left _ _).trans hqv, v.2.2⟩).trans_lt hv
  refine ⟨p, q, hps, hsq, ?_⟩
  apply futureInf_eq_of_lower_window f hpq (hqv.trans v.2.2)
  intro u hu
  have hpu : (p : ℝ) ≤ (u : ℝ) := by
    have hh := NNReal.coe_le_coe.mpr hu.1
    simpa only [Real.coe_toNNReal _ hp0] using hh
  have huq : (u : ℝ) ≤ (q : ℝ) := by
    have hh := NNReal.coe_le_coe.mpr hu.2
    simpa only [Real.coe_toNNReal _ hq0] using hh
  have hx := (hwin u ⟨hpu, huq⟩).1
  simp only [Real.toNNReal_coe] at hx
  exact hqb.le.trans hx.le

/-- The exploration Stieltjes measure is carried by ancestral times, including endpoint atoms. -/
theorem ae_exploration_ancestral_times (f : DLoc)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r) (t : ℝ≥0) :
    ∀ᵐ s ∂((explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ))),
      Function.leftLim f.1 s.toNNReal ≤ futureInf f t s.toNNReal := by
  let Q := {p : ℚ × ℚ // futureInfFun f t p.1 = futureInfFun f t p.2}
  have hnull (p : Q) :
      (explorationStieltjes f t).measure (Ioo (p.1.1 : ℝ) (p.1.2 : ℝ)) = 0 := by
    apply measure_mono_null Ioo_subset_Ioc_self
    rw [StieltjesFunction.measure_Ioc]
    have hF (x : ℝ) : explorationStieltjes f t x = futureInfFun f t x := by
      simp only [explorationStieltjes, dite_eq_left (explorationStieltjes_spec f t)]
    rw [hF, hF, p.2, sub_self, ENNReal.ofReal_zero]
  rw [ae_iff, Measure.restrict_apply' measurableSet_Ioc]
  apply measure_mono_null (t := ⋃ p : Q, Ioo (p.1.1 : ℝ) (p.1.2 : ℝ)) _
    (measure_iUnion_null hnull)
  rintro s ⟨hsbad, hs0, hst⟩
  obtain ⟨p, q, hps, hsq, he⟩ := exists_flat_rational_window f hf hs0 hst (not_le.mp hsbad)
  exact mem_iUnion.mpr ⟨⟨(p, q), he⟩, hps, hsq⟩

/-- At a fixed horizon, the Stieltjes measure sees finite ancestral heights below the endpoint. -/
theorem ae_exploration_height_bounds {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ᵐ s ∂((explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ))),
        0 ≤ height θ f s.toNNReal ∧ height θ f s.toNNReal ≤ height θ f t ∧
          heightRaw θ f s.toNNReal = ENNReal.ofReal (height θ f s.toNNReal) := by
  by_cases ht : t = 0
  · subst t
    filter_upwards with f
    simp
  filter_upwards [ae_height_ancestor_fixed hθ (pos_iff_ne_zero.mpr ht),
    ae_reversed_clock_prefix hθ (pos_iff_ne_zero.mpr ht), ae_leftLim_le_stableLocalLaw hθ]
    with f ha hg hf
  filter_upwards [ae_exploration_ancestral_times f hf t, ae_restrict_mem measurableSet_Ioc]
    with s hs hst
  have hst' : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hst.2
  have hc := ha s.toNNReal hst' hs
  have hM : 0 ≤ supLocalTime θ (reversedAt t f) (t - s.toNNReal) := by
    have hh := hg.2.2.1 (show (⟨0, show (0 : ℝ≥0) ≤ t from zero_le⟩ : Iic t) ≤
      ⟨t - s.toNNReal, show t - s.toNNReal ≤ t from tsub_le_self⟩ by
        change (0 : ℝ≥0) ≤ t - s.toNNReal
        exact zero_le)
    change supLocalTime θ (reversedAt t f) 0 ≤
      supLocalTime θ (reversedAt t f) (t - s.toNNReal) at hh
    rw [hg.2.2.2] at hh
    exact hh
  refine ⟨hc.2.1, ?_, hc.2.2.1⟩
  change height θ f s.toNNReal ≤ supLocalTime θ (reversedAt t f) t
  rw [hc.2.2.2]
  exact sub_le_self _ hM

/-- **Upper support bound** (fixed `t`): a.s. `ρ_t` puts no mass above `H_t` (excludes the
unbounded-support junk of `topHeight`). -/
theorem ae_exploration_above_height {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      exploration θ f t (Ioi (height θ f t).toNNReal) = 0 := by
  filter_upwards [ae_exploration_height_bounds hθ t] with f hf
  rw [exploration, Measure.map_apply (measurable_exploration_heightMap θ f) measurableSet_Ioi]
  apply measure_eq_zero_iff_ae_notMem.mpr
  filter_upwards [hf] with s hs
  intro hmem
  exact (not_lt_of_ge (Real.toNNReal_mono hs.2.1)) hmem

/-- At each fixed positive time, the height is almost surely positive. -/
theorem ae_height_pos_fixed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), 0 < height θ f t := by
  have hp : MeasurableSet[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      {f | 0 < supLocalTime θ f t} := by
    let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict t) inferInstance
    exact measurableSet_lt measurable_const (measurable_supLocalTime_prefix θ t)
  exact ae_reversedAt_of_prefix hθ ht hp
    ((ae_supLocalTime_pos hθ).mono fun _ hf => hf t ht)

/-- The future infimum from zero is the existing running infimum. -/
theorem futureInf_zero_eq_runningInf (f : DLoc) (t : ℝ≥0) :
    futureInf f t 0 = runningInfLoc f t := by
  let : Nonempty (Icc (min (0 : ℝ≥0) t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
  apply le_antisymm
  · apply le_runningInfLoc
    intro u
    exact futureInf_le_eval f t 0 u ⟨by simp only [zero_min]; exact zero_le, u.2⟩
  · apply le_ciInf
    intro u
    exact runningInfLoc_le_eval f t ⟨u, u.2.2⟩

/-- **Height zero iff reflected zero** (fixed `t` only): a.s. `H_t = 0 ↔ X_t = I_t`, i.e.
`ρ_t = 0`.  The all-`t` version needs ancestral local-time regularity (H03). -/
theorem ae_height_zero_iff {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (height θ f t = 0 ↔ f.1 t = futureInf f t 0) := by
  by_cases ht : t = 0
  · subst t
    filter_upwards with f
    simp only [height_zero, futureInf_self]
  filter_upwards [ae_height_pos_fixed hθ (pos_iff_ne_zero.mpr ht),
    ae_reflected_pos_fixed hθ (pos_iff_ne_zero.mpr ht), ae_eval_zero_stableLocalLaw hθ]
    with f hh hr hf0
  rw [reflectedFrom_zero_apply hf0, ← futureInf_zero_eq_runningInf] at hr
  constructor
  · intro he
    exact ((ne_of_gt hh) he).elim
  · intro he
    rw [he, sub_self] at hr
    exact (lt_irrefl 0 hr).elim

end BGW.StableTrees
