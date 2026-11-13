/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessConcentration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.Compact
import Mathlib.Topology.Order.IntermediateValue

/-!
# Fixed-time exploration support

The ladder-height transform excludes zero increments, yielding strict increase in level.
Transport on countable dense prefix times and ancestral concentration identify gap-free
exploration support with top equal to the height.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

private theorem measure_supLadderHeight_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {z : ℝ≥0} (hz : 0 < z) :
    (stableLocalLaw θ : Measure DLoc) {f | supLadderHeight θ z f = 0} = 0 := by
  have hb (lam : ℝ) (hlam : 0 ≤ lam) :
      (stableLocalLaw θ : Measure DLoc) {f | supLadderHeight θ z f = 0} ≤
        ENNReal.ofReal (Real.exp (-(z : ℝ) * lam ^ (θ - 1))) := by
    have hi : Integrable (fun f => Real.exp (-lam * supLadderHeight θ z f))
        (stableLocalLaw θ : Measure DLoc) := by
      simpa only [neg_zero, zero_mul, zero_sub, neg_mul] using
        integrable_exp_neg_supLadder hθ (q := 0) (lam := lam) (by norm_num) hlam z
    have hh := hi.measure_le_integral
      (Eventually.of_forall fun f => (Real.exp_pos (-lam * supLadderHeight θ z f)).le)
      (s := {f | supLadderHeight θ z f = 0}) (fun f hf => by
        change supLadderHeight θ z f = 0 at hf
        rw [hf, mul_zero, Real.exp_zero])
    rw [(integral_exp_neg_supLadder hθ z (q := 0) (lam := lam) (by norm_num) hlam).2.2] at hh
    exact hh
  have ht : Tendsto (fun lam : ℝ => ENNReal.ofReal
      (Real.exp (-((z : ℝ) * lam ^ (θ - 1))))) atTop (𝓝 0) := by
    have hp : Tendsto (fun lam : ℝ => (z : ℝ) * lam ^ (θ - 1)) atTop atTop :=
      Tendsto.const_mul_atTop (show (0 : ℝ) < z from hz) (tendsto_rpow_atTop (sub_pos.mpr hθ.1))
    simpa only [Function.comp_def, ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal (Real.tendsto_exp_neg_atTop_nhds_zero.comp hp)
  apply le_antisymm _ zero_le
  apply ge_of_tendsto ht
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with lam hlam
  simpa only [neg_mul] using hb lam hlam

/-- Ladder height increments over a positive deterministic level interval are positive. -/
theorem ae_supLadderHeight_increment_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {y z : ℝ≥0} (hyz : y < z) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), supLadderHeight θ y f < supLadderHeight θ z f := by
  have hpos : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), 0 < supLadderHeight θ (z - y) f := by
    filter_upwards [ae_supLadderPair_path hθ,
      (measure_eq_zero_iff_ae_notMem.mp
        (measure_supLadderHeight_zero hθ (tsub_pos_iff_lt.mpr hyz)))]
      with f hf hne
    exact lt_of_le_of_ne (hf.1 (z - y)).2 (Ne.symm hne)
  have hpair : ∀ᵐ p ∂((stableLocalLaw θ : Measure DLoc).map (supLadderPair θ (z - y))),
      0 < p.2 := by
    apply (ae_map_iff (measurable_supLadderPair θ (z - y)).aemeasurable
      (measurableSet_lt measurable_const measurable_snd)).mpr
    exact hpos
  rw [← map_supLadderIncrement hθ hyz.le] at hpair
  filter_upwards [ae_of_ae_map (measurable_supLadderIncrement θ y z).aemeasurable hpair]
    with f hf
  exact sub_pos.mp hf

/-- The ascending ladder height is strictly increasing on all levels on one event. -/
theorem ae_strictMono_supLadderHeight {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), StrictMono (fun z => supLadderHeight θ z f) := by
  have hq : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ q r : ℚ,
      (q : ℝ).toNNReal < (r : ℝ).toNNReal →
      supLadderHeight θ (q : ℝ).toNNReal f < supLadderHeight θ (r : ℝ).toNNReal f := by
    apply ae_all_iff.mpr
    intro q
    apply ae_all_iff.mpr
    intro r
    by_cases hqr : (q : ℝ).toNNReal < (r : ℝ).toNNReal
    · exact (ae_supLadderHeight_increment_pos hθ hqr).mono (fun _ hf _ => hf)
    · filter_upwards with f
      intro h
      exact (hqr h).elim
  filter_upwards [hq, ae_supLadder_spec hθ] with f hq hf
  have hm : Monotone (fun z => supLadderHeight θ z f) := hf.2.2.2.2.1
  intro y z hyz
  obtain ⟨q, hyq, hqz⟩ := exists_rat_btwn (show (y : ℝ) < z from hyz)
  obtain ⟨r, hqr, hrz⟩ := exists_rat_btwn hqz
  have hq0 : 0 ≤ (q : ℝ) := y.2.trans hyq.le
  have hr0 : 0 ≤ (r : ℝ) := hq0.trans hqr.le
  have hqr' : (q : ℝ).toNNReal < (r : ℝ).toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0, Real.coe_toNNReal _ hr0]
    exact hqr
  have hyq' : y ≤ (q : ℝ).toNNReal := by
    rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
    exact hyq.le
  have hrz' : (r : ℝ).toNNReal ≤ z := Real.toNNReal_le_iff_le_coe.mpr hrz.le
  exact (hm hyq').trans_lt ((hq q r hqr').trans_le (hm hrz'))

/-- Any increase of the supremum clock forces an increase of the running supremum. -/
theorem ae_supRunning_strict_of_clock_lt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s t : ℝ≥0,
      supLocalTime θ f s < supLocalTime θ f t → supRunning f s < supRunning f t := by
  filter_upwards [ae_strictMono_supLadderHeight hθ, ae_supLadder_spec hθ,
    ae_supLocalTime_spec hθ] with f hB hA hM
  intro s t hst
  have hMs : 0 ≤ supLocalTime θ f s := by
    simpa only [hM.1] using hM.2.1 (show (0 : ℝ≥0) ≤ s from zero_le)
  obtain ⟨y, hsy, hyt⟩ := exists_between hst
  obtain ⟨z, hyz, hzt⟩ := exists_between hyt
  let Y : ℝ≥0 := ⟨y, hMs.trans hsy.le⟩
  let Z : ℝ≥0 := ⟨z, (hMs.trans hsy.le).trans hyz.le⟩
  have hsA : s ≤ supLadderTime θ Y f := by
    by_contra hn
    have hh := hM.2.1 (le_of_lt (not_le.mp hn))
    rw [hA.2.2.2.2.2 Y] at hh
    exact (not_le_of_gt hsy) hh
  have hAt : supLadderTime θ Z f ≤ t := by
    by_contra hn
    have hh := hM.2.1 (le_of_lt (not_le.mp hn))
    rw [hA.2.2.2.2.2 Z] at hh
    exact (not_le_of_gt hzt) hh
  exact (monotone_supRunning f hsA).trans_lt
    ((hB (show Y < Z from hyz)).trans_le (monotone_supRunning f hAt))

private theorem prefix_comap_mono {s t : ℝ≥0} (hst : s ≤ t) :
    MeasurableSpace.comap (DLoc.restrict s) inferInstance ≤
      MeasurableSpace.comap (DLoc.restrict t) inferInstance := by
  have hm : Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      (DLoc.restrict s) := by
    have hh : Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
        (fun f => BGW.Skorokhod.restrict (show (s : ℝ) ≤ t from hst) (DLoc.restrict t f)) :=
      (BGW.Skorokhod.measurable_restrict (show (s : ℝ) ≤ t from hst)).comp
        (comap_measurable (DLoc.restrict t))
    convert hh using 1
    funext f
    exact (DLoc.restrict_restrict hst f).symm
  exact hm.comap_le

/-- Strict clock-to-supremum growth transports on any countable family of prefix times. -/
theorem ae_reversed_clock_strict_countable {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {T : ℝ≥0} (hT : 0 < T) (D : Set (Iic T)) (hD : D.Countable) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ u v : D,
      supLocalTime θ (reversedAt T f) u < supLocalTime θ (reversedAt T f) v →
      supRunning (reversedAt T f) u < supRunning (reversedAt T f) v := by
  let : Countable D := hD.to_subtype
  have hm (u : Iic T) :
      Measurable[MeasurableSpace.comap (DLoc.restrict T) inferInstance]
        (fun f : DLoc => supLocalTime θ f u) :=
    (measurable_supLocalTime_prefix θ u).mono (prefix_comap_mono u.2) le_rfl
  have hS (u : Iic T) :
      Measurable[MeasurableSpace.comap (DLoc.restrict T) inferInstance]
        (fun f : DLoc => supRunning f u) :=
    (measurable_supRunning_prefix u).mono (prefix_comap_mono u.2) le_rfl
  have hp : MeasurableSet[MeasurableSpace.comap (DLoc.restrict T) inferInstance]
      {f | ∀ u v : D, supLocalTime θ f u < supLocalTime θ f v →
        supRunning f u < supRunning f v} := by
    let : MeasurableSpace DLoc := MeasurableSpace.comap (DLoc.restrict T) inferInstance
    have hpair (u v : D) : MeasurableSet {f : DLoc |
        supLocalTime θ f u < supLocalTime θ f v → supRunning f u < supRunning f v} := by
      have he : {f : DLoc | supLocalTime θ f u < supLocalTime θ f v →
          supRunning f u < supRunning f v} =
          {f : DLoc | supLocalTime θ f u < supLocalTime θ f v}ᶜ ∪
            {f : DLoc | supRunning f u < supRunning f v} := by
        ext f
        exact imp_iff_not_or
      rw [he]
      exact (measurableSet_lt (hm u) (hm v)).compl.union (measurableSet_lt (hS u) (hS v))
    simpa only [Set.ofPred_forall] using
      MeasurableSet.iInter (fun u : D => MeasurableSet.iInter (fun v : D => hpair u v))
  apply ae_reversedAt_of_prefix hθ hT hp
  filter_upwards [ae_supRunning_strict_of_clock_lt hθ] with f hf
  intro u v huv
  exact hf u v huv

/-- **No gaps, fixed-time version** (`∀ t` outside the a.e. binder; kept for reference). -/
theorem ae_support_gapfree_fixed {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ h : ℝ≥0, (h : ℝ) < height θ f t →
      ∀ ε : ℝ, 0 < ε → 0 < exploration θ f t (Metric.ball h ε) := by
  by_cases ht : t = 0
  · subst t
    filter_upwards with f
    intro h hh
    rw [height_zero] at hh
    exact ((not_lt_of_ge h.2) hh).elim
  have htpos : 0 < t := pos_iff_ne_zero.mpr ht
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Iic t)
  let : Countable D := hDc.to_subtype
  have hcd : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ u : D,
      ContinuousAt f.1 (t - (u : Iic t)) :=
    ae_all_iff.mpr (fun u => ae_continuousAt_stableLocalLaw hθ (t - (u : Iic t)))
  filter_upwards [ae_reversed_clock_prefix hθ htpos, ae_height_ancestor_fixed hθ htpos,
    ae_reversed_clock_strict_countable hθ htpos D hDc, hcd, ae_leftLim_le_stableLocalLaw hθ]
    with f hg ha hstrict hcont hf
  let g := reversedAt t f
  let m : C(Iic t, ℝ) := ⟨fun u => supLocalTime θ g u, hg.2.1⟩
  let H := height θ f t
  let t0 : Iic t := ⟨0, show (0 : ℝ≥0) ≤ t from zero_le⟩
  let tt : Iic t := ⟨t, show t ≤ t from le_rfl⟩
  have hm0 : m t0 = 0 := hg.2.2.2
  have hmT : m tt = H := rfl
  intro h hh ε hε
  let a := max 0 (H - (h : ℝ) - ε / 2)
  let b := min H (H - (h : ℝ) + ε / 2)
  have hnonh : (0 : ℝ) ≤ h := h.2
  have hH : 0 < H := hnonh.trans_lt hh
  have hab : a < b := by
    apply max_lt_iff.mpr
    constructor
    · exact lt_min hH (by dsimp [H] at *; linarith only [hh, hnonh, hε])
    · apply lt_min <;> linarith only [hnonh, hε]
  have ha0 : 0 ≤ a := le_max_left _ _
  have hbH : b ≤ H := min_le_left _ _
  have hdense (x y : ℝ) (hx : 0 ≤ x) (hy : y ≤ H) (hxy : x < y) :
      ∃ u ∈ D, x < m u ∧ m u < y := by
    let inc : ℝ≥0 → Iic t := fun u => ⟨min u t, show min u t ≤ t from min_le_right _ _⟩
    have hinc : Continuous inc := Continuous.subtype_mk
      (continuous_id.min continuous_const) (fun u => show min u t ≤ t from min_le_right _ _)
    have hz : m (inc 0) = 0 := by simpa only [inc, zero_min] using hm0
    have htop : m (inc t) = H := by simpa only [inc, min_self] using hmT
    have hiv := intermediate_value_Icc (show (0 : ℝ≥0) ≤ t from zero_le)
      (m.continuous.comp hinc).continuousOn
    have hval : (x + y) / 2 ∈ Icc (m (inc 0)) (m (inc t)) := by
      rw [hz, htop]
      constructor <;> linarith only [hx, hy, hxy]
    obtain ⟨u, _hu, hmu⟩ := hiv hval
    dsimp only [Function.comp_def] at hmu
    have hO : IsOpen {u : Iic t | x < m u ∧ m u < y} :=
      (isOpen_lt continuous_const m.continuous).inter (isOpen_lt m.continuous continuous_const)
    obtain ⟨v, hvD, hv⟩ := hDd.exists_mem_open hO ⟨inc u, by
      change x < m (inc u) ∧ m (inc u) < y
      rw [hmu]
      constructor <;> linarith only [hxy]⟩
    exact ⟨v, hvD, hv⟩
  obtain ⟨k, hkD, hk⟩ := hdense a ((a + b) / 2) ha0
    (by linarith only [hab, hbH]) (by linarith only [hab])
  obtain ⟨l, hlD, hl⟩ := hdense ((a + b) / 2) b
    (by linarith only [ha0, hab]) hbH (by linarith only [hab])
  have hmkml : m k < m l := hk.2.trans hl.1
  have hkl : k < l := lt_of_not_ge (fun hle => (not_le_of_gt hmkml) (hg.2.2.1 hle))
  have hlt : (l : ℝ≥0) < t := lt_of_le_of_ne l.2 (by
    intro he
    have hml : m l = H := by
      have hltop : l = tt := Subtype.ext he
      rw [hltop]
      exact hmT
    linarith only [hl.2, hbH, hml])
  have hS : supRunning g k < supRunning g l := hstrict ⟨k, hkD⟩ ⟨l, hlD⟩ hmkml
  let A : Set ℝ := Ioc ((t - (l : ℝ≥0) : ℝ≥0) : ℝ) ((t - (k : ℝ≥0) : ℝ≥0) : ℝ)
  let μ := (explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ))
  have hAsub : A ⊆ Ioc 0 (t : ℝ) := by
    intro s hs
    have ha : (0 : ℝ) < (t - (l : ℝ≥0) : ℝ≥0) := tsub_pos_iff_lt.mpr hlt
    have hb : ((t - (k : ℝ≥0) : ℝ≥0) : ℝ) ≤ t := by
      exact_mod_cast (show t - (k : ℝ≥0) ≤ t from tsub_le_self)
    exact ⟨ha.trans hs.1, hs.2.trans hb⟩
  have hF (x : ℝ) : explorationStieltjes f t x = futureInfFun f t x := by
    simp only [explorationStieltjes, dite_eq_left (explorationStieltjes_spec f t)]
  have hkF : futureInf f t (t - (k : ℝ≥0)) = f.1 t - supRunning g k := by
    have he := supRunning_reversedAt_window f
      (s := t - (k : ℝ≥0)) tsub_le_self hf
      (hcont ⟨k, hkD⟩).continuousWithinAt.leftLim_eq
    erw [tsub_tsub_cancel_of_le (show (k : ℝ≥0) ≤ t from k.2)] at he
    linarith only [he]
  have hlF : futureInf f t (t - (l : ℝ≥0)) = f.1 t - supRunning g l := by
    have he := supRunning_reversedAt_window f
      (s := t - (l : ℝ≥0)) tsub_le_self hf
      (hcont ⟨l, hlD⟩).continuousWithinAt.leftLim_eq
    erw [tsub_tsub_cancel_of_le (show (l : ℝ≥0) ≤ t from l.2)] at he
    linarith only [he]
  have hmass : μ A = ENNReal.ofReal (supRunning g l - supRunning g k) := by
    change ((explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ)))
      (Ioc ((t - (l : ℝ≥0) : ℝ≥0) : ℝ) ((t - (k : ℝ≥0) : ℝ≥0) : ℝ)) = _
    rw [Measure.restrict_apply measurableSet_Ioc, inter_eq_left.mpr hAsub,
      StieltjesFunction.measure_Ioc, hF, hF]
    simp only [futureInfFun, Real.toNNReal_coe]
    rw [hkF, hlF]
    congr 1
    ring
  have hmasspos : 0 < μ A := by rw [hmass]; exact ENNReal.ofReal_pos.mpr (sub_pos.mpr hS)
  rw [exploration, Measure.map_apply (measurable_exploration_heightMap θ f) measurableSet_ball]
  apply hmasspos.trans_le
  apply measure_mono_ae
  filter_upwards [ae_exploration_ancestral_times f hf t, ae_restrict_mem measurableSet_Ioc]
    with s hs hst
  intro hsA
  have hst' : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hst.2
  have hc := ha s.toNNReal hst' hs
  have hsa : t - (l : ℝ≥0) < s.toNNReal := by
    rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hst.1.le]
    exact hsA.1
  have hsb : s.toNNReal ≤ t - (k : ℝ≥0) := Real.toNNReal_le_iff_le_coe.mpr hsA.2
  have hkv : (k : ℝ≥0) ≤ t - s.toNNReal := by
    calc
      (k : ℝ≥0) = t - (t - (k : ℝ≥0)) := (tsub_tsub_cancel_of_le (show (k : ℝ≥0) ≤ t from k.2)).symm
      _ ≤ t - s.toNNReal := tsub_le_tsub_left hsb t
  have hvl : t - s.toNNReal ≤ (l : ℝ≥0) := by
    calc
      t - s.toNNReal ≤ t - (t - (l : ℝ≥0)) := tsub_le_tsub_left hsa.le t
      _ = l := tsub_tsub_cancel_of_le (show (l : ℝ≥0) ≤ t from l.2)
  let v : Iic t := ⟨t - s.toNNReal, show t - s.toNNReal ≤ t from tsub_le_self⟩
  have hmvk : m k ≤ m v := hg.2.2.1 (show k ≤ v from hkv)
  have hmvl : m v ≤ m l := hg.2.2.1 (show v ≤ l from hvl)
  have he : height θ f s.toNNReal = H - m v := hc.2.2.2
  change |((height θ f s.toNNReal).toNNReal : ℝ) - (h : ℝ)| < ε
  rw [Real.coe_toNNReal _ hc.2.1, he]
  apply abs_lt.mpr
  have haW : H - (h : ℝ) - ε / 2 ≤ a := le_max_right _ _
  have hbW : b ≤ H - (h : ℝ) + ε / 2 := min_le_right _ _
  constructor <;> linarith only [hk.1, hl.2, hmvk, hmvl, haW, hbW, hε]

/-- A point of the support lies below any bound beyond which the measure has no mass. -/
theorem support_le_of_mass_above_zero {ρ : Measure ℝ≥0} {R : ℝ≥0}
    (hρ : ρ (Ioi R) = 0) {h : ℝ≥0}
    (hh : ∀ ε : ℝ, 0 < ε → 0 < ρ (Metric.ball h ε)) : h ≤ R := by
  by_contra hn
  have hRh : (R : ℝ) < h := not_le.mp hn
  let ε : ℝ := ((h : ℝ) - R) / 2
  have hε : 0 < ε := half_pos (sub_pos.mpr hRh)
  have hsub : Metric.ball h ε ⊆ Ioi R := by
    intro x hx
    have hx' : |(x : ℝ) - (h : ℝ)| < ε := hx
    have hhx := (abs_lt.mp hx').1
    change (R : ℝ) < x
    dsimp [ε] at hhx
    linarith only [hhx, hRh]
  have hz := measure_mono_null hsub hρ
  have hp := hh ε hε
  rw [hz] at hp
  exact (lt_irrefl 0) hp

/-- **Support reaches the height**, fixed `t`: a.s. the top of the support of `ρ_t` is `H_t`. -/
theorem ae_topHeight_exploration {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (topHeight (exploration θ f t) : ℝ) = height θ f t := by
  filter_upwards [ae_support_gapfree_fixed hθ t, ae_exploration_above_height hθ t,
    ae_heightRaw_eq hθ t] with f hgap habove hfinite
  let ρ := exploration θ f t
  let R := (height θ f t).toNNReal
  have hR : (R : ℝ) = height θ f t := Real.coe_toNNReal _ hfinite.1
  have hb : ∀ h ∈ {h : ℝ≥0 | ∀ ε : ℝ, 0 < ε → 0 < ρ (Metric.ball h ε)}, h ≤ R :=
    fun _ hh => support_le_of_mass_above_zero habove hh
  have hupper : topHeight ρ ≤ R := csSup_le' hb
  have hlower : R ≤ topHeight ρ := by
    by_contra hn
    have htR : (topHeight ρ : ℝ) < (R : ℝ) := NNReal.coe_lt_coe.mpr (not_le.mp hn)
    let u : ℝ≥0 := ⟨((topHeight ρ : ℝ) + R) / 2, by positivity⟩
    have huR : (u : ℝ) < height θ f t := by
      change ((topHeight ρ : ℝ) + R) / 2 < _
      rw [← hR]
      linarith only [htR]
    have hu : ∀ ε : ℝ, 0 < ε → 0 < ρ (Metric.ball u ε) := hgap u huR
    have hule : u ≤ topHeight ρ := le_csSup ⟨R, hb⟩ hu
    have htu : (topHeight ρ : ℝ) < u := by
      change (topHeight ρ : ℝ) < ((topHeight ρ : ℝ) + R) / 2
      linarith only [htR]
    exact (not_lt_of_ge (NNReal.coe_le_coe.mpr hule)) htu
  exact (congrArg (fun x : ℝ≥0 => (x : ℝ)) (le_antisymm hupper hlower)).trans hR

end BGW.StableTrees
