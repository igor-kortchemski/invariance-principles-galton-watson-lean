/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessRestartSource
public import BGW.StableTrees.HeightBridgesExcursionMoment
public import BGW.StableTrees.HeightBridgesAgeMeasure
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Measure.Prod

/-!
# First moments of the height occupation near the excursion start

Translation of Lebesgue measure identifies the approximation on the later window, and the
difference is exactly the occupation before the split age. Tonelli converts the error from
deleting an initial age window into the integral of the small-depth probabilities.
No pathwise sequence identification is required.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Splitting the approximation leaves precisely its occupation before the split age. -/
theorem heightApprox_sub_shift_eq (ε : ℝ) (f : DLoc) (t a : ℝ≥0) (hat : a ≤ t) :
    heightApprox ε f t - heightApprox ε (DLoc.shift a f) (t - a) =
      ε⁻¹ * (volume {s : ℝ | 0 ≤ s ∧ s < (a : ℝ) ∧
        f.1 s.toNNReal < futureInf f t s.toNNReal + ε}).toReal := by
  let r := t - a
  have har : a + r = t := add_tsub_cancel_of_le hat
  let E : Set ℝ := {s | 0 ≤ s ∧ s < (a : ℝ) ∧
    f.1 s.toNNReal < futureInf f t s.toNNReal + ε}
  let F : Set ℝ := {s | (a : ℝ) ≤ s ∧ s ≤ (t : ℝ) ∧
    f.1 s.toNNReal < futureInf f t s.toNNReal + ε}
  let A : Set ℝ := {s | 0 ≤ s ∧ s ≤ (t : ℝ) ∧
    f.1 s.toNNReal < futureInf f t s.toNNReal + ε}
  let B : Set ℝ := {u | 0 ≤ u ∧ u ≤ (r : ℝ) ∧
    (DLoc.shift a f).1 u.toNNReal < futureInf (DLoc.shift a f) r u.toNNReal + ε}
  have hmarg : MeasurableSet {s : ℝ |
      f.1 s.toNNReal < futureInf f t s.toNNReal + ε} :=
    measurableSet_lt
      (DLoc.measurable_eval₂.comp (measurable_const.prodMk measurable_real_toNNReal))
      ((measurable_futureInf_uncurry.comp
        ((measurable_const.prodMk measurable_real_toNNReal).prodMk measurable_const)).add
          measurable_const)
  have hFmeas : MeasurableSet F :=
    (measurableSet_le measurable_const measurable_id).inter
      ((measurableSet_le measurable_id measurable_const).inter hmarg)
  have hEfin : volume E ≠ ⊤ := ne_top_of_le_ne_top
    (show volume (Icc (0 : ℝ) (a : ℝ)) ≠ ⊤ by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
    (measure_mono (show E ⊆ Icc (0 : ℝ) a from fun _ h => ⟨h.1, h.2.1.le⟩))
  have hFfin : volume F ≠ ⊤ := ne_top_of_le_ne_top
    (show volume (Icc (0 : ℝ) (t : ℝ)) ≠ ⊤ by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)
    (measure_mono (show F ⊆ Icc (0 : ℝ) t from fun _ h => ⟨a.2.trans h.1, h.2.1⟩))
  have hsplit : A = E ∪ F := by
    ext s
    dsimp [A, E, F]
    constructor
    · rintro ⟨hs, hst, hmargin⟩
      exact (lt_or_ge s a).elim (fun h => Or.inl ⟨hs, h, hmargin⟩)
        (fun h => Or.inr ⟨h, hst, hmargin⟩)
    · rintro (⟨hs, hsa, hm⟩ | ⟨has, hst, hm⟩)
      · exact ⟨hs, hsa.le.trans hat, hm⟩
      · exact ⟨a.2.trans has, hst, hm⟩
  have hdisj : Disjoint E F := by
    apply disjoint_left.mpr
    intro s hs ht
    exact (not_lt_of_ge ht.1) hs.2.1
  have htrans : B = (fun u : ℝ => (a : ℝ) + u) ⁻¹' F := by
    ext u
    simp only [mem_preimage]
    by_cases hu : 0 ≤ u
    · have hsum : ((a : ℝ) + u).toNNReal = a + u.toNNReal := by
        apply NNReal.coe_injective
        change max ((a : ℝ) + u) 0 = (a : ℝ) + max u 0
        have hnonneg : (0 : ℝ) ≤ (a : ℝ) + u := add_nonneg a.2 hu
        exact (max_eq_left hnonneg).trans
          (congrArg (fun z : ℝ => (a : ℝ) + z) (max_eq_left hu)).symm
      have hrt : (a : ℝ) + (r : ℝ) = t := by exact_mod_cast har
      constructor
      · rintro ⟨_, hur, hmargin⟩
        have hur' : u.toNNReal ≤ r := Real.toNNReal_le_iff_le_coe.mpr hur
        have hI := futureInf_shift_window f a r hur'
        rw [har] at hI
        refine ⟨by linarith, by linarith, ?_⟩
        rw [hsum, hI]
        change f.1 (a + u.toNNReal) - f.1 a < _ at hmargin
        linarith only [hmargin]
      · rintro ⟨_, hut, hmargin⟩
        have hur : u ≤ (r : ℝ) := by linarith only [hut, hrt]
        have hur' : u.toNNReal ≤ r := Real.toNNReal_le_iff_le_coe.mpr hur
        have hI := futureInf_shift_window f a r hur'
        rw [har] at hI
        rw [hsum, hI] at hmargin
        refine ⟨hu, hur, ?_⟩
        change f.1 (a + u.toNNReal) - f.1 a < _
        linarith only [hmargin]
    · have hlu : (a : ℝ) + u < a := by linarith
      simp only [B, F, mem_ofPred_eq]
      exact iff_of_false (fun h => hu h.1) (fun h => not_le_of_gt hlu h.1)
  have hvol : volume B = volume F := by rw [htrans, measure_preimage_add]
  change ε⁻¹ * (volume A).toReal - ε⁻¹ * (volume B).toReal = ε⁻¹ * (volume E).toReal
  rw [hvol, hsplit, measure_union hdisj hFmeas, ENNReal.toReal_add hEfin hFfin]
  ring

/-- Tonelli's identity for the error from deleting the initial occupation window. -/
theorem lintegral_heightApprox_sub_shift (μ : Measure Excursion) [SFinite μ]
    (ε : ℝ) (hε : 0 < ε) (t a : ℝ≥0) (hat : a ≤ t) :
    (∫⁻ e, ENNReal.ofReal
      |heightApprox ε e.path t - heightApprox ε (DLoc.shift a e.path) (t - a)| ∂μ) =
    ENNReal.ofReal ε⁻¹ * ∫⁻ s in Ico (0 : ℝ) (a : ℝ),
      μ {e | e.path.1 s.toNNReal < futureInf e.path t s.toNNReal + ε} := by
  let R : Set (ℝ × Excursion) := {p | 0 ≤ p.1 ∧ p.1 < (a : ℝ) ∧
    p.2.path.1 p.1.toNNReal < futureInf p.2.path t p.1.toNNReal + ε}
  have hmargin : MeasurableSet {p : ℝ × Excursion |
      p.2.path.1 p.1.toNNReal < futureInf p.2.path t p.1.toNNReal + ε} :=
    measurableSet_lt
      (DLoc.measurable_eval₂.comp ((measurable_excursion_path.comp measurable_snd).prodMk
        (measurable_real_toNNReal.comp measurable_fst)))
      ((measurable_futureInf_uncurry.comp
        ((measurable_const.prodMk (measurable_real_toNNReal.comp measurable_fst)).prodMk
          (measurable_excursion_path.comp measurable_snd))).add measurable_const)
  have hR : MeasurableSet R :=
    (measurableSet_le measurable_const measurable_fst).inter
      ((measurableSet_lt measurable_fst measurable_const).inter hmargin)
  have hswap : Measurable (fun p : Excursion × ℝ => R.indicator (fun _ => (1 : ℝ≥0∞))
      (p.2, p.1)) := (measurable_const.indicator hR).comp measurable_swap
  have he (e : Excursion) : ENNReal.ofReal
      |heightApprox ε e.path t - heightApprox ε (DLoc.shift a e.path) (t - a)| =
      ENNReal.ofReal ε⁻¹ * ∫⁻ s : ℝ, R.indicator (fun _ => (1 : ℝ≥0∞)) (s, e) := by
    have hsec : MeasurableSet {s : ℝ | (s, e) ∈ R} :=
      (measurable_id.prodMk measurable_const) hR
    have hfin : volume {s : ℝ | (s, e) ∈ R} ≠ ⊤ := ne_top_of_le_ne_top
      (show volume (Icc (0 : ℝ) (a : ℝ)) ≠ ⊤ by
        rw [Real.volume_Icc]
        exact ENNReal.ofReal_ne_top)
      (measure_mono (show {s : ℝ | (s, e) ∈ R} ⊆ Icc (0 : ℝ) a from
        fun _ h => ⟨h.1, h.2.1.le⟩))
    have hn : 0 ≤ ε⁻¹ * (volume {s : ℝ | (s, e) ∈ R}).toReal :=
      mul_nonneg (inv_nonneg.mpr hε.le) ENNReal.toReal_nonneg
    rw [heightApprox_sub_shift_eq ε e.path t a hat]
    change ENNReal.ofReal |ε⁻¹ * (volume {s : ℝ | (s, e) ∈ R}).toReal| = _
    rw [abs_of_nonneg hn, ENNReal.ofReal_mul (inv_nonneg.mpr hε.le)]
    congr 1
    rw [ENNReal.ofReal_toReal hfin]
    exact (lintegral_indicator_one hsec).symm
  have hinner (s : ℝ) : (∫⁻ e, R.indicator (fun _ => (1 : ℝ≥0∞)) (s, e) ∂μ) =
      (Ico (0 : ℝ) (a : ℝ)).indicator
        (fun s => μ {e | e.path.1 s.toNNReal < futureInf e.path t s.toNNReal + ε}) s := by
    by_cases hs : s ∈ Ico (0 : ℝ) (a : ℝ)
    · rw [Set.indicator_of_mem hs]
      have hsec : MeasurableSet {e : Excursion |
          e.path.1 s.toNNReal < futureInf e.path t s.toNNReal + ε} :=
        (show Measurable (fun e : Excursion => (s, e)) from
          measurable_const.prodMk measurable_id) hmargin
      convert lintegral_indicator_one hsec using 1
      apply lintegral_congr
      intro e
      by_cases hm : e.path.1 s.toNNReal < futureInf e.path t s.toNNReal + ε
      · exact (Set.indicator_of_mem (show (s, e) ∈ R from ⟨hs.1, hs.2, hm⟩) _).trans
          (Set.indicator_of_mem (show e ∈ {e : Excursion |
            e.path.1 s.toNNReal < futureInf e.path t s.toNNReal + ε} from hm)
              (fun _ : Excursion => (1 : ℝ≥0∞))).symm
      · exact (Set.indicator_of_notMem (fun h => hm h.2.2) _).trans
          (Set.indicator_of_notMem (show e ∉ {e : Excursion |
            e.path.1 s.toNNReal < futureInf e.path t s.toNNReal + ε} from hm)
              (fun _ : Excursion => (1 : ℝ≥0∞))).symm
    · rw [Set.indicator_of_notMem hs]
      apply lintegral_eq_zero_of_ae_eq_zero
      filter_upwards with e
      exact Set.indicator_of_notMem (fun h => hs ⟨h.1, h.2.1⟩) _
  calc
    _ = ∫⁻ e, ENNReal.ofReal ε⁻¹ *
        (∫⁻ s : ℝ, R.indicator (fun _ => (1 : ℝ≥0∞)) (s, e)) ∂μ := lintegral_congr he
    _ = ENNReal.ofReal ε⁻¹ *
        ∫⁻ e, (∫⁻ s : ℝ, R.indicator (fun _ => (1 : ℝ≥0∞)) (s, e)) ∂μ :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal ε⁻¹ *
        ∫⁻ s : ℝ, ∫⁻ e, R.indicator (fun _ => (1 : ℝ≥0∞)) (s, e) ∂μ :=
      congrArg (fun z : ℝ≥0∞ => ENNReal.ofReal ε⁻¹ * z)
        (lintegral_lintegral_swap hswap.aemeasurable)
    _ = _ := by
      congr 1
      calc
        _ = ∫⁻ s : ℝ, (Ico (0 : ℝ) (a : ℝ)).indicator
            (fun s => μ {e | e.path.1 s.toNNReal < futureInf e.path t s.toNNReal + ε}) s :=
          lintegral_congr hinner
        _ = _ := lintegral_indicator measurableSet_Ico _

end BGW.StableTrees
