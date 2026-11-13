/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessSupport
import BGW.StableTrees.StableStrongMarkov

/-!
# Positivity of the clock after supremum contacts

A countable measurable characterization of positive finite clocks transfers through strong
Markov restart. Occupation additivity then gives immediate clock growth after every finite
strict upward passage at a fixed level.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- The fresh supremum clock after a finite stopping time is positive at every positive age. -/
theorem ae_supLocalTime_pos_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {τ : DLoc → ℝ≥0∞} (hτ : IsStoppingTime DLoc.filtration τ) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), τ f < ⊤ →
      ∀ u : ℝ≥0, 0 < u → 0 < supLocalTime θ (DLoc.shiftAt τ f) u := by
  let P : Measure DLoc := stableLocalLaw θ
  let S : Set DLoc := {f | τ f < ⊤}
  let B : Set DLoc := {f | (∀ n : ℕ, supLocalTimeENN θ f n ≠ ⊤) ∧
    ∀ n : ℕ, 0 < supLocalTime θ f (1 / (n + 1 : ℝ≥0))}
  have hENN (n : ℕ) : Measurable (fun f : DLoc => supLocalTimeENN θ f n) :=
    Measurable.comp (g := fun p : ℝ≥0 × DLoc => supLocalTimeENN θ p.2 p.1)
      (f := fun f : DLoc => ((n : ℝ≥0), f)) (measurable_supLocalTimeENN_uncurry θ)
      (measurable_const.prodMk measurable_id)
  have hB : MeasurableSet B := by
    have hN : MeasurableSet {f : DLoc | ∀ n : ℕ, supLocalTimeENN θ f n ≠ ⊤} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun n => (measurableSet_eq_fun (hENN n) measurable_const).compl)
    have hsmall : MeasurableSet {f : DLoc | ∀ n : ℕ,
        0 < supLocalTime θ f (1 / (n + 1 : ℝ≥0))} := by
      simp only [Set.ofPred_forall]
      exact MeasurableSet.iInter (fun n => measurableSet_lt measurable_const
        (measurable_supLocalTime θ (1 / (n + 1 : ℝ≥0))))
    exact hN.inter hsmall
  have haB : ∀ᵐ f ∂P, f ∈ B := by
    filter_upwards [ae_tendsto_supOccupation hθ, ae_supLocalTime_pos hθ] with f hf hp
    refine ⟨?_, fun n => hp _ (by positivity)⟩
    intro n
    change limsup (fun k => ENNReal.ofReal (supOccupation (supEps θ k) f n)) atTop ≠ ⊤
    rw [(ENNReal.tendsto_ofReal (hf n)).limsup_eq]
    exact ENNReal.ofReal_ne_top
  have haMap : ∀ᵐ g ∂((P.restrict S).map (DLoc.shiftAt τ)), g ∈ B := by
    rw [map_shiftAt_restrict_stableLocalLaw hθ hτ]
    exact Measure.ae_smul_measure haB _
  have haRes : ∀ᵐ f ∂P.restrict S, DLoc.shiftAt τ f ∈ B :=
    (ae_map_iff (DLoc.measurable_shiftAt hτ).aemeasurable hB).mp haMap
  have hS : MeasurableSet S :=
    hτ.measurableSpace_le _ (DLoc.measurableSet_lt_top_stopped hτ)
  filter_upwards [(ae_restrict_iff' hS).mp haRes] with f hf
  intro hfin u hu
  obtain ⟨hN, hsmall⟩ := hf hfin
  have hfinite (v : ℝ≥0) : supLocalTimeENN θ (DLoc.shiftAt τ f) v ≠ ⊤ := by
    let n : ℕ := ⌈(v : ℝ)⌉₊
    have hvn : v ≤ (n : ℝ≥0) := by exact_mod_cast (Nat.le_ceil (v : ℝ))
    exact ne_top_of_le_ne_top (hN n) (monotone_supLocalTimeENN θ _ hvn)
  have hmono : Monotone (supLocalTime θ (DLoc.shiftAt τ f)) := by
    intro v w hvw
    rw [supLocalTime_eq_toReal, supLocalTime_eq_toReal]
    exact ENNReal.toReal_mono (hfinite w) (monotone_supLocalTimeENN θ _ hvw)
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hu
  exact (hsmall n).trans_le (hmono hn.le)

/-- A convergent occupation clock restarts at every supremum contact of its path. -/
theorem supLocalTime_restart_of_contact (θ : ℝ) (f : DLoc) (hf0 : f.1 0 = 0)
    {s : ℝ≥0} (hs : supReflected f s = 0)
    (hp : ∀ u : ℝ≥0, Tendsto (fun k => supOccupation (supEps θ k) f u) atTop
      (𝓝 (supLocalTime θ f u))) (u : ℝ≥0) :
    supLocalTime θ f (s + u) = supLocalTime θ f s + supLocalTime θ (DLoc.shift s f) u := by
  have he (k : ℕ) := supOccupation_shift_of_contact (supEps_pos θ k) hf0 hs u
  have hl : Tendsto (fun k => supOccupation (supEps θ k) (DLoc.shift s f) u) atTop
      (𝓝 (supLocalTime θ f (s + u) - supLocalTime θ f s)) :=
    (tendsto_congr he).mp ((hp (s + u)).sub (hp s))
  have hh : supLocalTime θ (DLoc.shift s f) u =
      supLocalTime θ f (s + u) - supLocalTime θ f s := hl.limsup_eq
  linarith only [hh]

private theorem strictPassageAbove_contact (f : DLoc) (q : ℝ≥0) {s : ℝ≥0}
    (hτ : DLoc.strictPassageAbove (q : ℝ) f = (s : ℝ≥0∞)) : supReflected f s = 0 := by
  let g : DLoc := ⟨fun u => -f.1 u, f.2.continuous_comp continuous_neg⟩
  have hpass : firstPassageBelow q g = DLoc.strictPassageAbove (q : ℝ) f := by
    change (⨅ u : ℝ≥0, ⨅ (_ : -f.1 u < -(q : ℝ)), (u : ℝ≥0∞)) =
      ⨅ u : ℝ≥0, ⨅ (_ : (q : ℝ) < f.1 u), (u : ℝ≥0∞)
    simp only [neg_lt_neg_iff]
  have hq : (q : ℝ) ≤ f.1 s := by
    have hh := eval_le_of_firstPassageBelow_eq_coe (hpass.trans hτ)
    change -f.1 s ≤ -(q : ℝ) at hh
    linarith only [hh]
  unfold supReflected
  apply sub_eq_zero.mpr
  apply le_antisymm _ (eval_le_supRunning f le_rfl)
  apply supRunning_le
  intro u
  have hus : (u : ℝ≥0) ≤ s := u.2
  rcases hus.eq_or_lt with he | hlt
  · have he' : (u : ℝ≥0) = s := he
    exact (congrArg f.1 he').le
  · have huq : f.1 u ≤ (q : ℝ) := by
      by_contra hn
      have hp : DLoc.strictPassageAbove (q : ℝ) f ≤ (u : ℝ≥0∞) :=
        iInf_le_of_le (u : ℝ≥0) (iInf_le _ (not_le.mp hn))
      rw [hτ] at hp
      exact (not_le_of_gt (show (u : ℝ≥0∞) < (s : ℝ≥0∞) from by exact_mod_cast hlt)) hp
    exact huq.trans hq

/-- The clock increases immediately after every fixed-level strict upward passage. -/
theorem ae_clock_increases_after_passage {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (q : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), DLoc.strictPassageAbove (q : ℝ) f < ⊤ →
      ∀ u : ℝ≥0, 0 < u →
        supLocalTime θ f (ENNReal.toNNReal (DLoc.strictPassageAbove (q : ℝ) f)) <
          supLocalTime θ f (ENNReal.toNNReal (DLoc.strictPassageAbove (q : ℝ) f) + u) := by
  have hstop := DLoc.isStoppingTime_strictPassageAbove (q : ℝ)
  filter_upwards [ae_supLocalTime_pos_shiftAt hθ hstop, ae_tendsto_supOccupation hθ,
    ae_eval_zero_stableLocalLaw hθ] with f hp hc hf0
  intro hfin u hu
  have he : DLoc.strictPassageAbove (q : ℝ) f =
      (ENNReal.toNNReal (DLoc.strictPassageAbove (q : ℝ) f) : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal hfin.ne).symm
  have hcontact := strictPassageAbove_contact f q he
  have hr := supLocalTime_restart_of_contact θ f hf0 hcontact hc u
  have hpos := hp hfin u hu
  change 0 < supLocalTime θ
    (DLoc.shift (ENNReal.toNNReal (DLoc.strictPassageAbove (q : ℝ) f)) f) u at hpos
  linarith only [hr, hpos]

end BGW.StableTrees
