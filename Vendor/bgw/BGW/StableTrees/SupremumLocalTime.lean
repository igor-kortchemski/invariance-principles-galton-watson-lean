/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLoc
public import BGW.StableTrees.StableLocalLaw
import BGW.Skorokhod.MeasurableExtrema
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Order.LiminfLimsup

/-!
# Supremum occupation approximations

Deterministic bounds and fixed-time measurability for the running supremum and its
occupation approximations. The simultaneous occupation-sequence existence theorem and the
ascending local-time construction are not established here.

These are preliminary objects for Duquesne and Le Gall, *Random Trees, Lévy Processes and
Spatial Branching Processes*, Astérisque 281 (2002), Section 1.1.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-- Running supremum `S_t = sup_{u ≤ t} X_u`. -/
noncomputable def supRunning (f : DLoc) (t : ℝ≥0) : ℝ := ⨆ u : Set.Iic t, f.1 u

/-- The reflected-at-supremum process `S_t - X_t`. -/
noncomputable def supReflected (f : DLoc) (t : ℝ≥0) : ℝ := supRunning f t - f.1 t

/-- Occupation approximation `ε⁻¹ · Leb{s ≤ t | S_s - X_s < ε}`. -/
noncomputable def supOccupation (ε : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  ε⁻¹ * (volume {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧ supReflected f s.toNNReal < ε}).toReal

/-- A deterministic sequence is a *simultaneous occupation sequence*: positive, strictly decreasing
to `0`, and almost surely the approximations converge at every time at once. -/
def IsSupOccupationSeq (θ : ℝ) (ε : ℕ → ℝ) : Prop :=
  (∀ k, 0 < ε k) ∧ StrictAnti ε ∧ Tendsto ε atTop (𝓝 0) ∧
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      ∃ ℓ : ℝ, Tendsto (fun k => supOccupation (ε k) f t) atTop (𝓝 ℓ)

/-- A local càdlàg path is bounded above on each initial compact interval. -/
theorem supRunning_bddAbove (f : DLoc) (t : ℝ≥0) :
    BddAbove (range (fun u : Set.Iic t => f.1 u)) := by
  have hb := (isBounded_range (DLoc.restrict t f)).bddAbove
  apply hb.mono
  rintro y ⟨u, rfl⟩
  exact ⟨⟨(u : ℝ), u.1.2, by exact_mod_cast u.2⟩, rfl⟩

/-- Every value before `t` is bounded above by the running supremum at `t`. -/
theorem eval_le_supRunning (f : DLoc) {u t : ℝ≥0} (hut : u ≤ t) :
    f.1 u ≤ supRunning f t :=
  le_ciSup (supRunning_bddAbove f t) ⟨u, hut⟩

/-- An upper bound for the path on `[0,t]` bounds its running supremum. -/
theorem supRunning_le (f : DLoc) (t : ℝ≥0) {a : ℝ}
    (ha : ∀ u : Set.Iic t, f.1 u ≤ a) : supRunning f t ≤ a :=
  ciSup_le ha

/-- The running supremum is monotone in time. -/
theorem monotone_supRunning (f : DLoc) : Monotone (supRunning f) := by
  intro s t hst
  exact supRunning_le f s fun u => eval_le_supRunning f (u.2.trans hst)

/-- At the origin the running supremum equals the initial value. -/
theorem supRunning_zero (f : DLoc) : supRunning f 0 = f.1 0 := by
  apply le_antisymm
  · apply supRunning_le
    intro u
    have hu : (u : ℝ≥0) = 0 := le_antisymm u.2 (bot_le)
    simp [hu]
  · exact eval_le_supRunning f le_rfl

/-- Reflection at the running supremum is nonnegative for every path. -/
theorem supReflected_nonneg (f : DLoc) (t : ℝ≥0) : 0 ≤ supReflected f t :=
  sub_nonneg.mpr (eval_le_supRunning f le_rfl)

/-- Reflection at the running supremum starts at zero for every path. -/
theorem supReflected_zero (f : DLoc) : supReflected f 0 = 0 := by
  simp [supReflected, supRunning_zero]

/-- The occupation set is contained in the initial compact time interval. -/
theorem supOccupation_set_subset (ε : ℝ) (f : DLoc) (t : ℝ≥0) :
    {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧ supReflected f s.toNNReal < ε} ⊆ Icc 0 t := by
  intro s hs
  exact ⟨hs.1, hs.2.1⟩

/-- The occupation set has finite Lebesgue measure, without any measurability premise. -/
theorem supOccupation_volume_ne_top (ε : ℝ) (f : DLoc) (t : ℝ≥0) :
    volume {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧ supReflected f s.toNNReal < ε} ≠ ⊤ :=
  ne_of_lt ((measure_mono (supOccupation_set_subset ε f t)).trans_lt
    measure_Icc_lt_top)

/-- The occupation approximation is nonnegative for a positive cutoff. -/
theorem supOccupation_nonneg {ε : ℝ} (hε : 0 ≤ ε) (f : DLoc) (t : ℝ≥0) :
    0 ≤ supOccupation ε f t :=
  mul_nonneg (inv_nonneg.mpr hε) ENNReal.toReal_nonneg

/-- The occupation approximation is monotone in its time horizon. -/
theorem monotone_supOccupation {ε : ℝ} (hε : 0 ≤ ε) (f : DLoc) :
    Monotone (supOccupation ε f) := by
  intro s t hst
  apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hε)
  apply ENNReal.toReal_mono (supOccupation_volume_ne_top ε f t)
  apply measure_mono
  intro u hu
  exact ⟨hu.1, hu.2.1.trans (by exact_mod_cast hst), hu.2.2⟩

/-- The approximation vanishes at time zero. -/
theorem supOccupation_zero (ε : ℝ) (f : DLoc) : supOccupation ε f 0 = 0 := by
  have hzero : volume {s : ℝ | 0 ≤ s ∧ s ≤ ((0 : ℝ≥0) : ℝ) ∧
      supReflected f s.toNNReal < ε} = 0 := by
    apply measure_mono_null (supOccupation_set_subset ε f 0)
    simp
  unfold supOccupation
  rw [hzero]
  simp

/-- A nonpositive cutoff gives the empty occupation set. -/
theorem supOccupation_of_nonpos {ε : ℝ} (hε : ε ≤ 0) (f : DLoc) (t : ℝ≥0) :
    supOccupation ε f t = 0 := by
  have he : {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧ supReflected f s.toNNReal < ε} = ∅ := by
    apply eq_empty_iff_forall_notMem.mpr
    intro s hs
    exact not_lt_of_ge ((supReflected_nonneg f s.toNNReal).trans' hε) hs.2.2
  simp [supOccupation, he]

/-- Fixed-time measurability of the running supremum. -/
theorem measurable_supRunning (t : ℝ≥0) : Measurable (fun f : DLoc => supRunning f t) := by
  let _ : Nonempty (univ : Set (Icc (0 : ℝ) (t : ℝ))) :=
    ⟨⟨⟨0, le_rfl, t.2⟩, mem_univ _⟩⟩
  have hm := (measurable_iSup_eval (T := (t : ℝ)) (J := univ) ordConnected_univ).comp
    (DLoc.measurable_restrict t)
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

/-- Fixed-time measurability of the reflected process. -/
theorem measurable_supReflected (t : ℝ≥0) : Measurable (fun f : DLoc => supReflected f t) :=
  (measurable_supRunning t).sub (DLoc.measurable_eval t)

/-- A strict supremum crossing is detected before the horizon or at its endpoint. -/
theorem lt_supRunning_iff (a : ℝ) (f : DLoc) (t : ℝ≥0) :
    a < supRunning f t ↔ DLoc.strictPassageAbove a f < (t : WithTop ℝ≥0) ∨ a < f.1 t := by
  rw [supRunning, lt_ciSup_iff (supRunning_bddAbove f t)]
  constructor
  · rintro ⟨u, hu⟩
    rcases u.2.eq_or_lt with he | hlt
    · change a < f.1 (u : ℝ≥0) at hu
      have he' : (u : ℝ≥0) = t := NNReal.coe_injective he
      rw [he'] at hu
      exact Or.inr hu
    · left
      apply lt_of_le_of_lt (iInf_le_of_le (u : ℝ≥0) (iInf_le _ hu))
      exact_mod_cast hlt
  · rintro (h | h)
    · obtain ⟨q, hq0, hqt, hq⟩ := (DLoc.strictPassageAbove_lt_iff a f t).mp h
      have hq0R : (0 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq0
      have hle : Real.toNNReal q ≤ t := by
        apply NNReal.coe_le_coe.mp
        rw [Real.coe_toNNReal _ hq0R]
        exact hqt.le
      exact ⟨⟨Real.toNNReal q, hle⟩, hq⟩
    · exact ⟨⟨t, le_rfl⟩, h⟩

/-- Joint measurability of the running supremum in time and path. -/
theorem measurable_supRunning_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => supRunning p.2 p.1) := by
  apply measurable_of_Ioi
  intro a
  have he : (fun p : ℝ≥0 × DLoc => supRunning p.2 p.1) ⁻¹' Ioi a =
      {p | DLoc.strictPassageAbove a p.2 < (p.1 : WithTop ℝ≥0)} ∪
        {p | a < p.2.1 p.1} := by
    ext p
    exact lt_supRunning_iff a p.2 p.1
  rw [he]
  apply MeasurableSet.union
  · exact measurableSet_lt
      ((DLoc.isStoppingTime_strictPassageAbove a).measurable'.comp measurable_snd)
      (by fun_prop)
  · exact measurableSet_lt measurable_const (DLoc.measurable_eval₂.comp measurable_swap)

/-- Joint measurability of reflection at the supremum. -/
theorem measurable_supReflected_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => supReflected p.2 p.1) :=
  measurable_supRunning_uncurry.sub (DLoc.measurable_eval₂.comp measurable_swap)

/-- Joint measurability of the occupation approximation in cutoff, horizon, and path. -/
theorem measurable_supOccupation_uncurry :
    Measurable (fun p : ℝ × (ℝ≥0 × DLoc) => supOccupation p.1 p.2.2 p.2.1) := by
  let A : Set ((ℝ × (ℝ≥0 × DLoc)) × ℝ) :=
    {p | 0 ≤ p.2 ∧ p.2 ≤ (p.1.2.1 : ℝ) ∧ supReflected p.1.2.2 p.2.toNNReal < p.1.1}
  have hA : MeasurableSet A := by
    apply MeasurableSet.inter (measurableSet_le measurable_const measurable_snd)
    apply MeasurableSet.inter (measurableSet_le measurable_snd (by fun_prop))
    have hm : Measurable (fun p : ((ℝ × (ℝ≥0 × DLoc)) × ℝ) =>
        (p.2.toNNReal, p.1.2.2)) := by fun_prop
    exact measurableSet_lt (measurable_supReflected_uncurry.comp hm) (by fun_prop)
  exact measurable_fst.inv.mul (measurable_measure_prodMk_left hA).ennreal_toReal

/-- Joint measurability of the real limsup along any deterministic cutoff sequence. -/
theorem measurable_supOccupation_limsup (ε : ℕ → ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc =>
      limsup (fun k => supOccupation (ε k) p.2 p.1) atTop) := by
  exact Measurable.limsup fun k => measurable_supOccupation_uncurry.comp
    (measurable_const.prodMk measurable_id)

/-- Every simultaneous occupation sequence converges to its real limsup on the same event. -/
theorem IsSupOccupationSeq.ae_tendsto_limsup {θ : ℝ} {ε : ℕ → ℝ}
    (hε : IsSupOccupationSeq θ ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      Tendsto (fun k => supOccupation (ε k) f t) atTop
        (𝓝 (limsup (fun k => supOccupation (ε k) f t) atTop)) := by
  filter_upwards [hε.2.2.2] with f hf
  intro t
  obtain ⟨l, hl⟩ := hf t
  rw [hl.limsup_eq]
  exact hl

/-- Given simultaneous convergence, its limit starts at zero, is nonnegative, and is monotone.
This does not supply the simultaneous sequence or continuity of its limit. -/
theorem IsSupOccupationSeq.ae_limsup_zero_nonneg_monotone {θ : ℝ} {ε : ℕ → ℝ}
    (hε : IsSupOccupationSeq θ ε) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      limsup (fun k => supOccupation (ε k) f 0) atTop = 0 ∧
        (∀ t : ℝ≥0, 0 ≤ limsup (fun k => supOccupation (ε k) f t) atTop) ∧
        Monotone (fun t : ℝ≥0 => limsup (fun k => supOccupation (ε k) f t) atTop) := by
  filter_upwards [hε.ae_tendsto_limsup] with f hf
  refine ⟨by simp only [supOccupation_zero, limsup_const], ?_, ?_⟩
  · intro t
    exact ge_of_tendsto (hf t) (Eventually.of_forall fun k =>
      supOccupation_nonneg (hε.1 k).le f t)
  · intro s t hst
    exact le_of_tendsto_of_tendsto (hf s) (hf t) (Eventually.of_forall fun k =>
      monotone_supOccupation (hε.1 k).le f hst)

/-- The ladder exponent `κ(q, λ) = (q - λ^θ) / (q^{1/θ} - λ)`, extended continuously
at `λ = q^{1/θ}` by `θ q^{1 - 1/θ}`. -/
noncomputable def supLadderExponent (θ q lam : ℝ) : ℝ :=
  if lam = q ^ (1 / θ) then θ * q ^ (1 - 1 / θ) else (q - lam ^ θ) / (q ^ (1 / θ) - lam)

/-- The diagonal branch of the ladder exponent. -/
theorem supLadderExponent_diagonal (θ q : ℝ) :
    supLadderExponent θ q (q ^ (1 / θ)) = θ * q ^ (1 - 1 / θ) := by
  simp [supLadderExponent]

/-- The time marginal of the proposed ladder exponent. -/
theorem supLadderExponent_zero_right {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ}
    (hq : 0 ≤ q) : supLadderExponent θ q 0 = q ^ (1 - 1 / θ) := by
  have hθ0 : 0 < θ := zero_lt_one.trans hθ.1
  have hβ : 0 < 1 - 1 / θ := sub_pos.mpr ((div_lt_one hθ0).mpr hθ.1)
  by_cases hq0 : q = 0
  · subst q
    rw [supLadderExponent, Real.zero_rpow (ne_of_gt (one_div_pos.mpr hθ0)),
      ite_eq_left rfl, Real.zero_rpow (ne_of_gt hβ), mul_zero]
  · have hqp : 0 < q := lt_of_le_of_ne hq (Ne.symm hq0)
    have hpow : 0 < q ^ (1 / θ) := Real.rpow_pos_of_pos hqp _
    rw [supLadderExponent, ite_eq_right (Ne.symm (ne_of_gt hpow)),
      Real.zero_rpow (ne_of_gt hθ0), sub_zero, sub_zero]
    exact (Real.rpow_one_sub' hq (ne_of_gt hβ)).symm

/-- The height marginal of the proposed ladder exponent. -/
theorem supLadderExponent_zero_left {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {lam : ℝ}
    (hlam : 0 ≤ lam) : supLadderExponent θ 0 lam = lam ^ (θ - 1) := by
  have hθ0 : 0 < θ := zero_lt_one.trans hθ.1
  have hα : 1 / θ ≠ 0 := ne_of_gt (one_div_pos.mpr hθ0)
  have hβ : 1 - 1 / θ ≠ 0 := ne_of_gt
    (sub_pos.mpr ((div_lt_one hθ0).mpr hθ.1))
  by_cases hl0 : lam = 0
  · subst lam
    rw [supLadderExponent, Real.zero_rpow hα, ite_eq_left rfl, Real.zero_rpow hβ,
      mul_zero, Real.zero_rpow (ne_of_gt (sub_pos.mpr hθ.1))]
  · rw [supLadderExponent, Real.zero_rpow hα, ite_eq_right hl0, zero_sub, zero_sub,
      neg_div_neg_eq]
    exact (Real.rpow_sub_one' hlam (ne_of_gt (sub_pos.mpr hθ.1))).symm

end BGW.StableTrees
