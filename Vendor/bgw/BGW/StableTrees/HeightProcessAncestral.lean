/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightProcessRoot

/-!
# Simultaneous ancestral height identification

A countable intersection over rational horizons identifies every ancestral time. The
Stieltjes source is carried by strict ancestors and upward-jump endpoints, so this event
also gives the simultaneous measure-level bridge without Lebesgue disintegration.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
namespace BGW.StableTrees

/-- Each ancestor is ancestral to a strictly positive rational horizon. -/
theorem exists_rat_horizon_of_ancestor (f : DLoc) {t s : ℝ≥0}
    (ha : ((s < t ∧ Function.leftLim f.1 s ≤ futureInf f t s) ∨
      (s = t ∧ Function.leftLim f.1 t < f.1 t))) :
    ∃ q : ℚ, 0 < (q : ℝ) ∧ s ≤ (q : ℝ).toNNReal ∧
      Function.leftLim f.1 s ≤ futureInf f (q : ℝ).toNNReal s := by
  rcases ha with ⟨hst, hs⟩ | ⟨he, hs⟩
  · obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn
      (show (s : ℝ) < t from by exact_mod_cast hst)
    have hqpos : 0 < (q : ℝ) := (show (0 : ℝ) ≤ s from s.2).trans_lt hsq
    have hQ : ((q : ℝ).toNNReal : ℝ) = q := Real.coe_toNNReal _ hqpos.le
    have hsQ : s ≤ (q : ℝ).toNNReal := by
      exact_mod_cast (show (s : ℝ) ≤ ((q : ℝ).toNNReal : ℝ) by rw [hQ]; exact hsq.le)
    have hQt : (q : ℝ).toNNReal ≤ t := by
      exact_mod_cast (show ((q : ℝ).toNNReal : ℝ) ≤ t by rw [hQ]; exact hqt.le)
    refine ⟨q, hqpos, hsQ, hs.trans ?_⟩
    rw [futureInf_split f hsQ hQt]
    exact min_le_left _ _
  · subst s
    obtain ⟨q, htq, hq⟩ := exists_rat_ancestor_of_jump f hs
    have hqpos : 0 < (q : ℝ) := (show (0 : ℝ) ≤ t from t.2).trans_lt htq
    have hQ : ((q : ℝ).toNNReal : ℝ) = q := Real.coe_toNNReal _ hqpos.le
    refine ⟨q, hqpos, ?_, hq.le⟩
    exact_mod_cast (show (t : ℝ) ≤ ((q : ℝ).toNNReal : ℝ) by rw [hQ]; exact htq.le)

/-- **Ancestral convergence** (one null set; all `t` and all ancestral `s ≤ t` at once): at an
ancestral time `s` (`X_{s-} ≤ I^s_t` with `s < t`, or an upward jump of `X` at `s = t`) the
approximations along `supEps θ` converge to the finite nonnegative `H_s`, and the raw height is
the genuine finite `ofReal`. -/
theorem ae_heightApprox_ancestral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t s : ℝ≥0,
      ((s < t ∧ Function.leftLim f.1 s ≤ futureInf f t s) ∨
        (s = t ∧ Function.leftLim f.1 t < f.1 t)) →
      Tendsto (fun k => heightApprox (supEps θ k) f s) atTop (𝓝 (height θ f s)) ∧
      0 ≤ height θ f s ∧ heightRaw θ f s = ENNReal.ofReal (height θ f s) := by
  have hrat (q : ℚ) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), 0 < (q : ℝ) →
      ∀ s : ℝ≥0, s ≤ (q : ℝ).toNNReal →
        Function.leftLim f.1 s ≤ futureInf f (q : ℝ).toNNReal s →
        Tendsto (fun k => heightApprox (supEps θ k) f s) atTop (𝓝 (height θ f s)) ∧
          0 ≤ height θ f s ∧ heightRaw θ f s = ENNReal.ofReal (height θ f s) := by
    by_cases hq : 0 < (q : ℝ)
    · filter_upwards [ae_height_ancestor_fixed hθ (Real.toNNReal_pos.mpr hq)] with f hf
      intro _ s hs ha
      exact ⟨(hf s hs ha).1, (hf s hs ha).2.1, (hf s hs ha).2.2.1⟩
    · exact Eventually.of_forall (fun _ h => (hq h).elim)
  filter_upwards [ae_all_iff.mpr hrat] with f hf
  intro t s ha
  obtain ⟨q, hq, hs, hanc⟩ := exists_rat_horizon_of_ancestor f ha
  exact hf q hq s hs hanc

/-- The Stieltjes source measure is carried by strict ancestors and upward-jump endpoints. -/
theorem ae_exploration_strict_or_jump (f : DLoc)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r) (t : ℝ≥0) :
    ∀ᵐ s ∂((explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ))),
      ((s.toNNReal < t ∧ Function.leftLim f.1 s.toNNReal ≤ futureInf f t s.toNNReal) ∨
        (s.toNNReal = t ∧ Function.leftLim f.1 t < f.1 t)) := by
  by_cases ht : t = 0
  · subst t
    simp [Measure.restrict_empty]
  let μ := (explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ))
  have hend : ∀ᵐ s ∂μ, s ≠ (t : ℝ) ∨ Function.leftLim f.1 t < f.1 t := by
    by_cases hj : Function.leftLim f.1 t < f.1 t
    · exact Eventually.of_forall (fun _ => Or.inr hj)
    · have he : Function.leftLim f.1 t = f.1 t := le_antisymm (hf t) (not_lt.mp hj)
      have hz : μ {(t : ℝ)} = 0 := by
        apply le_antisymm _ (zero_le)
        calc μ {(t : ℝ)} ≤ (explorationStieltjes f t).measure {(t : ℝ)} :=
               Measure.restrict_le_self _
             _ = 0 := explorationStieltjes_no_atom_of_leftLim_eq f
               (pos_iff_ne_zero.mpr ht) he
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hz] with s hs
      exact Or.inl hs
  filter_upwards [ae_exploration_ancestral_times f hf t, ae_restrict_mem measurableSet_Ioc,
    hend] with s hs hst hend
  have hle : s.toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.mpr hst.2
  rcases hle.lt_or_eq with hlt | he
  · exact Or.inl ⟨hlt, hs⟩
  · refine Or.inr ⟨he, ?_⟩
    rcases hend with hn | hj
    · exact (hn (by rw [← he, Real.coe_toNNReal _ hst.1.le])).elim
    · exact hj

/-- **Measure-level bridge** (endpoint atoms retained): a.s., for every `t`, the random Stieltjes
measure of `x ↦ I^x_t` on `(0,t]` is carried by times where `H` is finite, nonnegative and equal
to the raw height.  Must be proved by Stieltjes ancestral concentration, NOT by Fubini against
Lebesgue measure from `ae_heightRaw_eq`. -/
theorem ae_heightRaw_eq_stieltjes {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      ∀ᵐ s ∂((explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ))),
        0 ≤ height θ f s.toNNReal ∧
          heightRaw θ f s.toNNReal = ENNReal.ofReal (height θ f s.toNNReal) := by
  filter_upwards [ae_heightApprox_ancestral hθ, ae_leftLim_le_stableLocalLaw hθ] with f ha hf
  intro t
  filter_upwards [ae_exploration_strict_or_jump f hf t] with s hs
  exact (ha t s.toNNReal hs).2

end BGW.StableTrees
