/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTime
import Mathlib.Order.Filter.ENNReal

/-!
# Public occupation sequence and totalized supremum clock

The auxiliary fast sequence supplies existence. The extended limsup retains pathwise
monotonicity even on exceptional paths where the real limsup has its default value.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A positive strictly decreasing sequence with simultaneous finite occupation limits exists. -/
theorem exists_isSupOccupationSeq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ ε : ℕ → ℝ, IsSupOccupationSeq θ ε := by
  refine ⟨supAuxEps θ, (isSupAuxEpsSeq_supAuxEps hθ).1,
    (isSupAuxEpsSeq_supAuxEps hθ).2.1, (isSupAuxEpsSeq_supAuxEps hθ).2.2.1, ?_⟩
  filter_upwards [ae_tendsto_supOccupation_supAuxEps_uniform hθ,
    ae_supAuxLimit_spec hθ] with f hu hf
  intro t
  let : CompactSpace (Iic t) := isCompact_iff_compactSpace.mp (by
    simpa only [Icc, Iic, zero_le, true_and] using
      (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) t)))
  refine ⟨supAuxLimit θ f t, tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  simp only [Real.dist_eq]
  apply squeeze_zero (fun _ => abs_nonneg _) _ (hu t)
  intro k
  refine le_ciSup (f := fun u : Iic t =>
    |supOccupation (supAuxEps θ k) f u - supAuxLimit θ f u|) ?_ ⟨t, le_rfl⟩
  exact (isCompact_range ((((continuous_supOccupation (supAuxEps_pos θ k) f).sub
    hf.2.2).abs).comp continuous_subtype_val)).bddAbove

open scoped Classical in
/-- The chosen sequence `ε_k ↓ 0`. -/
noncomputable def supEps (θ : ℝ) : ℕ → ℝ :=
  if h : 1 < θ ∧ θ ≤ 2 then Classical.choose (exists_isSupOccupationSeq h)
  else fun k => 1 / ((k : ℝ) + 1)

/-- The public choice is an admissible simultaneous occupation sequence. -/
theorem isSupOccupationSeq_supEps {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    IsSupOccupationSeq θ (supEps θ) := by
  simp only [supEps, hθ, and_self, dite_true]
  exact Classical.choose_spec (exists_isSupOccupationSeq hθ)

/-- Every public cutoff is positive, also outside the stable index range. -/
theorem supEps_pos (θ : ℝ) (k : ℕ) : 0 < supEps θ k := by
  classical
  by_cases hθ : 1 < θ ∧ θ ≤ 2
  · exact (isSupOccupationSeq_supEps hθ).1 k
  · simp only [supEps, dite_eq_right hθ]
    positivity

/-- The supremum local time `L^S = M`, the limsup of the occupation approximations along
`supEps θ` (real-valued, junk `0` where the occupations are unbounded). -/
noncomputable def supLocalTime (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  limsup (fun k => supOccupation (supEps θ k) f t) atTop

/-- The ENNReal limsup `p(t)` of the nonnegative occupations along `supEps θ`: the totalized
local time, everywhere nondecreasing in `t`. -/
noncomputable def supLocalTimeENN (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ≥0∞ :=
  limsup (fun k => ENNReal.ofReal (supOccupation (supEps θ k) f t)) atTop

/-- Nonnegative real sequences have compatible real and extended limsups, including
unbounded sequences, for which both real readings are zero. -/
theorem limsup_eq_toReal_of_nonneg {u : ℕ → ℝ} (hu : ∀ k, 0 ≤ u k) :
    limsup u atTop = (limsup (fun k => ENNReal.ofReal (u k)) atTop).toReal := by
  by_cases hb : IsBoundedUnder (· ≤ ·) atTop u
  · have h := ENNReal.toReal_limsup
      (u := fun k => ENNReal.ofReal (u k))
      (Eventually.of_forall fun _ => ENNReal.ofReal_ne_top)
      (by simpa only [ENNReal.toReal_ofReal (hu _)] using hb)
    simpa only [ENNReal.toReal_ofReal (hu _)] using h.symm
  · have he : {a : ℝ | ∀ᶠ k in atTop, u k ≤ a} = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hb ⟨a, ha⟩
    have ht : limsup (fun k => ENNReal.ofReal (u k)) atTop = ⊤ := by
      rw [limsup_eq, sInf_eq_top]
      intro a ha
      by_contra hne
      have hfin : a ≠ ⊤ := fun h => hne h
      apply hb
      refine ⟨a.toReal, ?_⟩
      change ∀ᶠ k in atTop, u k ≤ a.toReal
      change ∀ᶠ k in atTop, ENNReal.ofReal (u k) ≤ a at ha
      filter_upwards [ha] with k hk
      exact (ENNReal.toReal_ofReal (hu k)).symm.trans_le
        (ENNReal.toReal_mono hfin hk)
    rw [limsup_eq, he, Real.sInf_empty, ht, ENNReal.toReal_top]

/-- The real clock is the finite reading of the extended clock on every path. -/
theorem supLocalTime_eq_toReal (θ : ℝ) (f : DLoc) (t : ℝ≥0) :
    supLocalTime θ f t = (supLocalTimeENN θ f t).toReal := by
  exact limsup_eq_toReal_of_nonneg fun k => supOccupation_nonneg (supEps_pos θ k).le f t

/-- The extended clock is nondecreasing in time on every path. -/
theorem monotone_supLocalTimeENN (θ : ℝ) (f : DLoc) : Monotone (supLocalTimeENN θ f) := by
  intro s t hst
  exact limsup_le_limsup (Eventually.of_forall fun k => ENNReal.ofReal_le_ofReal
    (monotone_supOccupation (supEps_pos θ k).le f hst))

/-- The extended clock is jointly measurable in time and path. -/
theorem measurable_supLocalTimeENN_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supLocalTimeENN θ p.2 p.1) := by
  exact Measurable.limsup fun k =>
    (measurable_supOccupation_uncurry.comp
      (measurable_const.prodMk measurable_id)).ennreal_ofReal

/-- Prefix measurability of the extended clock in the right-continuous filtration. -/
theorem measurable_supLocalTimeENN_filtration (θ : ℝ) (t : ℝ≥0) :
    Measurable[DLoc.filtration t] (fun f : DLoc => supLocalTimeENN θ f t) := by
  have hm : Measurable[DLoc.rawFiltration t] (fun f : DLoc => supLocalTimeENN θ f t) :=
    Measurable.limsup fun k =>
      (measurable_rawFiltration_supOccupation (supEps θ k) t).ennreal_ofReal
  exact hm.mono (DLoc.rawFiltration.le_rightCont t) le_rfl

/-- Joint measurability of the real public clock. -/
theorem measurable_supLocalTime_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => supLocalTime θ p.2 p.1) := by
  exact measurable_supOccupation_limsup (supEps θ)

/-- The real public clock is strongly adapted. -/
theorem stronglyAdapted_supLocalTime (θ : ℝ) :
    StronglyAdapted DLoc.filtration (fun t (f : DLoc) => supLocalTime θ f t) := by
  intro t
  have hm : Measurable[DLoc.rawFiltration t] (fun f : DLoc => supLocalTime θ f t) :=
    Measurable.limsup fun k => measurable_rawFiltration_supOccupation (supEps θ k) t
  exact (hm.mono (DLoc.rawFiltration.le_rightCont t) le_rfl).stronglyMeasurable

/-- Fixed-time measurability of the real public clock. -/
theorem measurable_supLocalTime (θ : ℝ) (t : ℝ≥0) :
    Measurable (fun f : DLoc => supLocalTime θ f t) := by
  exact ((stronglyAdapted_supLocalTime θ t).measurable).mono
    (DLoc.filtration.le t) le_rfl

/-- The selected occupations converge simultaneously to their public real limsup. -/
theorem ae_tendsto_supOccupation {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      Tendsto (fun k => supOccupation (supEps θ k) f t) atTop (𝓝 (supLocalTime θ f t)) := by
  exact (isSupOccupationSeq_supEps hθ).ae_tendsto_limsup

end BGW.StableTrees
