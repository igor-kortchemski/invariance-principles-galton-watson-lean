/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeBasic
public import BGW.StableTrees.SupremumAuxLocalTimePath

/-!
# Constancy of the auxiliary clock off supremum contact

With no negative jumps of the original path, reflection at the supremum is lower
semicontinuous. On a compact interval with no contact its minimum is positive, so every
sufficiently small occupation cutoff is constant there. The same holds for its limit.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- On a compact interval without contact the raw auxiliary clock is constant. -/
theorem supAuxLocalTime_eq_of_gap {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {f : DLoc}
    (hf : ∀ u, Function.leftLim f.1 u ≤ f.1 u) {s t : ℝ≥0} (hst : s ≤ t)
    (hgap : ∀ u ∈ Icc s t, 0 < supReflected f u) :
    supAuxLocalTime θ f t = supAuxLocalTime θ f s := by
  obtain ⟨u, hu, hmin⟩ := LowerSemicontinuousOn.exists_isMinOn
    (f := supReflected f) ⟨s, left_mem_Icc.mpr hst⟩ isCompact_Icc
    ((lowerSemicontinuous_supReflected hf).lowerSemicontinuousOn (Icc s t))
  have he : ∀ᶠ k in atTop, supOccupation (supAuxEps θ k) f t =
      supOccupation (supAuxEps θ k) f s := by
    filter_upwards [(isSupAuxEpsSeq_supAuxEps hθ).2.2.1.eventually
      (Iio_mem_nhds (hgap u hu))] with k hk
    exact supOccupation_eq_of_gap f hst fun v hv => hk.le.trans (hmin hv)
  exact Filter.limsup_congr he

/-- **Increase only on the contact set**: constant on any `[s,t]` strictly below the running
supremum (also in left limits), for all `s < t` simultaneously. -/
theorem ae_supAuxLocalTime_const_of_lt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ s t : ℝ≥0, s < t →
      (∀ u ∈ Icc s t, f.1 u < supRunning f u ∧ Function.leftLim f.1 u < supRunning f u) →
        supAuxLocalTime θ f t = supAuxLocalTime θ f s := by
  filter_upwards [ae_leftLim_le_stableLocalLaw hθ] with f hf
  intro s t hst hgap
  apply supAuxLocalTime_eq_of_gap hθ hf hst.le
  intro u hu
  exact sub_pos.mpr (hgap u hu).1

/-- **Support in the contact set** `{R = 0}`: `dL^aux` charges no time outside it. -/
theorem ae_supAuxStieltjes_support {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (supAuxStieltjes θ f).measure {s : ℝ | 0 ≤ s ∧ s.toNNReal ∉ supContact f} = 0 := by
  filter_upwards [ae_leftLim_le_stableLocalLaw hθ, ae_supAuxLocalTime_continuous hθ]
    with f hf hm
  let U : Set ℝ := {s | s.toNNReal ∉ supContact f}
  have hU : IsOpen U :=
    ((isClosed_supContact hf).preimage continuous_real_toNNReal).isOpen_compl
  let Q := {p : ℚ × ℚ // 0 ≤ p.1 ∧ p.1 < p.2 ∧ Icc (p.1 : ℝ) (p.2 : ℝ) ⊆ U}
  have hnull (p : Q) :
      (supAuxStieltjes θ f).measure (Ioo (p.1.1 : ℝ) (p.1.2 : ℝ)) = 0 := by
    have hq : (0 : ℝ) ≤ p.1.1 := by exact_mod_cast p.2.1
    have hr : (0 : ℝ) ≤ p.1.2 := hq.trans (by exact_mod_cast p.2.2.1.le)
    have hqr : (p.1.1 : ℝ) ≤ p.1.2 := by exact_mod_cast p.2.2.1.le
    have he : supAuxLocalTime θ f (p.1.2 : ℝ).toNNReal =
        supAuxLocalTime θ f (p.1.1 : ℝ).toNNReal := by
      apply supAuxLocalTime_eq_of_gap hθ hf (Real.toNNReal_mono hqr)
      intro u hu
      have hu' : (u : ℝ) ∈ Icc (p.1.1 : ℝ) (p.1.2 : ℝ) := by
        have h1 := NNReal.coe_le_coe.mpr hu.1
        have h2 := NNReal.coe_le_coe.mpr hu.2
        rw [Real.coe_toNNReal _ hq] at h1
        rw [Real.coe_toNNReal _ hr] at h2
        exact ⟨h1, h2⟩
      have hne : supReflected f u ≠ 0 := by
        have hnot := p.2.2.2 hu'
        simpa only [U, mem_ofPred_eq, Real.toNNReal_coe, supContact] using hnot
      exact lt_of_le_of_ne (supReflected_nonneg f u) hne.symm
    apply measure_mono_null Ioo_subset_Ioc_self
    change (pathStieltjes (supAuxLocalTime θ f)).measure
      (Ioc (p.1.1 : ℝ) (p.1.2 : ℝ)) = 0
    rw [pathStieltjes_measure_Ioc ⟨hm.2.1, hm.2.2⟩, he, sub_self, ENNReal.ofReal_zero]
  have hcover : {s : ℝ | 0 ≤ s ∧ s.toNNReal ∉ supContact f} ⊆
      ⋃ p : Q, Ioo (p.1.1 : ℝ) (p.1.2 : ℝ) := by
    intro s hs
    have hs0 : 0 < s := by
      apply lt_of_le_of_ne hs.1
      intro he
      have hz : s.toNNReal = 0 := by simp [← he]
      exact hs.2 (by simp [hz, supContact, supReflected_zero])
    obtain ⟨a, b, hsab, hab⟩ :=
      mem_nhds_iff_exists_Ioo_subset.mp (hU.mem_nhds hs.2)
    obtain ⟨q, hq, hqs⟩ := exists_rat_btwn (max_lt hsab.1 hs0)
    obtain ⟨r, hsr, hr⟩ := exists_rat_btwn hsab.2
    have hq0 : 0 ≤ q := by exact_mod_cast (le_max_right a 0).trans hq.le
    have hqr : q < r := by exact_mod_cast hqs.trans hsr
    have hsub : Icc (q : ℝ) (r : ℝ) ⊆ U := by
      apply subset_trans _ hab
      intro x hx
      exact ⟨((le_max_left a 0).trans_lt hq).trans_le hx.1, hx.2.trans_lt hr⟩
    exact mem_iUnion.mpr ⟨⟨(q, r), hq0, hqr, hsub⟩, hqs, hsr⟩
  exact measure_mono_null hcover (measure_iUnion_null hnull)

end BGW.StableTrees
