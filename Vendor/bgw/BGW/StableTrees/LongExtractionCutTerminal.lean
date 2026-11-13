/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionStoppedCut

/-!
# Continuity at the observed terminal source time

Continuity of a cut at its cutoff gives left continuity of the source at the corresponding
interior time. Càdlàg right continuity supplies the other side.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Continuity at an interior cut cutoff implies continuity of the source at the shifted cutoff.
Reference: Billingsley (1999), Chapter 3. -/
theorem continuousAt_source_of_translatedStoppedCut {M : ℝ} {T : ℝ≥0}
    (hT : 0 < T) (f : D M ℝ) (g d q : Icc (0 : ℝ) M) (hgd : g ≤ d)
    (hqt : (q : ℝ) = (g : ℝ) + T) (hqd : q < d)
    (hc : ContinuousAt (translatedStoppedCut T f g d hgd) ⟨T, T.2, le_rfl⟩) :
    ContinuousAt f q := by
  let ψ : Icc (0 : ℝ) M → Icc (0 : ℝ) (T : ℝ) :=
    fun s => projIcc (0 : ℝ) (T : ℝ) T.2 ((s : ℝ) - g)
  have hψ : Continuous ψ := continuous_projIcc.comp (continuous_subtype_val.sub continuous_const)
  have hψq : ψ q = ⟨T, T.2, le_rfl⟩ := by
    apply Subtype.ext
    change max (0 : ℝ) (min (T : ℝ) ((q : ℝ) - g)) = T
    rw [hqt, add_sub_cancel_left, min_self]
    exact max_eq_right (show (0 : ℝ) ≤ (T : ℝ) from T.2)
  have hmap : Tendsto ψ (𝓝 q) (𝓝 (ψ q)) := hψ.continuousAt.tendsto
  rw [hψq] at hmap
  have hlim := hc.tendsto.comp hmap
  have hvalue : translatedStoppedCut T f g d hgd ⟨T, T.2, le_rfl⟩ + f g = f q := by
    rw [translatedStoppedCut_apply]
    have heq : (⟨min ((g : ℝ) + T) d, le_min (add_nonneg g.2.1 T.2) d.2.1,
        (min_le_right _ _).trans d.2.2⟩ : Icc (0 : ℝ) M) = q := by
      apply Subtype.ext
      change min ((g : ℝ) + T) d = (q : ℝ)
      rw [← hqt]
      exact min_eq_left (show (q : ℝ) ≤ (d : ℝ) from hqd.le)
    rw [heq]
    ring
  have hsum := hlim.add_const (f g)
  rw [hvalue] at hsum
  rw [continuousAt_iff_continuous_left'_right']
  refine ⟨?_, (isCadlag f).isRightContinuous q⟩
  have hgq : g < q := by
    change (g : ℝ) < q
    rw [hqt]
    exact lt_add_of_pos_right _ (by exact_mod_cast hT)
  have heq : f =ᶠ[𝓝[<] q] fun s => translatedStoppedCut T f g d hgd (ψ s) + f g := by
    filter_upwards [self_mem_nhdsWithin,
      (eventually_gt_nhds hgq).filter_mono nhdsWithin_le_nhds] with s hsq hgs
    rw [translatedStoppedCut_apply]
    have hmem : (s : ℝ) - g ∈ Icc (0 : ℝ) (T : ℝ) := by
      constructor
      · exact sub_nonneg.mpr hgs.le
      · have hs : (s : ℝ) < q := hsq
        rw [hqt] at hs
        linarith only [hs]
    have hψs : (ψ s : ℝ) = (s : ℝ) - g := by
      change max (0 : ℝ) (min (T : ℝ) ((s : ℝ) - g)) = (s : ℝ) - g
      rw [min_eq_right hmem.2, max_eq_right hmem.1]
    have heval : (⟨min ((g : ℝ) + ψ s) d,
        le_min (add_nonneg g.2.1 (ψ s).2.1) d.2.1,
        (min_le_right _ _).trans d.2.2⟩ : Icc (0 : ℝ) M) = s := by
      apply Subtype.ext
      change min ((g : ℝ) + (ψ s : ℝ)) d = s
      rw [hψs, show (g : ℝ) + ((s : ℝ) - g) = s by ring,
        min_eq_left (show (s : ℝ) ≤ (d : ℝ) from (hsq.trans hqd).le)]
    rw [heval]
    ring
  exact (hsum.mono_left nhdsWithin_le_nhds).congr' (Filter.EventuallyEq.symm heq)

end BGW.StableTrees
