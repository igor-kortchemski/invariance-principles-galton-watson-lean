/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionHeightBasic
import Mathlib.MeasureTheory.Measure.Prod

/-!
# Agreement of continuous and universal heights at almost every host time

Fubini on countably many bounded windows puts the a.e.-age identities on a single host event.
Literal prefix locality then identifies both reconstructions at every horizon on that event.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **A.e.-time identity on the host**: almost surely, the continuous height equals the
universal raw height at Lebesgue-almost every time. -/
theorem ae_heightLoc_eq_heightUniv_ae {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      heightLoc θ f s.toNNReal = heightUniv θ f s.toNNReal := by
  have hm : MeasurableSet {p : ℝ × DLoc |
      heightLoc θ p.2 p.1.toNNReal = heightUniv θ p.2 p.1.toNNReal} :=
    measurableSet_eq_fun
      (Measurable.comp (g := fun p : ℝ≥0 × DLoc => heightLoc θ p.2 p.1)
        (f := fun p : ℝ × DLoc => (p.1.toNNReal, p.2))
        (measurable_heightLoc_uncurry θ)
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
      (Measurable.comp (g := fun p : ℝ≥0 × DLoc => heightUniv θ p.2 p.1)
        (f := fun p : ℝ × DLoc => (p.1.toNNReal, p.2))
        (measurable_heightUniv_uncurry θ)
        ((measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd))
  have hn (n : ℕ) : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ᵐ s : ℝ ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
        heightLoc θ f s.toNNReal = heightUniv θ f s.toNNReal := by
    apply (MeasureTheory.Measure.ae_ae_comm hm).mp
    filter_upwards [ae_age_heightUniv_eq_height hθ (n : ℝ≥0)] with s hs
    filter_upwards [hs, ae_heightLoc_eq_height hθ s.toNNReal] with f hf hg
    exact hg.trans hf.symm
  have hu : (⋃ n : ℕ, Ioo (0 : ℝ) (n : ℝ)) = Ioi 0 := by
    ext s
    simp only [mem_iUnion, mem_Ioo, mem_Ioi]
    constructor
    · rintro ⟨_, hs, _⟩
      exact hs
    · intro hs
      obtain ⟨n, hn⟩ := exists_nat_gt s
      exact ⟨n, hs, hn⟩
  filter_upwards [ae_all_iff.mpr hn] with f hf
  rw [← hu]
  exact (ae_restrict_iUnion_iff _ _).mpr hf

/-- An a.e.-time host agreement gives a version on each compact prefix. -/
theorem isPrefixHeightVersion_restrict_of_ae (θ : ℝ) (f : DLoc)
    (hf : ∀ᵐ s : ℝ ∂(volume.restrict (Ioi (0 : ℝ))),
      heightLoc θ f s.toNNReal = heightUniv θ f s.toNNReal) (T : ℝ≥0) :
    IsPrefixHeightVersion θ T (DLoc.restrict T f)
      ⟨fun t => heightLoc θ f ⟨t, t.2.1⟩,
        (continuous_heightLoc θ f).comp
          (continuous_subtype_val.subtype_mk fun t => t.2.1)⟩ := by
  refine ⟨heightLoc_zero θ f, ?_⟩
  have hh := ae_restrict_of_ae_restrict_of_subset (Ioo_subset_Ioi_self :
    Ioo (0 : ℝ) (T : ℝ) ⊆ Ioi 0) hf
  filter_upwards [hh, ae_restrict_mem measurableSet_Ioo] with s hs hmem
  have hp : Set.projIcc 0 (T : ℝ) T.2 s = ⟨s, hmem.1.le, hmem.2.le⟩ :=
    Set.projIcc_of_mem T.2 ⟨hmem.1.le, hmem.2.le⟩
  change heightLoc θ f ⟨(Set.projIcc 0 (T : ℝ) T.2 s : ℝ),
    (Set.projIcc 0 (T : ℝ) T.2 s).2.1⟩ = _
  rw [hp]
  have ht : (⟨s, hmem.1.le⟩ : ℝ≥0) = s.toNNReal :=
    (Real.toNNReal_of_nonneg hmem.1.le).symm
  change heightLoc θ f ⟨s, hmem.1.le⟩ = _
  rw [ht, hs]
  exact heightUniv_eq_of_restrict_eq θ T f _ (restrict_extendConst T _).symm _
    (Real.toNNReal_le_iff_le_coe.mpr hmem.2.le)

/-- Under the stable law, the a.e.-time prefix map and H03's rational-time prefix map agree on
the restricted path, simultaneously for all horizons. -/
theorem ae_heightPrefixAE_eq_heightPrefix {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ T : ℝ≥0,
      heightPrefixAE θ T (DLoc.restrict T f) = heightPrefix θ T (DLoc.restrict T f) := by
  filter_upwards [ae_heightLoc_eq_heightUniv_ae hθ, ae_heightPrefix_restrict_all hθ]
    with f hf hg
  intro T
  rw [heightPrefixAE_eq_of_isPrefixHeightVersion θ T _ _
    (isPrefixHeightVersion_restrict_of_ae θ f hf T)]
  ext t
  exact (hg T t).symm

end BGW.StableTrees
