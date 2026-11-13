/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightContinuity
import Mathlib.Topology.UniformSpace.CompactConvergence
import Mathlib.Topology.Metrizable.Uniformity
import Mathlib.Topology.ContinuousMap.SecondCountableSpace

public import BGW.Skorokhod.PathRegularity

/-!
# Continuous excursion heights from almost every age

Versions agree with the universal height at Lebesgue-almost every interior age. Continuity
and the prescribed boundary values make versions unique, even when the prefix horizon is zero.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- `g` is an **a.e.-age height version** of the excursion `e`: it vanishes at time `0` and at
and after the lifetime, and agrees with `heightUniv θ e.path` at Lebesgue-almost every age of
`(0, ζ(e))`. -/
def IsExcursionHeightVersion (θ : ℝ) (e : Excursion) (g : C(ℝ≥0, ℝ)) : Prop :=
  g 0 = 0 ∧ (∀ t : ℝ≥0, e.lifetime ≤ t → g t = 0) ∧
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) (e.lifetime : ℝ))),
      g s.toNNReal = heightUniv θ e.path s.toNNReal

/-- **The excursion height**: the a.e.-age height version of `e` when one exists (it is then
unique), the zero function otherwise. -/
noncomputable def excursionHeight (θ : ℝ) (e : Excursion) : C(ℝ≥0, ℝ) :=
  if h : ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g then Classical.choose h else 0

/-- `c` is an **a.e.-time prefix height version** of `g : D T ℝ`: it vanishes at time `0` and
agrees with `heightUniv θ (extendConst T g)` at Lebesgue-almost every time of `(0, T)`. -/
def IsPrefixHeightVersion (θ : ℝ) (T : ℝ≥0) (g : D (T : ℝ) ℝ)
    (c : C(Set.Icc (0 : ℝ) T, ℝ)) : Prop :=
  c ⟨0, le_rfl, T.2⟩ = 0 ∧
    ∀ᵐ s : ℝ ∂(volume.restrict (Set.Ioo (0 : ℝ) (T : ℝ))),
      c (Set.projIcc 0 (T : ℝ) T.2 s) = heightUniv θ (extendConst T g) s.toNNReal

/-- **A.e.-time prefix height map** on `[0,T]`: the a.e.-time prefix height version of `g` when
one exists (it is then unique), `0` otherwise. -/
noncomputable def heightPrefixAE (θ : ℝ) (T : ℝ≥0) (g : D (T : ℝ) ℝ) :
    C(Set.Icc (0 : ℝ) T, ℝ) :=
  if h : ∃ c : C(Set.Icc (0 : ℝ) T, ℝ), IsPrefixHeightVersion θ T g c then
    Classical.choose h else 0

/-- A.e.-age versions of one excursion coincide. -/
theorem IsExcursionHeightVersion.unique {θ : ℝ} {e : Excursion} {g h : C(ℝ≥0, ℝ)}
    (hg : IsExcursionHeightVersion θ e g) (hh : IsExcursionHeightVersion θ e h) : g = h := by
  have he := eqOn_Icc_of_ae_eq_Ioo (show (0 : ℝ) < e.lifetime from e.lifetime_pos)
    (g.continuous.comp continuous_real_toNNReal)
    (h.continuous.comp continuous_real_toNNReal) (by
      filter_upwards [hg.2.2, hh.2.2] with s hs ht
      exact hs.trans ht.symm)
  ext t
  by_cases ht : e.lifetime ≤ t
  · exact (hg.2.1 t ht).trans (hh.2.1 t ht).symm
  · have ht' : (t : ℝ) ∈ Icc (0 : ℝ) (e.lifetime : ℝ) :=
      ⟨t.2, (not_le.mp ht).le⟩
    simpa only [Function.comp_apply, Real.toNNReal_coe] using he ht'

/-- **Deterministic characterization**: an a.e.-age height version is the excursion height. -/
theorem excursionHeight_eq_of_isExcursionHeightVersion (θ : ℝ) (e : Excursion)
    (g : C(ℝ≥0, ℝ)) (hg : IsExcursionHeightVersion θ e g) : excursionHeight θ e = g := by
  have hex : ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g := ⟨g, hg⟩
  rw [excursionHeight, dite_eq_left hex]
  exact IsExcursionHeightVersion.unique (Classical.choose_spec hex) hg

/-- On the non-junk branch the excursion height is itself a version. -/
theorem isExcursionHeightVersion_excursionHeight (θ : ℝ) (e : Excursion)
    (h : ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g) :
    IsExcursionHeightVersion θ e (excursionHeight θ e) := by
  rw [excursionHeight, dite_eq_left h]
  exact Classical.choose_spec h

/-- The excursion height starts at `0`, for every excursion. -/
theorem excursionHeight_zero (θ : ℝ) (e : Excursion) : excursionHeight θ e 0 = 0 := by
  unfold excursionHeight
  split_ifs with h
  · exact (Classical.choose_spec h).1
  · rfl

/-- The excursion height vanishes at and after the lifetime, for every excursion. -/
theorem excursionHeight_eq_zero_of_lifetime_le (θ : ℝ) (e : Excursion) {t : ℝ≥0}
    (ht : e.lifetime ≤ t) : excursionHeight θ e t = 0 := by
  unfold excursionHeight
  split_ifs with h
  · exact (Classical.choose_spec h).2.1 t ht
  · rfl

/-- Every a.e.-age version is nonnegative, by uniqueness applied to its positive part. -/
theorem IsExcursionHeightVersion.nonneg {θ : ℝ} {e : Excursion} {g : C(ℝ≥0, ℝ)}
    (hg : IsExcursionHeightVersion θ e g) (t : ℝ≥0) : 0 ≤ g t := by
  let h : C(ℝ≥0, ℝ) := ⟨fun s => max (g s) 0, g.continuous.max continuous_const⟩
  have hh : IsExcursionHeightVersion θ e h := by
    refine ⟨by change max (g 0) 0 = 0; rw [hg.1, max_self], ?_, ?_⟩
    · intro s hs
      change max (g s) 0 = 0
      rw [hg.2.1 s hs, max_self]
    · filter_upwards [hg.2.2] with s hs
      change max (g s.toNNReal) 0 = _
      rw [hs, max_eq_left (heightUniv_nonneg θ e.path s.toNNReal)]
  have he := congrArg (fun c : C(ℝ≥0, ℝ) => c t) (hh.unique hg)
  change max (g t) 0 = g t at he
  exact he ▸ le_max_right (g t) 0

/-- The excursion height is nonnegative, for every excursion. -/
theorem excursionHeight_nonneg (θ : ℝ) (e : Excursion) (t : ℝ≥0) :
    0 ≤ excursionHeight θ e t := by
  unfold excursionHeight
  split_ifs with h
  · exact (Classical.choose_spec h).nonneg t
  · exact le_rfl

/-- A.e.-time versions on a compact horizon coincide, including at horizon zero. -/
theorem IsPrefixHeightVersion.unique {θ : ℝ} {T : ℝ≥0} {g : D (T : ℝ) ℝ}
    {c d : C(Set.Icc (0 : ℝ) T, ℝ)} (hc : IsPrefixHeightVersion θ T g c)
    (hd : IsPrefixHeightVersion θ T g d) : c = d := by
  by_cases hT : T = 0
  · subst T
    ext t
    have ht : t = ⟨0, le_rfl, (0 : ℝ≥0).2⟩ := Subtype.ext (le_antisymm t.2.2 t.2.1)
    rw [ht, hc.1, hd.1]
  · have hp : (0 : ℝ) < T := by exact_mod_cast (pos_iff_ne_zero.mpr hT : 0 < T)
    have he : Set.EqOn (fun s : ℝ => c (Set.projIcc 0 (T : ℝ) T.2 s))
        (fun s : ℝ => d (Set.projIcc 0 (T : ℝ) T.2 s)) (Icc 0 (T : ℝ)) :=
      eqOn_Icc_of_ae_eq_Ioo hp
      (c.continuous.comp continuous_projIcc)
      (d.continuous.comp continuous_projIcc) (by
        filter_upwards [hc.2, hd.2] with s hs ht
        exact hs.trans ht.symm)
    ext t
    exact (congrArg c (Set.projIcc_val T.2 t)).symm.trans
      ((he t.2).trans (congrArg d (Set.projIcc_val T.2 t)))

/-- **Deterministic characterization** of the prefix map: an a.e.-time prefix height version is
the value of `heightPrefixAE`. -/
theorem heightPrefixAE_eq_of_isPrefixHeightVersion (θ : ℝ) (T : ℝ≥0) (g : D (T : ℝ) ℝ)
    (c : C(Set.Icc (0 : ℝ) T, ℝ)) (hc : IsPrefixHeightVersion θ T g c) :
    heightPrefixAE θ T g = c := by
  have hex : ∃ c : C(Set.Icc (0 : ℝ) T, ℝ), IsPrefixHeightVersion θ T g c := ⟨c, hc⟩
  rw [heightPrefixAE, dite_eq_left hex]
  exact IsPrefixHeightVersion.unique (Classical.choose_spec hex) hc

/-- **Deterministic graph identity**: on the non-junk branch, for every horizon `a < ζ(e)`, the
prefix map applied to the restricted excursion is the excursion height on `[0,a]`. -/
theorem heightPrefixAE_excursionRestrict_of_exists (θ : ℝ) (e : Excursion)
    (he : ∃ g : C(ℝ≥0, ℝ), IsExcursionHeightVersion θ e g) {a : ℝ≥0} (ha : a < e.lifetime)
    (t : Set.Icc (0 : ℝ) a) :
    heightPrefixAE θ a (excursionRestrict a e) t = excursionHeight θ e ⟨t, t.2.1⟩ := by
  let c : C(Set.Icc (0 : ℝ) a, ℝ) :=
    ⟨fun t => excursionHeight θ e ⟨t, t.2.1⟩,
      (excursionHeight θ e).continuous.comp
        (continuous_subtype_val.subtype_mk fun t => t.2.1)⟩
  have hc : IsPrefixHeightVersion θ a (excursionRestrict a e) c := by
    refine ⟨excursionHeight_zero θ e, ?_⟩
    have hh := (isExcursionHeightVersion_excursionHeight θ e he).2.2
    have hh' := ae_restrict_of_ae_restrict_of_subset
      (Ioo_subset_Ioo_right (show (a : ℝ) ≤ e.lifetime from ha.le)) hh
    filter_upwards [hh', ae_restrict_mem measurableSet_Ioo] with s hs hmem
    have hsa : s.toNNReal ≤ a := Real.toNNReal_le_iff_le_coe.mpr hmem.2.le
    have hp : Set.projIcc 0 (a : ℝ) a.2 s = ⟨s, hmem.1.le, hmem.2.le⟩ :=
      Set.projIcc_of_mem a.2 ⟨hmem.1.le, hmem.2.le⟩
    have ht : (⟨s, hmem.1.le⟩ : ℝ≥0) = s.toNNReal :=
      (Real.toNNReal_of_nonneg hmem.1.le).symm
    change excursionHeight θ e ⟨(Set.projIcc 0 (a : ℝ) a.2 s : ℝ),
      (Set.projIcc 0 (a : ℝ) a.2 s).2.1⟩ = _
    rw [hp]
    change excursionHeight θ e ⟨s, hmem.1.le⟩ = _
    rw [ht, hs]
    exact heightUniv_eq_of_restrict_eq θ a e.path _
      (restrict_extendConst a (excursionRestrict a e)).symm _ hsa
  exact congrArg (fun d : C(Set.Icc (0 : ℝ) a, ℝ) => d t)
    (heightPrefixAE_eq_of_isPrefixHeightVersion θ a (excursionRestrict a e) c hc)

end BGW.StableTrees
