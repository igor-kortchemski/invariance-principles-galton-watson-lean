/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightBridges
public import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap
import BGW.StableTrees.HeightBridgesCompact
import Mathlib.MeasureTheory.Function.FactorsThrough
import Mathlib.Topology.Order.Basic

/-!
# Deterministic reconstruction of continuous heights

Rational evaluations determine a continuous height uniquely, including on a singleton horizon.
Constant extension preserves the compact prefix literally.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal Classical
open BGW.Skorokhod

namespace BGW.StableTrees

/-- `t` is a rational time. -/
def IsRationalTime (t : ℝ≥0) : Prop := ∃ q : ℚ, (q : ℝ) = t

/-- **The continuous height process**: the continuous function agreeing with `heightUniv θ f` at
every rational time when one exists (it is then unique), the zero function otherwise. -/
noncomputable def heightLoc (θ : ℝ) (f : DLoc) : ℝ≥0 → ℝ :=
  if h : ∃ g : C(ℝ≥0, ℝ), ∀ t : ℝ≥0, IsRationalTime t → g t = heightUniv θ f t then
    ⇑(Classical.choose h) else fun _ => 0

/-- Every path of `heightLoc` is continuous. -/
theorem continuous_heightLoc (θ : ℝ) (f : DLoc) : Continuous (heightLoc θ f) := by
  unfold heightLoc
  split_ifs with h
  · exact (Classical.choose h).continuous
  · exact continuous_const

/-- Rational nonnegative times are dense. -/
theorem dense_isRationalTime : Dense {t : ℝ≥0 | IsRationalTime t} := by
  apply dense_iff_exists_between.mpr
  intro a b hab
  obtain ⟨q, haq, hqb⟩ := exists_rat_btwn (show (a : ℝ) < b from hab)
  have hq : 0 ≤ (q : ℝ) := a.2.trans haq.le
  exact ⟨⟨q, hq⟩, ⟨q, rfl⟩, haq, hqb⟩

/-- Continuous extensions of the same rational heights coincide. -/
theorem heightLoc_eq_of_rational_agreement (θ : ℝ) (f : DLoc) (g : C(ℝ≥0, ℝ))
    (hg : ∀ t : ℝ≥0, IsRationalTime t → g t = heightUniv θ f t) :
    heightLoc θ f = g := by
  have hex : ∃ g : C(ℝ≥0, ℝ), ∀ t : ℝ≥0,
      IsRationalTime t → g t = heightUniv θ f t := ⟨g, hg⟩
  rw [heightLoc, dite_eq_left hex]
  exact Continuous.ext_on dense_isRationalTime (Classical.choose hex).continuous g.continuous
    (fun t ht => (Classical.choose_spec hex t ht).trans (hg t ht).symm)

/-- The continuous height starts at `0` for every path (`height θ f 0 = 0` surely). -/
theorem heightLoc_zero (θ : ℝ) (f : DLoc) : heightLoc θ f 0 = 0 := by
  unfold heightLoc
  split_ifs with h
  · exact (Classical.choose_spec h 0 ⟨0, by simp⟩).trans (heightUniv_zero θ f)
  · rfl

/-- The continuous height is nonnegative for every path. -/
theorem heightLoc_nonneg (θ : ℝ) (f : DLoc) (t : ℝ≥0) : 0 ≤ heightLoc θ f t := by
  unfold heightLoc
  split_ifs with h
  · have hclosed : IsClosed {t : ℝ≥0 | 0 ≤ Classical.choose h t} :=
      isClosed_le continuous_const (Classical.choose h).continuous
    have hsub : {t : ℝ≥0 | IsRationalTime t} ⊆ {t | 0 ≤ Classical.choose h t} := by
      intro u hu
      change 0 ≤ Classical.choose h u
      rw [Classical.choose_spec h u hu]
      exact heightUniv_nonneg θ f u
    exact hclosed.closure_subset_iff.mpr hsub (dense_isRationalTime t)
  · exact le_rfl

/-- Extension of a path on `[0,T]` by its terminal value (the junk branch never occurs). -/
noncomputable def extendConst (T : ℝ≥0) (g : D (T : ℝ) ℝ) : DLoc :=
  if h : IsCadlag (fun u : ℝ≥0 => g (Set.projIcc 0 (T : ℝ) T.2 u)) then
    ⟨fun u => g (Set.projIcc 0 (T : ℝ) T.2 u), h⟩ else DLoc.zero

/-- **Prefix height map** on `[0,T]`: the continuous function on `[0,T]` agreeing with
`heightUniv` of `extendConst T g` at the rational times of `[0,T]` when one exists, `0`
otherwise. -/
noncomputable def heightPrefix (θ : ℝ) (T : ℝ≥0) (g : D (T : ℝ) ℝ) :
    C(Set.Icc (0 : ℝ) T, ℝ) :=
  if h : ∃ c : C(Set.Icc (0 : ℝ) T, ℝ), ∀ t : Set.Icc (0 : ℝ) T, (∃ q : ℚ, (q : ℝ) = t) →
      c t = heightUniv θ (extendConst T g) ⟨t, t.2.1⟩ then Classical.choose h else 0

private theorem clamp_eq_min (T u : ℝ≥0) :
    Set.projIcc 0 (T : ℝ) T.2 u =
      ⟨min (u : ℝ) T, le_min u.2 T.2, min_le_right _ _⟩ := by
  apply Subtype.ext
  change max 0 (min (T : ℝ) u) = min (u : ℝ) T
  rw [min_comm]
  exact max_eq_right (le_min u.2 T.2)

/-- Constant extension is càdlàg, including at the terminal time. -/
theorem isCadlag_extendConst_fun (T : ℝ≥0) (g : D (T : ℝ) ℝ) :
    IsCadlag (fun u : ℝ≥0 => g (Set.projIcc 0 (T : ℝ) T.2 u)) := by
  have he : (fun u : ℝ≥0 => g (Set.projIcc 0 (T : ℝ) T.2 u)) =
      (horizonExtension T g).1 := by
    funext u
    exact congrArg g (clamp_eq_min T u)
  rw [he]
  exact (horizonExtension T g).2

private theorem extendConst_eq_horizonExtension (T : ℝ≥0) (g : D (T : ℝ) ℝ) :
    extendConst T g = horizonExtension T g := by
  erw [extendConst, dite_eq_left (isCadlag_extendConst_fun T g)]
  apply Subtype.ext
  funext u
  exact congrArg g (clamp_eq_min T u)

/-- Restricting constant extension gives the original path. -/
theorem restrict_extendConst (T : ℝ≥0) (g : D (T : ℝ) ℝ) :
    DLoc.restrict T (extendConst T g) = g := by
  rw [extendConst_eq_horizonExtension]
  exact restrict_horizonExtension T g

/-- Constant extension is measurable for the evaluation sigma algebra. -/
theorem measurable_extendConst (T : ℝ≥0) : Measurable (extendConst T) := by
  have he : extendConst T = horizonExtension T := funext (extendConst_eq_horizonExtension T)
  rw [he]
  exact measurable_horizonExtension T

/-- **Literal prefix locality** of the raw height: `height θ f t` reads `f` only on `[0,t]`. -/
theorem height_eq_of_restrict_eq (θ : ℝ) (T : ℝ≥0) (f g : DLoc)
    (hfg : DLoc.restrict T f = DLoc.restrict T g) (t : ℝ≥0) (ht : t ≤ T) :
    height θ f t = height θ g t := by
  apply (measurable_height_prefix θ t).factorsThrough
  apply BGW.Skorokhod.ext
  intro u
  exact congrArg (fun p : D (T : ℝ) ℝ => p ⟨u, u.2.1, u.2.2.trans ht⟩) hfg

/-- Rational times are dense in a compact nonnegative interval. -/
theorem dense_prefix_rationals (T : ℝ≥0) :
    Dense {t : Set.Icc (0 : ℝ) T | ∃ q : ℚ, (q : ℝ) = t} := by
  by_cases hT : T = 0
  · subst T
    have he : {t : Set.Icc (0 : ℝ) (0 : ℝ≥0) | ∃ q : ℚ, (q : ℝ) = t} = univ := by
      ext t
      simp only [mem_ofPred_eq, mem_univ, iff_true]
      exact ⟨0, by simpa using (le_antisymm t.2.2 t.2.1).symm⟩
    rw [he]
    exact dense_univ
  · have hTpos : (0 : ℝ) < T := by exact_mod_cast pos_iff_ne_zero.mpr hT
    let : Nontrivial (Set.Icc (0 : ℝ) (T : ℝ)) :=
      ⟨⟨⟨0, le_rfl, hTpos.le⟩, ⟨T, hTpos.le, le_rfl⟩, by
        intro he
        exact hTpos.ne (congrArg Subtype.val he)⟩⟩
    apply dense_iff_exists_between.mpr
    intro a b hab
    obtain ⟨q, haq, hqb⟩ := exists_rat_btwn (show (a : ℝ) < b from hab)
    exact ⟨⟨q, a.2.1.trans haq.le, hqb.le.trans b.2.2⟩, ⟨q, rfl⟩, haq, hqb⟩

/-- Rational times in a compact nonnegative interval determine continuous functions. -/
theorem continuousMap_ext_rational (T : ℝ≥0) (c d : C(Set.Icc (0 : ℝ) T, ℝ))
    (h : ∀ t : Set.Icc (0 : ℝ) T, (∃ q : ℚ, (q : ℝ) = t) → c t = d t) : c = d :=
  DFunLike.coe_injective (Continuous.ext_on (dense_prefix_rationals T) c.continuous
    d.continuous h)

/-- The fixed-time height is measurable. -/
theorem measurable_height_fixed (θ : ℝ) (t : ℝ≥0) : Measurable (fun f : DLoc => height θ f t) :=
  Measurable.comp (g := fun p : ℝ≥0 × DLoc => height θ p.2 p.1)
    (f := fun f : DLoc => (t, f)) (measurable_height_uncurry θ)
    (measurable_const.prodMk measurable_id)

/-- **Deterministic reconstruction**: a continuous function on `[0,T]` agreeing with
`heightUniv θ f` at the rational times of `[0,T]` is the prefix height of `f` (no law
involved; used by H04 under the excursion measures). -/
theorem heightPrefix_eq_of_rational_agreement (θ : ℝ) (T : ℝ≥0) (f : DLoc)
    (c : C(Set.Icc (0 : ℝ) T, ℝ))
    (hc : ∀ t : Set.Icc (0 : ℝ) T, IsRationalTime ⟨t, t.2.1⟩ →
      c t = heightUniv θ f ⟨t, t.2.1⟩) :
    heightPrefix θ T (DLoc.restrict T f) = c := by
  have hh (t : Set.Icc (0 : ℝ) T) :
      heightUniv θ (extendConst T (DLoc.restrict T f)) ⟨t, t.2.1⟩ =
        heightUniv θ f ⟨t, t.2.1⟩ :=
    heightUniv_eq_of_restrict_eq θ T _ f (restrict_extendConst T _) _ t.2.2
  have hex : ∃ d : C(Set.Icc (0 : ℝ) T, ℝ), ∀ t : Set.Icc (0 : ℝ) T,
      (∃ q : ℚ, (q : ℝ) = t) →
        d t = heightUniv θ (extendConst T (DLoc.restrict T f)) ⟨t, t.2.1⟩ := by
    exact ⟨c, fun t ht => (hc t ht).trans (hh t).symm⟩
  rw [heightPrefix, dite_eq_left hex]
  apply continuousMap_ext_rational T
  intro t ht
  exact (Classical.choose_spec hex t ht).trans ((hh t).trans (hc t ht).symm)

end BGW.StableTrees
