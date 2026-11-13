/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLoc
public import BGW.Skorokhod.PolishTightness
import Mathlib.Data.NNRat.Encodable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

import BGW.Probability.NNReal

/-!
# The tagged excursion carrier

This module defines càdlàg excursions together with a positive lifetime tag.  It proves that the
carrier is standard Borel, constructs excursion cuts, and establishes space-time scaling and
normalization with their measurability and group laws (J. Bertoin, *Lévy Processes*, Cambridge
University Press, 1996, Chapter IV; L. Chaumont, Excursion normalisée, méandre et pont pour les
processus de Lévy stables, Bull. Sci. Math. 121 (1997), 377–403).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod

open BGW.Probability

namespace BGW.StableTrees

private theorem isCadlag_comp_strictMono {f : ℝ≥0 → ℝ} (hf : IsCadlag f)
    {φ : ℝ≥0 → ℝ≥0} (hφ : Continuous φ) (hmono : StrictMono φ) :
    IsCadlag (fun t => f (φ t)) := by
  constructor
  · intro t
    have hmap : MapsTo φ (Set.Ioi t) (Set.Ioi (φ t)) := fun _ hu => hmono hu
    exact (hf.isRightContinuous (φ t)).comp
      hφ.continuousAt.continuousWithinAt hmap
  · intro t
    obtain ⟨l, hl⟩ := hf.tendsto_nhdsLT (φ t)
    have hleft : Tendsto φ (𝓝[Set.Iio t] t) (𝓝[Set.Iio (φ t)] (φ t)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hφ.continuousAt, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with u hu
      exact hmono hu
    exact ⟨l, hl.comp hleft⟩

/-- Stopping a càdlàg path at a deterministic time is càdlàg. -/
theorem isCadlag_stopLoc (a : ℝ≥0) (f : DLoc) : IsCadlag (fun t : ℝ≥0 => f.1 (min t a)) := by
  constructor
  · intro t
    by_cases ht : t < a
    · have hcont : Continuous (fun u : ℝ≥0 => min u a) := continuous_id.min continuous_const
      have hmap : MapsTo (fun u : ℝ≥0 => min u a) (Set.Ioi t)
          (Set.Ioi (min t a)) := by
        intro u hu
        change min t a < min u a
        rw [min_eq_left ht.le]
        exact lt_min hu ht
      exact ContinuousWithinAt.comp (x := t) (f := fun u : ℝ≥0 => min u a)
        (f.2.isRightContinuous (min t a)) hcont.continuousAt.continuousWithinAt hmap
    · have ha : a ≤ t := le_of_not_gt ht
      have hconst : ∀ u ∈ Set.Ioi t, min u a = min t a := by
        intro u hu
        simp [min_eq_right ha, min_eq_right (ha.trans hu.le)]
      exact tendsto_nhdsWithin_congr (fun u hu => congrArg f.1 (hconst u hu).symm)
        tendsto_const_nhds
  · intro t
    by_cases ht : t ≤ a
    · have hmap : MapsTo (fun u : ℝ≥0 => min u a) (Set.Iio t)
          (Set.Iio (min t a)) := by
        intro u hu
        have hua : u ≤ a := hu.le.trans ht
        simpa [min_eq_left hua, min_eq_left ht] using hu
      obtain ⟨l, hl⟩ := f.2.tendsto_nhdsLT (min t a)
      have hcont : Continuous (fun u : ℝ≥0 => min u a) := continuous_id.min continuous_const
      have hleft : Tendsto (fun u : ℝ≥0 => min u a) (𝓝[Set.Iio t] t)
          (𝓝[Set.Iio (min t a)] (min t a)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hcont.continuousAt, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact hmap hu
      exact ⟨l, hl.comp hleft⟩
    · have ha : a < t := lt_of_not_ge ht
      have hev : ∀ᶠ u in 𝓝[Set.Iio t] t, a < u :=
        (eventually_gt_nhds ha).filter_mono nhdsWithin_le_nhds
      have hfg : (fun u : ℝ≥0 => f.1 (min u a)) =ᶠ[𝓝[Set.Iio t] t]
          fun _ => f.1 (min t a) := by
        filter_upwards [hev] with u hu
        simp [min_eq_right hu.le, min_eq_right ha.le]
      exact ⟨f.1 (min t a), (tendsto_congr' hfg).2 tendsto_const_nhds⟩

/-- Stopping a local path at a deterministic time: `t ↦ f (min t a)`. -/
noncomputable def stopLoc (a : ℝ≥0) (f : DLoc) : DLoc :=
  ⟨fun t => f.1 (min t a), isCadlag_stopLoc a f⟩

/-- The constant zero local path. -/
noncomputable def zeroLoc : DLoc := ⟨fun _ => 0, IsCadlag.const⟩

/-- The path of the cut of `f` between times `g` and `d`: `t ↦ f (min (g+t) d) - f g`
(for `g ≤ d`). -/
noncomputable def cutPath (g d : ℝ≥0) (f : DLoc) : DLoc :=
  stopLoc (d - g) (DLoc.shift g f)

/-- The valid-excursion conditions on a (path, tag) pair: starts at `0`, nonnegative, identically
zero at and after the tag. -/
def IsExcursionTag (p : DLoc × Set.Ioi (0 : ℝ≥0)) : Prop :=
  p.1.1 0 = 0 ∧ (∀ t, 0 ≤ p.1.1 t) ∧ ∀ t : ℝ≥0, (p.2 : ℝ≥0) ≤ t → p.1.1 t = 0

/-- The tagged excursion carrier (Borel subtype of `DLoc × Ioi 0`). -/
def Excursion : Type := {p : DLoc × Set.Ioi (0 : ℝ≥0) // IsExcursionTag p}

noncomputable instance : MeasurableSpace Excursion :=
  (inferInstance : MeasurableSpace {p : DLoc × Set.Ioi (0 : ℝ≥0) // IsExcursionTag p})

namespace Excursion

/-- The path coordinate. -/
def path (e : Excursion) : DLoc := e.1.1
/-- The tagged lifetime. -/
def lifetime (e : Excursion) : ℝ≥0 := e.1.2
/-- The tagged lifetime as a positive real. -/
def lifetimePos (e : Excursion) : Set.Ioi (0 : ℝ) := ⟨(e.lifetime : ℝ), NNReal.coe_pos.2 e.1.2.2⟩

/-- The lifetime tag of an excursion is positive. -/
theorem lifetime_pos (e : Excursion) : 0 < e.lifetime := e.1.2.2

end Excursion

/-- Cut-validity: between times `g < d`, `f d = f g` and `f ≥ f g` on `[g, d]`.

A valid cut uses the post-jump value `f g` as the base level (the cut path is `f(g + ·) - f g`), so
`excursionCut` never represents an excursion that starts with a jump out of the infimum; this is
consistent with `IsExcursionInterval` (in `BGW.StableTrees.ReflectedRestart`), which requires
`R g = 0`. -/
def cutValid (g d : ℝ≥0) (f : DLoc) : Prop :=
  g < d ∧ f.1 d = f.1 g ∧ ∀ t : ℝ≥0, g ≤ t → t ≤ d → f.1 g ≤ f.1 t

private lemma exists_nnrat_right_mem (f : DLoc) {t b : ℝ≥0} (htb : t < b)
    {s : Set ℝ} (hs : IsOpen s) (hmem : f.1 t ∈ s) :
    ∃ q : ℚ≥0, t < (q : ℝ≥0) ∧ (q : ℝ≥0) < b ∧ f.1 q ∈ s := by
  have hnhds : f.1 ⁻¹' s ∈ 𝓝[>] t := (f.2.isRightContinuous t) (hs.mem_nhds hmem)
  obtain ⟨u, hu, hsub⟩ := (mem_nhdsGT_iff_exists_mem_Ioc_Ioo_subset htb).1 hnhds
  obtain ⟨q, htq, hqu⟩ := exists_nnrat_btwn hu.1
  exact ⟨q, htq, hqu.trans_le hu.2, hsub ⟨htq, hqu⟩⟩

private lemma nonneg_iff_nnrat (f : DLoc) :
    (∀ t, 0 ≤ f.1 t) ↔ ∀ q : ℚ≥0, 0 ≤ f.1 q := by
  constructor
  · intro h q
    exact h _
  · intro h t
    by_contra ht
    have hneg : f.1 t < 0 := lt_of_not_ge ht
    obtain ⟨q, -, -, hq⟩ := exists_nnrat_right_mem f (b := t + 1) (by simp)
      isOpen_Iio hneg
    exact (not_lt_of_ge (h q)) hq

private lemma zero_tail_iff_nnrat (f : DLoc) (ζ : ℝ≥0) :
    (∀ t : ℝ≥0, ζ ≤ t → f.1 t = 0) ↔ ∀ q : ℚ≥0, ζ ≤ q → f.1 q = 0 := by
  constructor
  · intro h q hq
    exact h _ hq
  · intro h t ht
    by_contra hne
    obtain ⟨q, htq, -, hq⟩ := exists_nnrat_right_mem f (b := t + 1) (by simp)
      isOpen_compl_singleton hne
    exact hq (h q (ht.trans htq.le))

private lemma window_nonneg_iff_nnrat (g d : ℝ≥0) (f : DLoc) (hfd : f.1 d = f.1 g) :
    (∀ t : ℝ≥0, g ≤ t → t ≤ d → f.1 g ≤ f.1 t) ↔
      ∀ q : ℚ≥0, g ≤ q → (q : ℝ≥0) ≤ d → f.1 g ≤ f.1 q := by
  constructor
  · intro h q hgq hqd
    exact h _ hgq hqd
  · intro h t hgt htd
    by_cases hteq : t = d
    · subst t
      exact hfd.ge
    · have htl : t < d := lt_of_le_of_ne htd hteq
      by_contra hn
      have hn' : f.1 t < f.1 g := lt_of_not_ge hn
      obtain ⟨q, htq, hqd, hq⟩ := exists_nnrat_right_mem f htl isOpen_Iio hn'
      exact (not_lt_of_ge (h q (hgt.trans htq.le) hqd.le)) hq

/-- The cut of a valid window, with tag `d - g`, satisfies the excursion-tag conditions. -/
theorem isExcursionTag_cutPath {g d : ℝ≥0} {f : DLoc} (h : cutValid g d f) :
    IsExcursionTag (cutPath g d f, ⟨d - g, tsub_pos_of_lt h.1⟩) := by
  have hadd (t : ℝ≥0) : g + min t (d - g) = min (g + t) d := by
    rw [add_min, add_tsub_cancel_of_le h.1.le]
  refine ⟨?_, ?_, ?_⟩
  · change f.1 (g + min 0 (d - g)) - f.1 g = 0
    simp
  · intro t
    change 0 ≤ f.1 (g + min t (d - g)) - f.1 g
    rw [sub_nonneg, hadd]
    exact h.2.2 _ (le_min (by simp) h.1.le) (min_le_right _ _)
  · intro t ht
    change f.1 (g + min t (d - g)) - f.1 g = 0
    have hd : d ≤ g + t := by
      rw [← add_tsub_cancel_of_le h.1.le]
      simpa only [add_comm] using add_le_add_left ht g
    rw [hadd, min_eq_right hd, h.2.1, sub_self]

/-- Measurability of the validity predicate: a Borel subset of `DLoc × Ioi 0`. -/
theorem measurableSet_isExcursionTag :
    MeasurableSet {p : DLoc × Set.Ioi (0 : ℝ≥0) | IsExcursionTag p} := by
  have hstart : MeasurableSet {p : DLoc × Set.Ioi (0 : ℝ≥0) | p.1.1 0 = 0} :=
    measurableSet_eq_fun ((DLoc.measurable_eval 0).comp measurable_fst) measurable_const
  have hnonneg : MeasurableSet {p : DLoc × Set.Ioi (0 : ℝ≥0) |
      ∀ q : ℚ≥0, 0 ≤ p.1.1 q} := by
    rw [Set.ofPred_forall]
    exact MeasurableSet.iInter fun q =>
      measurableSet_le measurable_const ((DLoc.measurable_eval _).comp measurable_fst)
  have htail : MeasurableSet {p : DLoc × Set.Ioi (0 : ℝ≥0) |
      ∀ q : ℚ≥0, (p.2 : ℝ≥0) ≤ q → p.1.1 q = 0} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro q
    have hset : {p : DLoc × Set.Ioi (0 : ℝ≥0) | (p.2 : ℝ≥0) ≤ q → p.1.1 q = 0} =
        {p | (q : ℝ≥0) < p.2} ∪ {p | p.1.1 q = 0} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      by_cases hq : (p.2 : ℝ≥0) ≤ q
      · simp [hq]
      · simp [hq, lt_of_not_ge hq]
    rw [hset]
    exact (measurableSet_lt measurable_const
      (measurable_subtype_coe.comp measurable_snd)).union
      (measurableSet_eq_fun ((DLoc.measurable_eval _).comp measurable_fst) measurable_const)
  rw [show {p : DLoc × Set.Ioi (0 : ℝ≥0) | IsExcursionTag p} =
      {p | p.1.1 0 = 0} ∩ {p | ∀ q : ℚ≥0, 0 ≤ p.1.1 q} ∩
        {p | ∀ q : ℚ≥0, (p.2 : ℝ≥0) ≤ q → p.1.1 q = 0} by
    ext p
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, IsExcursionTag]
    rw [nonneg_iff_nnrat, zero_tail_iff_nnrat]
    tauto]
  exact (hstart.inter hnonneg).inter htail

/-- **Compatible families form a Borel set**: the integer-horizon compatible families are a
measurable subset of the countable product of the spaces `D (n+1) ℝ`. -/
theorem measurableSet_compatibleFamilies :
    MeasurableSet {p : (n : ℕ) → D ((n : ℝ) + 1) ℝ | ∀ n : ℕ,
      BGW.Skorokhod.restrict (strictMono_succHorizon.monotone (Nat.le_succ n)) (p (n + 1)) =
        p n} := BGW.Skorokhod.measurableSet_compatible _ strictMono_succHorizon

/-- **`DLoc` is standard Borel** (measurably equivalent to the Borel set of compatible families
in a countable product of standard Borel spaces `D (n+1) ℝ`). -/
instance : StandardBorelSpace DLoc := by
  let _ : StandardBorelSpace (CompatiblePaths (fun n : ℕ => (n : ℝ) + 1)
      strictMono_succHorizon) :=
    (BGW.Skorokhod.measurableSet_compatible _ strictMono_succHorizon).standardBorel
  let _ := upgradeStandardBorel (CompatiblePaths (fun n : ℕ => (n : ℝ) + 1)
    strictMono_succHorizon)
  let e := DLoc.measurableEquivCompatible
  let τ : TopologicalSpace DLoc :=
    (inferInstance : TopologicalSpace (CompatiblePaths (fun n : ℕ => (n : ℝ) + 1)
      strictMono_succHorizon)).induced e
  have hpolish : @PolishSpace DLoc τ := e.toEquiv.polishSpace_induced
  have hborel : @BorelSpace DLoc τ inferInstance := by
    constructor
    rw [borel_comap, ← BorelSpace.measurable_eq]
    exact e.measurableEmbedding.comap_eq.symm
  exact ⟨⟨τ, hborel, hpolish⟩⟩

/-- **Standard Borel.** The carrier is a standard Borel space (through
`DLoc.measurableEquivCompatible` and the Borel compatible-family subset of the countable product
of Polish `D (n+1) ℝ`; no closedness or J1-completeness is assumed). -/
instance : StandardBorelSpace Excursion := by
  let _ : PolishSpace (Set.Ioi (0 : ℝ≥0)) := isOpen_Ioi.polishSpace
  exact measurableSet_isExcursionTag.standardBorel

/-- The junk excursion: zero path with tag one. -/
noncomputable def junkExcursion : Excursion :=
  ⟨(zeroLoc, ⟨1, Set.mem_Ioi.2 one_pos⟩), by
    refine ⟨rfl, fun t => le_refl _, fun t _ => rfl⟩⟩

/-- Measurability of the path coordinate. -/
theorem measurable_excursion_path : Measurable (Excursion.path) :=
  measurable_fst.comp measurable_subtype_coe

/-- Measurability of the tagged lifetime. -/
theorem measurable_excursion_lifetime : Measurable (Excursion.lifetime) :=
  measurable_subtype_coe.comp (measurable_snd.comp measurable_subtype_coe)

/-- The positive-real lifetime coordinate is measurable. -/
theorem measurable_lifetimePos : Measurable Excursion.lifetimePos :=
  Measurable.subtype_mk measurable_excursion_lifetime.coe_nnreal_real

/-- Measurability of each coordinate evaluation `e ↦ e(t)`. -/
theorem measurable_excursion_eval (t : ℝ≥0) : Measurable (fun e : Excursion => e.path.1 t) :=
  (DLoc.measurable_eval t).comp measurable_excursion_path

/-- **Joint evaluation** `(e, t) ↦ e(t)` is measurable. -/
theorem measurable_excursion_eval₂ :
    Measurable (fun p : Excursion × ℝ≥0 => p.1.path.1 p.2) :=
  DLoc.measurable_eval₂.comp
    (measurable_excursion_path.comp measurable_fst |>.prodMk measurable_snd)

/-- `e ↦ e(ζ(e))` evaluates to `0` (the path is stopped at the tag), so evaluation at the tag is
trivially measurable; kept as the sanity statement that the tag convention is "zero at the tag". -/
theorem excursion_path_zero_at_lifetime (e : Excursion) : e.path.1 e.lifetime = 0 :=
  e.2.2.2 _ le_rfl

/-- Cutting a path at a window `[g, d]`: the excursion with path `t ↦ f (min (g+t) d) - f g` and
tag `d - g` when the cut is valid, the junk excursion otherwise.  A valid cut is based at the
post-jump value `f g`, so an excursion starting with a jump out of the infimum is never
represented (see `cutValid`). -/
noncomputable def excursionCut (g d : ℝ≥0) (f : DLoc) : Excursion :=
  letI := Classical.propDecidable (cutValid g d f)
  if h : cutValid g d f then
    ⟨(cutPath g d f, ⟨d - g, tsub_pos_of_lt h.1⟩), isExcursionTag_cutPath h⟩
  else junkExcursion

/-- **Junk branch.** -/
theorem excursionCut_of_not_cutValid {g d : ℝ≥0} {f : DLoc} (h : ¬ cutValid g d f) :
    excursionCut g d f = junkExcursion := by
  unfold excursionCut
  simp [h]

/-- **Exact evaluation formula** for cutting between two finite times with equal values. -/
theorem excursionCut_eval {g d : ℝ≥0} {f : DLoc} (h : cutValid g d f) (t : ℝ≥0) :
    (excursionCut g d f).path.1 t = f.1 (min (g + t) d) - f.1 g := by
  classical
  simp [excursionCut, h, Excursion.path]
  change f.1 (g + min t (d - g)) - f.1 g = f.1 (min (g + t) d) - f.1 g
  rw [add_min, add_tsub_cancel_of_le h.1.le]

/-- The lifetime of a valid cut is the window length. -/
theorem excursionCut_lifetime {g d : ℝ≥0} {f : DLoc} (h : cutValid g d f) :
    (excursionCut g d f).lifetime = d - g := by
  classical
  simp [excursionCut, h, Excursion.lifetime]

/-- The validity set is jointly measurable in `(g, d, f)`. -/
theorem measurableSet_cutValid :
    MeasurableSet {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} := by
  have hg : Measurable (fun p : ℝ≥0 × ℝ≥0 × DLoc => p.1) := measurable_fst
  have hd : Measurable (fun p : ℝ≥0 × ℝ≥0 × DLoc => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hf : Measurable (fun p : ℝ≥0 × ℝ≥0 × DLoc => p.2.2) :=
    measurable_snd.comp measurable_snd
  have hevg : Measurable (fun p : ℝ≥0 × ℝ≥0 × DLoc => p.2.2.1 p.1) :=
    DLoc.measurable_eval₂.comp (hf.prodMk hg)
  have hevd : Measurable (fun p : ℝ≥0 × ℝ≥0 × DLoc => p.2.2.1 p.2.1) :=
    DLoc.measurable_eval₂.comp (hf.prodMk hd)
  have hstart : MeasurableSet {p : ℝ≥0 × ℝ≥0 × DLoc | p.1 < p.2.1} :=
    measurableSet_lt hg hd
  have heq : MeasurableSet {p : ℝ≥0 × ℝ≥0 × DLoc | p.2.2.1 p.2.1 = p.2.2.1 p.1} :=
    measurableSet_eq_fun hevd hevg
  have hwindow : MeasurableSet {p : ℝ≥0 × ℝ≥0 × DLoc |
      ∀ q : ℚ≥0, p.1 ≤ q → (q : ℝ≥0) ≤ p.2.1 → p.2.2.1 p.1 ≤ p.2.2.1 q} := by
    rw [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro q
    have hset : {p : ℝ≥0 × ℝ≥0 × DLoc |
        p.1 ≤ q → (q : ℝ≥0) ≤ p.2.1 → p.2.2.1 p.1 ≤ p.2.2.1 q} =
        ({p | (q : ℝ≥0) < p.1} ∪ {p | p.2.1 < (q : ℝ≥0)}) ∪
          {p | p.2.2.1 p.1 ≤ p.2.2.1 q} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_union]
      by_cases hgq : p.1 ≤ (q : ℝ≥0)
      · by_cases hqd : (q : ℝ≥0) ≤ p.2.1
        · simp [hgq, hqd]
        · simp [hgq, hqd, lt_of_not_ge hqd]
      · simp [hgq, lt_of_not_ge hgq]
    rw [hset]
    exact ((measurableSet_lt measurable_const hg).union
      (measurableSet_lt hd measurable_const)).union
      (measurableSet_le hevg ((DLoc.measurable_eval _).comp hf))
  rw [show {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} =
      {p | p.1 < p.2.1} ∩ {p | p.2.2.1 p.2.1 = p.2.2.1 p.1} ∩
        {p | ∀ q : ℚ≥0, p.1 ≤ (q : ℝ≥0) → (q : ℝ≥0) ≤ p.2.1 →
          p.2.2.1 p.1 ≤ p.2.2.1 q} by
    ext p
    change cutValid p.1 p.2.1 p.2.2 ↔ _
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
    constructor
    · rintro ⟨hgd, hfd, hw⟩
      exact ⟨⟨hgd, hfd⟩, (window_nonneg_iff_nnrat _ _ _ hfd).1 hw⟩
    · rintro ⟨⟨hgd, hfd⟩, hw⟩
      exact ⟨hgd, hfd, (window_nonneg_iff_nnrat _ _ _ hfd).2 hw⟩]
  exact (hstart.inter heq).inter hwindow

private theorem measurable_dLoc_of_eval {α : Type*} [MeasurableSpace α] (F : α → DLoc)
    (h : ∀ t : ℝ≥0, Measurable fun x => (F x).1 t) : Measurable F := by
  rw [measurable_iff_comap_le]
  change (⨆ t : ℝ≥0, MeasurableSpace.comap (DLoc.eval t) inferInstance).comap F ≤ _
  rw [MeasurableSpace.comap_iSup, iSup_le_iff]
  intro t
  rw [MeasurableSpace.comap_comp]
  change MeasurableSpace.comap (fun x => (F x).1 t) inferInstance ≤ _
  exact (h t).comap_le

/-- **Joint cut measurability**: `(g, d, f) ↦ excursionCut g d f` is measurable jointly (not
merely at fixed times). -/
theorem measurable_excursionCut :
    Measurable (fun p : ℝ≥0 × ℝ≥0 × DLoc => excursionCut p.1 p.2.1 p.2.2) := by
  classical
  unfold excursionCut
  refine Measurable.dite (s := {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2})
    (f := fun q : {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} =>
      (⟨(cutPath q.1.1 q.1.2.1 q.1.2.2,
        ⟨q.1.2.1 - q.1.1, tsub_pos_of_lt q.2.1⟩), isExcursionTag_cutPath q.2⟩ : Excursion))
    (g := fun _ => junkExcursion) ?_ ?_ measurableSet_cutValid
  · apply Measurable.subtype_mk
    apply Measurable.prodMk
    · apply measurable_dLoc_of_eval
      intro t
      have hg : Measurable (fun p : {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} =>
          p.1.1) := measurable_fst.comp measurable_subtype_coe
      have hd : Measurable (fun p : {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} =>
          p.1.2.1) := measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)
      have hf : Measurable (fun p : {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} =>
          p.1.2.2) := measurable_snd.comp (measurable_snd.comp measurable_subtype_coe)
      have hplus : Measurable (fun p : {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} =>
          (p.1.2.2, p.1.1 + min t (p.1.2.1 - p.1.1))) :=
        hf.prodMk (hg.add (measurable_const.min (hd.sub hg)))
      have hbase : Measurable (fun p : {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} =>
          (p.1.2.2, p.1.1)) := hf.prodMk hg
      have hm := (DLoc.measurable_eval₂.comp hplus).sub
        (DLoc.measurable_eval₂.comp hbase)
      change Measurable (fun p : {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} =>
        p.1.2.2.1 (p.1.1 + min t (p.1.2.1 - p.1.1)) - p.1.2.2.1 p.1.1) at hm
      simpa only [cutPath, stopLoc, DLoc.shift, Excursion.path] using hm
    · have hg : Measurable (fun p : {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} =>
          p.1.1) := measurable_fst.comp measurable_subtype_coe
      have hd : Measurable (fun p : {p : ℝ≥0 × ℝ≥0 × DLoc | cutValid p.1 p.2.1 p.2.2} =>
          p.1.2.1) := measurable_fst.comp (measurable_snd.comp measurable_subtype_coe)
      exact Measurable.subtype_mk (hd.sub hg)
  · exact measurable_const

/-- Space-time scaling of a càdlàg path is càdlàg. -/
theorem isCadlag_scaleLoc (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (f : DLoc) :
    IsCadlag (fun t : ℝ≥0 => (c : ℝ) ^ (1 / θ) * f.1 (t / (c : ℝ).toNNReal)) := by
  have hc : 0 < (c : ℝ).toNNReal := Real.toNNReal_pos.2 c.2
  have htime : IsCadlag (fun t : ℝ≥0 => f.1 (t / (c : ℝ).toNNReal)) :=
    isCadlag_comp_strictMono f.2 (continuous_id.div_const _) (strictMono_div_right_of_pos hc)
  simpa only [Function.comp_def, Pi.mul_apply, id_eq] using
    htime.continuous_comp (continuous_const.mul continuous_id)

/-- Scaling of the underlying path: `t ↦ c^(1/θ) * f (t / c)`. -/
noncomputable def scaleLoc (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (f : DLoc) : DLoc :=
  ⟨fun t => (c : ℝ) ^ (1 / θ) * f.1 (t / (c : ℝ).toNNReal), isCadlag_scaleLoc θ c f⟩

/-- Scaling preserves the excursion-tag conditions (with tag `c ζ`). -/
theorem isExcursionTag_scale (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (e : Excursion) :
    IsExcursionTag (scaleLoc θ c e.path, ⟨(c : ℝ).toNNReal * e.lifetime,
      mul_pos (Real.toNNReal_pos.2 c.2) e.lifetime_pos⟩) := by
  have hc : 0 < (c : ℝ).toNNReal := Real.toNNReal_pos.2 c.2
  refine ⟨?_, ?_, ?_⟩
  · change (c : ℝ) ^ (1 / θ) * e.1.1.1 (0 / (c : ℝ).toNNReal) = 0
    simp [e.2.1]
  · intro t
    exact mul_nonneg (Real.rpow_nonneg c.2.le _) (e.2.2.1 _)
  · intro t ht
    change (c : ℝ) ^ (1 / θ) * e.1.1.1 (t / (c : ℝ).toNNReal) = 0
    have htime : e.lifetime ≤ t / (c : ℝ).toNNReal := by
      rw [le_div_iff₀ hc]
      simpa only [mul_comm] using ht
    rw [e.2.2.2 _ htime, mul_zero]

/-- **Excursion scaling `S_c`**: path `c^(1/θ) e(t/c)`, tag `c * ζ`; the lifetime multiplies
by `c`. -/
noncomputable def excursionScale (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (e : Excursion) : Excursion :=
  ⟨(scaleLoc θ c e.path, ⟨(c : ℝ).toNNReal * e.lifetime,
      mul_pos (Real.toNNReal_pos.2 c.2) e.lifetime_pos⟩), isExcursionTag_scale θ c e⟩

/-- Scaling multiplies the lifetime by `c`. -/
theorem excursionScale_lifetime (θ : ℝ) (c : Set.Ioi (0 : ℝ)) (e : Excursion) :
    ((excursionScale θ c e).lifetime : ℝ) = (c : ℝ) * e.lifetime := by
  simp [excursionScale, Excursion.lifetime, Real.coe_toNNReal _ c.2.le]

/-- **Scale group law** (identity). -/
theorem excursionScale_one (θ : ℝ) (e : Excursion) :
    excursionScale θ ⟨1, Set.mem_Ioi.2 one_pos⟩ e = e := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    funext t
    change (1 : ℝ) ^ (1 / θ) * e.path.1 (t / (1 : ℝ).toNNReal) = e.path.1 t
    simp
  · apply Subtype.ext
    change (1 : ℝ).toNNReal * e.lifetime = e.lifetime
    simp

/-- **Scale group law** (composition). -/
theorem excursionScale_mul (θ : ℝ) (c₁ c₂ : Set.Ioi (0 : ℝ)) (e : Excursion) :
    excursionScale θ c₁ (excursionScale θ c₂ e) =
      excursionScale θ ⟨(c₁ : ℝ) * c₂, Set.mem_Ioi.2 (mul_pos c₁.2 c₂.2)⟩ e := by
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    funext t
    simp only [excursionScale, scaleLoc, Excursion.path]
    change (c₁ : ℝ) ^ (1 / θ) * ((c₂ : ℝ) ^ (1 / θ) *
      e.path.1 ((t / (c₁ : ℝ).toNNReal) / (c₂ : ℝ).toNNReal)) =
      ((c₁ : ℝ) * c₂) ^ (1 / θ) * e.path.1 (t / ((c₁ : ℝ) * c₂).toNNReal)
    have htime : (t / (c₁ : ℝ).toNNReal) / (c₂ : ℝ).toNNReal =
        t / ((c₁ : ℝ) * c₂).toNNReal := by
      rw [div_div, Real.toNNReal_mul c₁.2.le]
    rw [htime, Real.mul_rpow c₁.2.le c₂.2.le, mul_assoc]
  · apply Subtype.ext
    change (c₁ : ℝ).toNNReal * ((c₂ : ℝ).toNNReal * e.lifetime) =
      ((c₁ : ℝ) * c₂).toNNReal * e.lifetime
    rw [Real.toNNReal_mul c₁.2.le, mul_assoc]

/-- Scaling is measurable at each fixed `c`. -/
theorem measurable_excursionScale (θ : ℝ) (c : Set.Ioi (0 : ℝ)) :
    Measurable (excursionScale θ c) := by
  apply Measurable.subtype_mk
  apply Measurable.prodMk
  · apply measurable_dLoc_of_eval
    intro t
    exact measurable_const.mul ((DLoc.measurable_eval _).comp measurable_excursion_path)
  · exact Measurable.subtype_mk (measurable_const.mul measurable_excursion_lifetime)

/-- Scaling is jointly measurable in `(c, e)`. -/
theorem measurable_excursionScale_joint (θ : ℝ) :
    Measurable (fun p : Set.Ioi (0 : ℝ) × Excursion => excursionScale θ p.1 p.2) := by
  apply Measurable.subtype_mk
  apply Measurable.prodMk
  · apply measurable_dLoc_of_eval
    intro t
    have hc : Continuous (fun c : Set.Ioi (0 : ℝ) => (c : ℝ) ^ (1 / θ)) :=
      continuous_subtype_val.rpow_const fun c => Or.inl c.2.ne'
    have hcnn : Measurable (fun p : Set.Ioi (0 : ℝ) × Excursion => (p.1 : ℝ).toNNReal) :=
      measurable_real_toNNReal.comp (measurable_subtype_coe.comp measurable_fst)
    have htime : Measurable (fun p : Set.Ioi (0 : ℝ) × Excursion =>
        p.2.path.1 (t / (p.1 : ℝ).toNNReal)) :=
      DLoc.measurable_eval₂.comp ((measurable_excursion_path.comp measurable_snd).prodMk
        (measurable_const.div hcnn))
    exact (hc.measurable.comp measurable_fst).mul htime
  · have hcnn : Measurable (fun p : Set.Ioi (0 : ℝ) × Excursion => (p.1 : ℝ).toNNReal) :=
      measurable_real_toNNReal.comp (measurable_subtype_coe.comp measurable_fst)
    exact Measurable.subtype_mk
      (hcnn.mul (measurable_excursion_lifetime.comp measurable_snd))

/-- **Normalization**: rescale to lifetime one, `S_{1/ζ} e`. -/
noncomputable def normalizeExc (θ : ℝ) (e : Excursion) : Excursion :=
  excursionScale θ ⟨((e.lifetime : ℝ≥0) : ℝ)⁻¹, inv_pos.2 (NNReal.coe_pos.2 e.lifetime_pos)⟩ e

/-- A normalized excursion has lifetime one. -/
theorem normalizeExc_lifetime (θ : ℝ) (e : Excursion) : (normalizeExc θ e).lifetime = 1 := by
  apply NNReal.eq
  change ((normalizeExc θ e).lifetime : ℝ) = (1 : ℝ)
  rw [normalizeExc, excursionScale_lifetime]
  exact inv_mul_cancel₀ (NNReal.coe_ne_zero.2 e.lifetime_pos.ne')

/-- **Measurable normalization** (variable positive scaling `c = 1/ζ(e)`; the raw functional need
not be J1-continuous). -/
theorem measurable_normalizeExc (θ : ℝ) : Measurable (normalizeExc θ) := by
  unfold normalizeExc
  let c : Excursion → Set.Ioi (0 : ℝ) := fun e =>
    ⟨(e.lifetime : ℝ)⁻¹, inv_pos.2 (NNReal.coe_pos.2 e.lifetime_pos)⟩
  have hc : Measurable c := Measurable.subtype_mk measurable_excursion_lifetime.coe_nnreal_real.inv
  have hpair : Measurable (fun e => (c e, e)) := hc.prodMk measurable_id
  simpa only [c, Function.comp_def] using (measurable_excursionScale_joint θ).comp hpair

/-- Restriction of an excursion to the horizon `[0, T]`, as a path in the sealed compact space. -/
noncomputable def excursionRestrict (T : ℝ≥0) (e : Excursion) : D (T : ℝ) ℝ :=
  DLoc.restrict T e.path

/-- Restriction is measurable, for the Borel `σ`-algebra of `D T ℝ`. -/
theorem measurable_excursionRestrict (T : ℝ≥0) : Measurable (excursionRestrict T) :=
  (DLoc.measurable_restrict T).comp measurable_excursion_path

/-- **Lifetime/shape map**: `e ↦ (ζ(e), normalized e)`. -/
noncomputable def shapeLifetime (θ : ℝ) (e : Excursion) : Set.Ioi (0 : ℝ) × Excursion :=
  (e.lifetimePos, normalizeExc θ e)

/-- **Inverse map** `(ζ, s) ↦ S_ζ s`. -/
noncomputable def fromShapeLifetime (θ : ℝ) (p : Set.Ioi (0 : ℝ) × Excursion) : Excursion :=
  excursionScale θ p.1 p.2

/-- The lifetime/shape decomposition is measurable. -/
theorem measurable_shapeLifetime (θ : ℝ) : Measurable (shapeLifetime θ) :=
  (Measurable.subtype_mk measurable_excursion_lifetime.coe_nnreal_real).prodMk
    (measurable_normalizeExc θ)

/-- Rebuilding an excursion from its lifetime and unit-lifetime shape is measurable. -/
theorem measurable_fromShapeLifetime (θ : ℝ) : Measurable (fromShapeLifetime θ) :=
  measurable_excursionScale_joint θ

/-- `fromShapeLifetime ∘ shapeLifetime = id` on all excursions. -/
theorem fromShapeLifetime_shapeLifetime (θ : ℝ) (e : Excursion) :
    fromShapeLifetime θ (shapeLifetime θ e) = e := by
  change excursionScale θ e.lifetimePos (normalizeExc θ e) = e
  rw [normalizeExc, excursionScale_mul]
  have hc : (e.lifetimePos : ℝ) * (e.lifetime : ℝ)⁻¹ = 1 := by
    exact mul_inv_cancel₀ (NNReal.coe_ne_zero.2 e.lifetime_pos.ne')
  simpa only [hc] using excursionScale_one θ e

/-- `shapeLifetime ∘ fromShapeLifetime = id` on (lifetime, unit-lifetime shape) pairs. -/
theorem shapeLifetime_fromShapeLifetime (θ : ℝ) (ζ : Set.Ioi (0 : ℝ)) (s : Excursion)
    (hs : s.lifetime = 1) : shapeLifetime θ (fromShapeLifetime θ (ζ, s)) = (ζ, s) := by
  apply Prod.ext
  · apply Subtype.ext
    change ((fromShapeLifetime θ (ζ, s)).lifetime : ℝ) = (ζ : ℝ)
    rw [fromShapeLifetime, excursionScale_lifetime, hs]
    simp
  · change normalizeExc θ (excursionScale θ ζ s) = s
    rw [normalizeExc, excursionScale_mul]
    have hl : (excursionScale θ ζ s).lifetime = (ζ : ℝ).toNNReal := by
      apply NNReal.eq
      rw [excursionScale_lifetime, hs]
      simp [Real.coe_toNNReal _ ζ.2.le]
    have hζ : (ζ : ℝ) ≠ 0 := (show (0 : ℝ) < ζ from ζ.2).ne'
    simpa only [hl, Real.coe_toNNReal _ ζ.2.le, inv_mul_cancel₀ hζ] using
      excursionScale_one θ s

end BGW.StableTrees
