/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLoc
public import BGW.Skorokhod.DLocShiftAt
public import BGW.StableTrees.StableLocalLaw
import BGW.StableTrees.StableLocalMarkov
import BGW.StableTrees.StableStrongMarkov
import BGW.StableTrees.StableRegularity
public import BGW.StableTrees.StableFirstPassage
public import BGW.StableTrees.StablePassageSubordinatorPath
import BGW.StableTrees.StablePassageSubordinatorLaplace
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Passage subordinator and local time at the minimum

The strict downward passage times of the spectrally positive stable process form a
càdlàg subordinator.  Its right-continuous inverse is the negative running infimum,
whose Stieltjes measure is carried by the zero set of the reflected path.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VII,
Section 1 and Chapter IV, for the local time at the infimum and its inverse.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

/-- The `ℝ≥0`-valued passage time (junk value `0` on `{T_x = ⊤}`, a null set). -/
noncomputable def passageTime (x : ℝ≥0) (f : DLoc) : ℝ≥0 := (firstPassageBelow x f).untopD 0

/-- First hitting time of `(-∞, -x]`, `H_x = inf{t | X_t ≤ -x}` (weak hitting, NOT strict). -/
noncomputable def firstHitBelow (x : ℝ≥0) (f : DLoc) : WithTop ℝ≥0 :=
  sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, t = u ∧ f.1 u ≤ -(x : ℝ)}

/-- The law of the passage time `T_x` under the local stable law, as a measure on `ℝ`
(finite reading `passageTime`). -/
noncomputable def passageLaw (θ : ℝ) (x : ℝ≥0) : Measure ℝ :=
  Measure.map (fun f : DLoc => ((passageTime x f : ℝ≥0) : ℝ)) (stableLocalLaw θ : Measure DLoc)

/-- `passageTime x` is measurable in the path. -/
theorem measurable_passageTime (x : ℝ≥0) : Measurable (passageTime x) := by
  exact (measurable_firstPassageBelow_uncurry.comp
    (measurable_const.prodMk measurable_id)).untopD 0

/-- Joint measurability of `(x, f) ↦ T_x(f)` (finite reading). -/
theorem measurable_passageTime_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => passageTime p.1 p.2) := by
  exact measurable_firstPassageBelow_uncurry.untopD 0

/-- `passageLaw θ x` is a probability measure (`x = 0` uses `T_0 = 0`). -/
theorem passageLaw_isProbabilityMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) :
    IsProbabilityMeasure (passageLaw θ x) := by
  have _hθ := hθ
  rw [passageLaw]
  infer_instance

/-! ### Pathwise structure: finiteness, monotonicity, strict right-continuity, `T_0 = 0` -/

/-- Almost surely, for every `x ≥ 0`, `T_x` is finite and equals its finite reading,
and `T_0 = 0`. -/
theorem ae_passageTime_eq_firstPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (∀ x : ℝ≥0, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0)) ∧
        passageTime 0 f = 0 := by
  filter_upwards [ae_firstPassageBelow_spec hθ,
    ae_strictPassage_zero_stableLocalLaw hθ] with f hf hzero
  have hzero' : firstPassageBelow 0 f = 0 := by
    simpa [firstPassageBelow] using hzero.2
  have hfin : ∀ x : ℝ≥0, firstPassageBelow x f < ⊤ := by
    intro x
    by_cases hx : x = 0
    · subst x
      rw [hzero']
      exact WithTop.coe_lt_top _
    · exact (hf.2 x (pos_iff_ne_zero.mpr hx)).1
  have hT : ∀ x : ℝ≥0, firstPassageBelow x f =
      (((firstPassageBelow x f).untopD 0 : ℝ≥0) : WithTop ℝ≥0) :=
    firstPassageBelow_eq_coe_untopD f hfin
  refine ⟨fun x => hT x, ?_⟩
  simp [passageTime, hzero']

/-- **Monotone, càdlàg, starts at `0`** Right-continuity
here is the one for the strict passage time `T_x = inf{t | X_t < -x}`. -/
theorem ae_isCadlag_monotone_passage {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      IsCadlag (fun x : ℝ≥0 => ((passageTime x f : ℝ≥0) : ℝ)) ∧
        Monotone (fun x : ℝ≥0 => passageTime x f) ∧ passageTime 0 f = 0 := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
  have hfin : ∀ x : ℝ≥0, firstPassageBelow x f < ⊤ := by
    intro x
    rw [hf.1 x]
    exact WithTop.coe_lt_top _
  exact ⟨isCadlag_untopD_firstPassageBelow f hfin,
    untopD_firstPassageBelow_mono f hfin, hf.2⟩

/-- Almost surely `T` is unbounded: `T_x → ∞` as `x → ∞`. -/
theorem ae_tendsto_passageTime_atTop {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      Tendsto (fun x : ℝ≥0 => passageTime x f) atTop atTop := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
  apply tendsto_atTop.2
  intro b
  let x : ℝ≥0 := Real.toNNReal (max (-runningInfLoc f b) 0 + 1)
  have hx0 : 0 ≤ max (-runningInfLoc f b) 0 + 1 := by positivity
  have hx : -runningInfLoc f b < (x : ℝ) := by
    rw [show (x : ℝ) = max (-runningInfLoc f b) 0 + 1 from Real.coe_toNNReal _ hx0]
    exact (le_max_left _ _).trans_lt (lt_add_one _)
  filter_upwards [eventually_ge_atTop x] with y hy
  by_contra hby
  have hylt : passageTime y f < b := lt_of_not_ge hby
  have hpass : firstPassageBelow y f < (b : WithTop ℝ≥0) := by
    rw [hf.1 y]
    exact_mod_cast hylt
  have hI := (runningInfLoc_lt_sandwich y b f).1 hpass
  have hxy' : (x : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  linarith

/-! ### Inverse relation with the running infimum (`L = -runningInf` is the local time) -/

/-- **`T` is the strict right inverse of `L = -runningInf`**: `T_x = inf{t | L_t > x}`.
This is a deterministic identity, valid for every path (bounded-below on
compacts), every `x ≥ 0`, and the `inf` over the empty set is `⊤`. -/
theorem firstPassageBelow_eq_inverseLocalTime (x : ℝ≥0) (f : DLoc) :
    firstPassageBelow x f =
      sInf {t : WithTop ℝ≥0 | ∃ u : ℝ≥0, t = u ∧ (x : ℝ) < -runningInfLoc f u} := by
  exact firstPassageBelow_eq_sInf_runningInf x f

/-- **Event sandwich for the running infimum, strict side.** For every path, level and time:
`{T_x < t} ⊆ {I_t < -x} ⊆ {T_x ≤ t}`. -/
theorem runningInf_lt_sandwich (x : ℝ≥0) (t : ℝ≥0) (f : DLoc) :
    (firstPassageBelow x f < (t : WithTop ℝ≥0) → runningInfLoc f t < -(x : ℝ)) ∧
      (runningInfLoc f t < -(x : ℝ) → firstPassageBelow x f ≤ (t : WithTop ℝ≥0)) := by
  exact runningInfLoc_lt_sandwich x t f

private lemma eval_le_of_firstHitBelow_eq_coe {f : DLoc} {x t : ℝ≥0}
    (hT : firstHitBelow x f = (t : WithTop ℝ≥0)) : f.1 t ≤ -(x : ℝ) := by
  by_contra h
  have ha : -(x : ℝ) < f.1 t := lt_of_not_ge h
  have he : ∀ᶠ s in 𝓝[Set.Ioi t] t, -(x : ℝ) < f.1 s :=
    (f.2.isRightContinuous t).eventually (isOpen_Ioi.mem_nhds ha)
  have hSet : {u : ℝ≥0 | -(x : ℝ) < f.1 u} ∈ 𝓝[Set.Ioi t] t := he
  rw [(nhdsGT_basis t).mem_iff] at hSet
  obtain ⟨b, htb, hb⟩ := hSet
  have hTb : firstHitBelow x f < (b : WithTop ℝ≥0) := by
    rw [hT]
    exact_mod_cast htb
  rw [firstHitBelow, sInf_lt_iff] at hTb
  obtain ⟨_, ⟨u, rfl, hu⟩, hub⟩ := hTb
  have hub' : u < b := by exact_mod_cast hub
  rcases lt_or_ge u t with hut | htu
  · have hle : firstHitBelow x f ≤ (u : WithTop ℝ≥0) := sInf_le ⟨u, rfl, hu⟩
    rw [hT] at hle
    exact (not_le_of_gt (by exact_mod_cast hut)) hle
  · rcases htu.eq_or_lt with hut | htu'
    · subst u
      exact (not_le_of_gt ha) hu
    · exact (not_le_of_gt (hb ⟨htu', hub'⟩)) hu

/-- **Weak side of the sandwich.** For every path, `H_x ≤ t → I_t ≤ -x`; also
`T_x ≤ t → I_t ≤ -x` (deterministic; stated a.s. for uniformity with the other items).
The converses are NOT claimed: at a plateau level
`x` of `L` (an excursion from the minimum straddling `t`) one has `I_t = -x` but `T_x > t`. -/
theorem runningInf_le_of_firstHitBelow_le (x t : ℝ≥0) (f : DLoc)
    (h : firstHitBelow x f ≤ (t : WithTop ℝ≥0)) : runningInfLoc f t ≤ -(x : ℝ) := by
  obtain ⟨u, hu⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top WithTop.coe_ne_top h)
  rw [← hu] at h
  have hut : u ≤ t := by exact_mod_cast h
  exact (runningInfLoc_le_eval f t ⟨u, hut⟩).trans
    (eval_le_of_firstHitBelow_eq_coe hu.symm)

theorem ae_runningInf_le_of_firstPassageBelow_le {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (x t : ℝ≥0),
      firstPassageBelow x f ≤ (t : WithTop ℝ≥0) → runningInfLoc f t ≤ -(x : ℝ) := by
  have _hθ := hθ
  exact Filter.Eventually.of_forall fun f x t h =>
    runningInfLoc_le_of_firstPassageBelow_le f h

/-- **Strict passage versus first hitting (deterministic sandwich).** For every path and level
`x > 0`, `sup_{y<x} T_y ≤ H_x ≤ T_x`. The left limit `T_{x-}` of the passage process is
at most the first hitting time of `-x`; a plateau of `-runningInf` at level `x` is exactly where
these are `<`. -/
theorem iSup_firstPassageBelow_le_firstHitBelow_le (f : DLoc) {x : ℝ≥0} (hx : 0 < x) :
    (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ firstHitBelow x f ∧
      firstHitBelow x f ≤ firstPassageBelow x f := by
  have _hx := hx
  constructor
  · apply iSup_le
    intro y
    apply le_sInf
    rintro _ ⟨u, rfl, hu⟩
    apply firstPassageBelow_le_of_eval_lt
    exact hu.trans_lt (neg_lt_neg (by exact_mod_cast y.2))
  · apply le_iInf
    intro u
    apply le_iInf
    intro hu
    exact sInf_le ⟨u, rfl, hu.le⟩

/-! ### Local time `L = -I`: measurability, adaptedness, Stieltjes concentration, straddling -/

/-- The local time at the minimum, `L_t = -I_t`. -/
noncomputable def localTime (f : DLoc) (t : ℝ≥0) : ℝ := -runningInfLoc f t

/-- `L` is jointly measurable in `(t, f)`. -/
theorem measurable_localTime_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => localTime p.2 p.1) := by
  exact measurable_runningInfLoc_uncurry.neg

/-- `L` is adapted to the right-continuous filtration of `DLoc`. -/
theorem stronglyAdapted_localTime :
    StronglyAdapted DLoc.filtration (fun t (f : DLoc) => localTime f t) := by
  exact stronglyAdapted_runningInfLoc.neg

/-- Almost surely `L_0 = 0` (from `f 0 = 0`), `L` is monotone, continuous, and unbounded. -/
theorem ae_localTime_spec {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      localTime f 0 = 0 ∧ Monotone (localTime f) ∧ Continuous (localTime f) ∧
        Tendsto (localTime f) atTop atTop := by
  filter_upwards [ae_firstPassageBelow_spec hθ,
    ae_runningInf_continuous_antitone_tendsto hθ] with f hf hI
  have hI0 : runningInfLoc f 0 = 0 := by
    apply le_antisymm
    · simpa only [hf.1] using runningInfLoc_le_eval f 0 ⟨0, by simp⟩
    · apply le_runningInfLoc
      intro u
      have hu : u.1 = 0 := by exact_mod_cast (show (u : ℝ≥0) = 0 from le_antisymm u.2 (by simp))
      simp [hu, hf.1]
  exact ⟨by simp [localTime, hI0], fun _ _ h => neg_le_neg (hI.2.1 h),
    hI.1.neg, tendsto_neg_atBot_atTop.comp hI.2.2⟩

open scoped Classical in
/-- The Stieltjes function `s ↦ L_{s⁺}` on `ℝ` (`s⁺ = max s 0`) when `L` is monotone and
continuous; junk value the zero function otherwise (a null set of paths). -/
noncomputable def localTimeStieltjes (f : DLoc) : StieltjesFunction ℝ :=
  if h : Monotone (localTime f) ∧ Continuous (localTime f) then
    { toFun := fun s => localTime f s.toNNReal
      mono' := h.1.comp (fun _ _ hab => Real.toNNReal_mono hab)
      right_continuous' := fun _ =>
        ((h.2.comp continuous_real_toNNReal).continuousAt).continuousWithinAt }
  else
    { toFun := fun _ => 0
      mono' := monotone_const
      right_continuous' := fun _ => continuousWithinAt_const }

/-- The `ℝ≥0`-valued left limit `T_{x-} = sup_{y<x} T_y` of the passage process, with `T_{0-} = 0`;
junk `0` where some `T_y = ⊤` (null set). -/
noncomputable def passageTimeMinus (x : ℝ≥0) (f : DLoc) : ℝ≥0 :=
  (⨆ y : Set.Iio x, firstPassageBelow y f).untopD 0

/-- `L_t` as a level in `ℝ≥0` (`L_t ≥ 0` almost surely). -/
noncomputable def localTimeNN (f : DLoc) (t : ℝ≥0) : ℝ≥0 := (localTime f t).toNNReal

private lemma iSup_firstPassageBelow_eq_iSup_rat (x : ℝ≥0) (f : DLoc) :
    (⨆ y : Set.Iio x, firstPassageBelow y f) =
      ⨆ q : ℚ, if 0 ≤ q ∧ (q : ℝ) < (x : ℝ) then
        firstPassageBelow (Real.toNNReal q) f else 0 := by
  apply le_antisymm
  · apply iSup_le
    intro y
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn (show (y : ℝ) < (x : ℝ) by exact_mod_cast y.2)
    have hq0 : 0 ≤ (q : ℝ) := (by positivity : (0 : ℝ) ≤ (y : ℝ≥0)).trans hyq.le
    have hle : firstPassageBelow y f ≤ firstPassageBelow (Real.toNNReal q) f := by
      apply firstPassageBelow_mono f
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ hq0]
      exact_mod_cast hyq.le
    apply hle.trans
    apply le_iSup_of_le q
    simp only [show 0 ≤ q from by exact_mod_cast hq0,
      show (q : ℝ) < (x : ℝ) from hqx, and_self, ↓reduceIte, le_rfl]
  · apply iSup_le
    intro q
    by_cases hq : 0 ≤ q ∧ (q : ℝ) < (x : ℝ)
    · simp only [hq]
      have hq0 : 0 ≤ (q : ℝ) := by exact_mod_cast hq.1
      have hqx : Real.toNNReal q < x := by
        rw [← NNReal.coe_lt_coe, Real.coe_toNNReal _ hq0]
        exact hq.2
      exact le_iSup (fun y : Set.Iio x => firstPassageBelow y f) ⟨Real.toNNReal q, hqx⟩
    · simp [hq]

private lemma iSup_firstPassageBelow_le (f : DLoc) (x : ℝ≥0) :
    (⨆ y : Set.Iio x, firstPassageBelow y f) ≤ firstPassageBelow x f := by
  apply iSup_le
  intro y
  exact firstPassageBelow_mono f y.2.le

private lemma passageTimeMinus_eq (f : DLoc)
    (hfin : ∀ x : ℝ≥0, firstPassageBelow x f < ⊤) (x : ℝ≥0) :
    (⨆ y : Set.Iio x, firstPassageBelow y f) = (passageTimeMinus x f : WithTop ℝ≥0) := by
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top (ne_of_lt (hfin x)) (iSup_firstPassageBelow_le f x))
  simp only [passageTimeMinus, ← ht, WithTop.untopD_coe]

/-- `passageTimeMinus x` is measurable in the path. -/
theorem measurable_passageTimeMinus (x : ℝ≥0) : Measurable (passageTimeMinus x) := by
  apply Measurable.untopD 0
  have heq : (fun f => ⨆ y : Set.Iio x, firstPassageBelow y f) = fun f =>
      ⨆ q : ℚ, if 0 ≤ q ∧ (q : ℝ) < (x : ℝ) then
        firstPassageBelow (Real.toNNReal q) f else 0 := by
    funext f
    exact iSup_firstPassageBelow_eq_iSup_rat x f
  rw [heq]
  apply Measurable.iSup
  intro q
  apply Measurable.ite (measurable_const.setOf)
  · exact (measurable_firstPassageBelow_uncurry.comp
      (measurable_const.prodMk measurable_id))
  · exact measurable_const

/-- Joint measurability of `(x, f) ↦ T_{x-}(f)`. -/
theorem measurable_passageTimeMinus_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => passageTimeMinus p.1 p.2) := by
  apply Measurable.untopD 0
  have heq : (fun p : ℝ≥0 × DLoc => ⨆ y : Set.Iio p.1, firstPassageBelow y p.2) =
      fun p => ⨆ q : ℚ, if 0 ≤ q ∧ (q : ℝ) < (p.1 : ℝ) then
        firstPassageBelow (Real.toNNReal q) p.2 else 0 := by
    funext p
    exact iSup_firstPassageBelow_eq_iSup_rat p.1 p.2
  rw [heq]
  apply Measurable.iSup
  intro q
  apply Measurable.ite
  · exact (measurable_const.setOf.inter
      (measurableSet_lt measurable_const (measurable_coe_nnreal_real.comp measurable_fst)))
  · exact measurable_firstPassageBelow_uncurry.comp
      (measurable_const.prodMk measurable_snd)
  · exact measurable_const

private lemma integral_exp_neg_passageTimeMinus {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {x : ℝ≥0} (hx : 0 < x) {q : ℝ} (hq : 0 ≤ q) :
    ∫ f : DLoc, Real.exp (-q * ((passageTimeMinus x f : ℝ≥0) : ℝ))
        ∂(stableLocalLaw θ : Measure DLoc) = Real.exp (-(x : ℝ) * q ^ (1 / θ)) := by
  have : (𝓝[<] x).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, hx⟩
  let P : Measure DLoc := stableLocalLaw θ
  have hfin := ae_passageTime_eq_firstPassageBelow hθ
  have hleft (f : DLoc)
      (hf : (∀ z : ℝ≥0, firstPassageBelow z f = (passageTime z f : WithTop ℝ≥0)) ∧
        passageTime 0 f = 0) :
      Tendsto (fun y : ℝ≥0 => passageTime y f) (𝓝[<] x) (𝓝 (passageTimeMinus x f)) := by
    have hfin' : ∀ z : ℝ≥0, firstPassageBelow z f < ⊤ := by
      intro z
      rw [hf.1 z]
      exact WithTop.coe_lt_top _
    have hmono : Monotone (fun y : ℝ≥0 => passageTime y f) :=
      untopD_firstPassageBelow_mono f hfin'
    have hb : BddAbove ((fun y : ℝ≥0 => passageTime y f) '' Set.Iio x) := by
      refine ⟨passageTime x f, ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact hmono hy.le
    have hpm : sSup ((fun y : ℝ≥0 => passageTime y f) '' Set.Iio x) =
        passageTimeMinus x f := by
      apply le_antisymm
      · have hne : ((fun y : ℝ≥0 => passageTime y f) '' Set.Iio x).Nonempty :=
          ⟨passageTime 0 f, ⟨0, hx, rfl⟩⟩
        apply csSup_le hne
        rintro _ ⟨y, hy, rfl⟩
        have he : firstPassageBelow y f ≤ (passageTimeMinus x f : WithTop ℝ≥0) := by
          rw [← passageTimeMinus_eq f hfin' x]
          exact le_iSup (fun z : Set.Iio x => firstPassageBelow z f) ⟨y, hy⟩
        rw [hf.1 y] at he
        exact_mod_cast he
      · apply WithTop.coe_le_coe.mp
        rw [← passageTimeMinus_eq f hfin' x, WithTop.coe_sSup hb]
        apply iSup_le
        intro y
        rw [hf.1 y]
        have hmem : passageTime y f ∈ (fun y : ℝ≥0 => passageTime y f) '' Set.Iio x :=
          ⟨y, y.2, rfl⟩
        exact le_iSup_of_le (passageTime y f) (le_iSup_of_le hmem le_rfl)
    simpa only [hpm] using hmono.tendsto_nhdsLT x
  have hDCT : Tendsto (fun y : ℝ≥0 =>
      ∫ f : DLoc, Real.exp (-q * ((passageTime y f : ℝ≥0) : ℝ)) ∂P) (𝓝[<] x)
      (𝓝 (∫ f : DLoc, Real.exp (-q * ((passageTimeMinus x f : ℝ≥0) : ℝ)) ∂P)) := by
    apply tendsto_integral_filter_of_dominated_convergence (fun _ : DLoc => (1 : ℝ))
    · exact Eventually.of_forall fun y => (((measurable_passageTime y).coe_nnreal_real.const_mul
        (-q)).exp).aestronglyMeasurable
    · refine Eventually.of_forall fun y => ?_
      exact Eventually.of_forall fun f => by
        rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr hq) (by positivity))
    · exact integrable_const 1
    · apply Eventually.mono hfin
      intro f hf
      have hl := hleft f hf
      exact (by fun_prop : Continuous fun z : ℝ≥0 => Real.exp (-q * (z : ℝ)))
        |>.continuousAt.tendsto.comp hl
  have hformula : (fun y : ℝ≥0 =>
      ∫ f : DLoc, Real.exp (-q * ((passageTime y f : ℝ≥0) : ℝ)) ∂P) =ᶠ[𝓝[<] x]
      (fun y : ℝ≥0 => Real.exp (-(y : ℝ) * q ^ (1 / θ))) := by
    filter_upwards [Ioo_mem_nhdsLT hx] with y hy
    exact integral_exp_neg_strictPassageBelow hθ (by exact_mod_cast hy.1) hq
  have hexplicit : Tendsto (fun y : ℝ≥0 => Real.exp (-(y : ℝ) * q ^ (1 / θ)))
      (𝓝[<] x) (𝓝 (Real.exp (-(x : ℝ) * q ^ (1 / θ)))) := by
    have hc : Continuous (fun y : ℝ≥0 => Real.exp (-(y : ℝ) * q ^ (1 / θ))) := by fun_prop
    exact hc.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  exact tendsto_nhds_unique hDCT (hexplicit.congr' hformula.symm)

private lemma ae_passageTimeMinus_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), passageTimeMinus x f = passageTime x f := by
  by_cases hx : x = 0
  · subst x
    filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
    simp only [passageTimeMinus, iSup_of_empty, hf.2]
    rfl
  · have hxpos : 0 < x := pos_iff_ne_zero.mpr hx
    let P : Measure DLoc := stableLocalLaw θ
    have hle : ∀ᵐ f ∂P, passageTimeMinus x f ≤ passageTime x f := by
      filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
      have hfin : ∀ z : ℝ≥0, firstPassageBelow z f < ⊤ := by
        intro z
        rw [hf.1 z]
        exact WithTop.coe_lt_top _
      have hc : (passageTimeMinus x f : WithTop ℝ≥0) ≤ (passageTime x f : WithTop ℝ≥0) := by
        rw [← passageTimeMinus_eq f hfin x, ← hf.1 x]
        exact iSup_firstPassageBelow_le f x
      exact_mod_cast hc
    have hi : ∀ q : ℝ, 0 < q →
        ∫ f : DLoc, (Real.exp (-q * ((passageTimeMinus x f : ℝ≥0) : ℝ)) -
          Real.exp (-q * ((passageTime x f : ℝ≥0) : ℝ))) ∂P = 0 := by
      intro q hq
      have hmi : Integrable (fun f : DLoc =>
          Real.exp (-q * ((passageTimeMinus x f : ℝ≥0) : ℝ))) P :=
        (integrable_const (1 : ℝ)).mono'
          (((measurable_passageTimeMinus x).coe_nnreal_real.const_mul
            (-q)).exp).aestronglyMeasurable
          (Eventually.of_forall fun f => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr hq.le) (by positivity)))
      have hti : Integrable (fun f : DLoc =>
          Real.exp (-q * ((passageTime x f : ℝ≥0) : ℝ))) P :=
        (integrable_const (1 : ℝ)).mono'
            (((measurable_passageTime x).coe_nnreal_real.const_mul (-q)).exp).aestronglyMeasurable
          (Eventually.of_forall fun f => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr hq.le) (by positivity)))
      rw [integral_sub hmi hti, integral_exp_neg_passageTimeMinus hθ hxpos hq.le]
      have hp := integral_exp_neg_strictPassageBelow hθ (by exact_mod_cast hxpos) hq.le
      have hp' : (∫ f : DLoc, Real.exp (-q * ((passageTime x f : ℝ≥0) : ℝ)) ∂P) =
          Real.exp (-(x : ℝ) * q ^ (1 / θ)) := by
        simpa [P, passageTime, firstPassageBelow] using hp
      rw [hp']
      ring
    choose q hq using (show ∃ q : ℝ, 0 < q from ⟨1, one_pos⟩)
    have hnonneg : 0 ≤ᵐ[P] fun f : DLoc =>
        Real.exp (-q * ((passageTimeMinus x f : ℝ≥0) : ℝ)) -
          Real.exp (-q * ((passageTime x f : ℝ≥0) : ℝ)) := by
      filter_upwards [hle] with f hf
      apply sub_nonneg.mpr
      apply Real.exp_le_exp.mpr
      have hc : ((passageTimeMinus x f : ℝ≥0) : ℝ) ≤ (passageTime x f : ℝ) := by
        exact_mod_cast hf
      nlinarith
    have hint : Integrable (fun f : DLoc =>
        Real.exp (-q * ((passageTimeMinus x f : ℝ≥0) : ℝ)) -
          Real.exp (-q * ((passageTime x f : ℝ≥0) : ℝ))) P := by
      apply Integrable.sub
      · exact (integrable_const (1 : ℝ)).mono'
          (((measurable_passageTimeMinus x).coe_nnreal_real.const_mul
            (-q)).exp).aestronglyMeasurable
          (Eventually.of_forall fun f => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr hq.le) (by positivity)))
      · exact (integrable_const (1 : ℝ)).mono'
            (((measurable_passageTime x).coe_nnreal_real.const_mul (-q)).exp).aestronglyMeasurable
          (Eventually.of_forall fun f => by
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
              (neg_nonpos.mpr hq.le) (by positivity)))
    have hz := (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp (hi q hq)
    filter_upwards [hz, hle] with f hz hle
    have he := Real.exp_injective (sub_eq_zero.mp hz)
    have hc : ((passageTimeMinus x f : ℝ≥0) : ℝ) ≤ (passageTime x f : ℝ) := by
      exact_mod_cast hle
    have hq0 : 0 < q := hq
    apply le_antisymm hle
    by_contra hlt
    have hgt : (passageTimeMinus x f : ℝ) < (passageTime x f : ℝ) := by
      exact_mod_cast (lt_of_not_ge hlt)
    nlinarith

/-- **First hitting agrees with strict passage at each FIXED level** (a.s., NOT simultaneously
for all levels). -/
theorem ae_firstHitBelow_eq_firstPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), firstHitBelow x f = firstPassageBelow x f := by
  filter_upwards [ae_passageTimeMinus_eq hθ x,
    ae_passageTime_eq_firstPassageBelow hθ] with f hleft hf
  by_cases hx : x = 0
  · subst x
    apply le_antisymm
    · apply le_iInf
      intro u
      apply le_iInf
      intro hu
      exact sInf_le ⟨u, rfl, hu.le⟩
    · have hzero : firstPassageBelow 0 f = 0 := by rw [hf.1 0, hf.2]; rfl
      rw [hzero]
      exact bot_le
  · apply le_antisymm (iSup_firstPassageBelow_le_firstHitBelow_le f
      (pos_iff_ne_zero.mpr hx)).2
    have hle := (iSup_firstPassageBelow_le_firstHitBelow_le f
      (pos_iff_ne_zero.mpr hx)).1
    rw [passageTimeMinus_eq f (fun z => by rw [hf.1 z]; exact WithTop.coe_lt_top _) x,
      hleft, ← hf.1 x] at hle
    exact hle

/-- **Straddling.** Almost surely for all `t`: `T_{L_t -} ≤ t ≤ T_{L_t}`. -/
theorem ae_passageTimeMinus_le_le_firstPassageBelow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ t : ℝ≥0,
      passageTimeMinus (localTimeNN f t) f ≤ t ∧
        (t : WithTop ℝ≥0) ≤ firstPassageBelow (localTimeNN f t) f := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ,
    ae_firstPassageBelow_spec hθ] with f hf hspec
  have hfin : ∀ x : ℝ≥0, firstPassageBelow x f < ⊤ := by
    intro x
    rw [hf.1 x]
    exact WithTop.coe_lt_top _
  have hL (t : ℝ≥0) : 0 ≤ localTime f t := by
    apply neg_nonneg.mpr
    exact (runningInfLoc_le_eval f t ⟨0, by simp⟩).trans_eq hspec.1
  have hNN (t : ℝ≥0) : ((localTimeNN f t : ℝ≥0) : ℝ) = localTime f t :=
    Real.coe_toNNReal _ (hL t)
  intro t
  constructor
  · have hsup : (⨆ y : Set.Iio (localTimeNN f t), firstPassageBelow y f) ≤
        (t : WithTop ℝ≥0) := by
      apply iSup_le
      intro y
      apply (runningInfLoc_lt_sandwich y t f).2
      have hy : (y : ℝ) < localTime f t := by
        rw [← hNN t]
        exact_mod_cast y.2
      change (y : ℝ) < -runningInfLoc f t at hy
      linarith
    rw [passageTimeMinus_eq f hfin] at hsup
    exact_mod_cast hsup
  · apply le_of_not_gt
    intro hlt
    have hI := (runningInfLoc_lt_sandwich (localTimeNN f t) t f).1 hlt
    rw [hNN t, localTime] at hI
    linarith

/-- **Generalized inverse identities.** Almost surely for all `x ≥ 0`:
`L (T_x) = x` and `L (T_{x-}) = x`. -/
theorem ae_localTime_passageTime {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x : ℝ≥0,
      localTime f (passageTime x f) = x ∧ localTime f (passageTimeMinus x f) = x := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ,
    ae_firstPassageBelow_spec hθ] with f hf hspec
  have hfin : ∀ x : ℝ≥0, firstPassageBelow x f < ⊤ := by
    intro x
    rw [hf.1 x]
    exact WithTop.coe_lt_top _
  have hcreep (x : ℝ≥0) : f.1 (passageTime x f) = -(x : ℝ) := by
    by_cases hx : x = 0
    · subst x
      simp [hf.2, hspec.1]
    · exact hspec.2 x (pos_iff_ne_zero.mpr hx) |>.2.2
  have hbefore (x : ℝ≥0) {u : ℝ≥0} (hu : u < passageTime x f) :
      -(x : ℝ) ≤ f.1 u := by
    apply le_eval_of_lt_strictPassageBelow
    change (u : WithTop ℝ≥0) < firstPassageBelow x f
    rw [hf.1 x]
    exact_mod_cast hu
  have hIp (x : ℝ≥0) : runningInfLoc f (passageTime x f) = -(x : ℝ) := by
    apply le_antisymm
    · exact (runningInfLoc_le_eval f (passageTime x f)
        ⟨passageTime x f, by simp⟩).trans_eq (hcreep x)
    · apply le_runningInfLoc
      intro u
      rcases u.2.eq_or_lt with hu | hu
      · have hu' : (u : ℝ≥0) = passageTime x f := NNReal.coe_injective hu
        change -(x : ℝ) ≤ f.1 u.1
        rw [hu']
        exact (hcreep x).ge
      · exact hbefore x hu
  have hLpass (x : ℝ≥0) : localTime f (passageTime x f) = x := by
    rw [localTime, hIp x]
    simp
  intro x
  refine ⟨hLpass x, ?_⟩
  have hSrep := passageTimeMinus_eq f hfin x
  have hST : (passageTimeMinus x f : WithTop ℝ≥0) ≤ firstPassageBelow x f := by
    rw [← hSrep]
    exact iSup_firstPassageBelow_le f x
  have hlower : -(x : ℝ) ≤ runningInfLoc f (passageTimeMinus x f) := by
    apply le_runningInfLoc
    intro u
    have huS : (u : ℝ≥0) ≤ passageTimeMinus x f := u.2
    have huSC : (u : WithTop ℝ≥0) ≤ (passageTimeMinus x f : WithTop ℝ≥0) := by
      exact_mod_cast huS
    have huT : (u : WithTop ℝ≥0) ≤ firstPassageBelow x f := huSC.trans hST
    rcases huT.eq_or_lt with hu | hu
    · have hup : (u : ℝ≥0) = passageTime x f := by
        rw [hf.1 x] at hu
        exact_mod_cast hu
      change -(x : ℝ) ≤ f.1 u
      rw [hup]
      exact (hcreep x).ge
    · apply hbefore x
      rw [hf.1 x] at hu
      exact_mod_cast hu
  have hupper : runningInfLoc f (passageTimeMinus x f) ≤ -(x : ℝ) := by
    by_cases hx : x = 0
    · subst x
      have hzero : passageTimeMinus 0 f = 0 := by simp [passageTimeMinus]
      rw [hzero]
      simpa using runningInfLoc_le_eval f 0 ⟨0, by simp⟩ |>.trans_eq hspec.1
    · have hxpos : 0 < x := pos_iff_ne_zero.mpr hx
      apply le_of_forall_gt
      intro a ha
      have hmax : max (-a) 0 < (x : ℝ) := max_lt (by linarith) (by exact_mod_cast hxpos)
      obtain ⟨v, hv, hvx⟩ := exists_between hmax
      let y : ℝ≥0 := Real.toNNReal v
      have hv0 : 0 ≤ v := (le_max_right _ _).trans hv.le
      have hy : (y : ℝ) = v := Real.coe_toNNReal _ hv0
      have hyx0 : (y : ℝ) < (x : ℝ) := hy.trans_lt hvx
      have hyx : y < x := by exact_mod_cast hyx0
      have hle : firstPassageBelow y f ≤ (passageTimeMinus x f : WithTop ℝ≥0) := by
        rw [← hSrep]
        exact le_iSup (fun z : Set.Iio x => firstPassageBelow z f) ⟨y, hyx⟩
      have hI := runningInfLoc_le_of_firstPassageBelow_le f hle
      have hya : -(y : ℝ) < a := by
        rw [hy]
        have hnav : -a < v := (le_max_left _ _).trans_lt hv
        linarith
      exact hI.trans_lt hya
  rw [localTime]
  linarith

/-! ### Strong Markov at `T_x` and independent stationary increments -/

/-- **Additivity from creeping** (deterministic on the creeping event): a.s., for all `x y ≥ 0`,
`T_{x+y}(f) = T_x(f) + T_y(shiftAt T_x f)`. -/
theorem ae_firstPassageBelow_add {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ x y : ℝ≥0,
      firstPassageBelow (x + y) f =
        firstPassageBelow x f + firstPassageBelow y (DLoc.shiftAt (firstPassageBelow x) f) := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ,
    ae_firstPassageBelow_spec hθ] with f hf hspec
  have hs (x : ℝ≥0) : firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0) := hf.1 x
  have hval (x : ℝ≥0) : f.1 (passageTime x f) = -(x : ℝ) := by
    by_cases hx : x = 0
    · subst x
      simp [hf.2, hspec.1]
    · exact hspec.2 x (pos_iff_ne_zero.mpr hx) |>.2.2
  intro x y
  exact firstPassageBelow_add_of_creeping (hs x) (hval x)

/-- **Reflected process after `T_x`**: on the creeping event,
`X_{T_x + t} - I_{T_x + t} = X'_t - I'_t` for the centered shift `X' = shiftAt T_x`. -/
theorem ae_reflected_shiftAt_passage {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ∀ (x : ℝ≥0) (t : ℝ≥0),
      f.1 (passageTime x f + t) - runningInfLoc f (passageTime x f + t) =
        (DLoc.shiftAt (firstPassageBelow x) f).1 t -
          runningInfLoc (DLoc.shiftAt (firstPassageBelow x) f) t := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ,
    ae_firstPassageBelow_spec hθ] with f hf hspec
  have hs (x : ℝ≥0) : firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0) := hf.1 x
  have hval (x : ℝ≥0) : f.1 (passageTime x f) = -(x : ℝ) := by
    by_cases hx : x = 0
    · subst x
      simp [hf.2, hspec.1]
    · exact hspec.2 x (pos_iff_ne_zero.mpr hx) |>.2.2
  intro x t
  have hshift : DLoc.shiftAt (firstPassageBelow x) f = DLoc.shift (passageTime x f) f := by
    unfold DLoc.shiftAt
    rw [hs x]
    rfl
  rw [hshift]
  exact reflected_shift_of_creeping (hs x) (hval x) t

/-- **Fresh increment: independence of `F_{T_x}` and law.** For `x, y ≥ 0`, any event `A` of the
stopped σ-algebra `F_{T_x}` and Borel `S ⊆ ℝ`:
`P(A ∩ {T_{x+y} - T_x ∈ S}) = P(A) · P(T_y ∈ S)`. -/
theorem measure_inter_passageIncrement {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x y : ℝ≥0)
    {A : Set DLoc} (hA : MeasurableSet[(isStoppingTime_firstPassageBelow x).measurableSpace] A)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (stableLocalLaw θ : Measure DLoc)
        (A ∩ {f | ((passageTime (x + y) f : ℝ≥0) : ℝ) - (passageTime x f : ℝ) ∈ S}) =
      (stableLocalLaw θ : Measure DLoc) A * passageLaw θ y S := by
  let P : Measure DLoc := stableLocalLaw θ
  let τ : DLoc → ℝ≥0∞ := firstPassageBelow x
  let A' := A ∩ {f | τ f < ⊤}
  let B := {f : DLoc | ((passageTime y f : ℝ≥0) : ℝ) ∈ S}
  have hτ : IsStoppingTime DLoc.filtration τ := isStoppingTime_firstPassageBelow x
  have hA' : MeasurableSet[hτ.measurableSpace] A' :=
    hA.inter (DLoc.measurableSet_lt_top_stopped hτ)
  have hB : MeasurableSet B := (measurable_passageTime y).coe_nnreal_real hS
  have hstrong := measure_inter_preimage_shiftAt hθ hτ hA' (fun _ h => h.2) hB
  have hPB : P B = passageLaw θ y S := by
    rw [passageLaw, Measure.map_apply (measurable_passageTime y).coe_nnreal_real hS]
    change P B = P B
    rfl
  have hAeq : P A' = P A := by
    apply measure_congr
    filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
    have hfin : τ f < ⊤ := by
      rw [show τ f = (passageTime x f : WithTop ℝ≥0) from hf.1 x]
      exact WithTop.coe_lt_top _
    simp [A', hfin]
  rw [← hPB, ← hAeq, ← hstrong]
  apply measure_congr
  filter_upwards [ae_firstPassageBelow_add hθ,
    ae_passageTime_eq_firstPassageBelow hθ] with f hadd hf
  have hsy : firstPassageBelow y (DLoc.shiftAt τ f) =
      (passageTime y (DLoc.shiftAt τ f) : WithTop ℝ≥0) := by
    have hne : firstPassageBelow y (DLoc.shiftAt τ f) ≠ ⊤ := by
      intro htop
      have hadd' := hadd x y
      rw [htop] at hadd'
      rw [hf.1 (x + y), hf.1 x] at hadd'
      exact WithTop.coe_ne_top (hadd'.trans (by rw [WithTop.add_top]))
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
    simp only [passageTime, ← hr, WithTop.untopD_coe]
  have hinc : ((passageTime (x + y) f : ℝ≥0) : ℝ) - (passageTime x f : ℝ) =
      ((passageTime y (DLoc.shiftAt τ f) : ℝ≥0) : ℝ) := by
    have hadd' := hadd x y
    rw [hf.1 (x + y), hf.1 x, hsy] at hadd'
    have hnn : passageTime (x + y) f = passageTime x f + passageTime y (DLoc.shiftAt τ f) := by
      exact_mod_cast hadd'
    rw [hnn]
    push_cast
    ring
  apply propext
  change (f ∈ A ∧ ((passageTime (x + y) f : ℝ≥0) : ℝ) - (passageTime x f : ℝ) ∈ S) ↔
    f ∈ A' ∧ ((passageTime y (DLoc.shiftAt τ f) : ℝ≥0) : ℝ) ∈ S
  rw [hinc]
  have hfin : τ f < ⊤ := by
    rw [show τ f = (passageTime x f : WithTop ℝ≥0) from hf.1 x]
    exact WithTop.coe_lt_top _
  simp [A', hfin]

/-- **Stationary increments.** `T_{x+y} - T_x` has the law of `T_y`. -/
theorem map_passageIncrement {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x y : ℝ≥0) :
    Measure.map (fun f : DLoc => ((passageTime (x + y) f : ℝ≥0) : ℝ) - (passageTime x f : ℝ))
        (stableLocalLaw θ : Measure DLoc) = passageLaw θ y := by
  have hmeas : Measurable (fun f : DLoc =>
      ((passageTime (x + y) f : ℝ≥0) : ℝ) - (passageTime x f : ℝ)) :=
    (measurable_passageTime (x + y)).coe_nnreal_real.sub
      (measurable_passageTime x).coe_nnreal_real
  ext S hS
  rw [Measure.map_apply hmeas hS]
  change (stableLocalLaw θ : Measure DLoc)
    {f | ((passageTime (x + y) f : ℝ≥0) : ℝ) - (passageTime x f : ℝ) ∈ S} = passageLaw θ y S
  have h := measure_inter_passageIncrement hθ x y (A := Set.univ) MeasurableSet.univ hS
  simpa using h

/-! ### One-dimensional law: Laplace transform, positivity, scaling -/

private lemma passageLaw_Iio_zero (θ : ℝ) (x : ℝ≥0) : passageLaw θ x (Iio 0) = 0 := by
  rw [passageLaw, Measure.map_apply
    (measurable_passageTime x).coe_nnreal_real measurableSet_Iio,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [] with f
  exact not_lt_of_ge (passageTime x f).2

/-- **Laplace transform**:
`∫ e^{-q t} d passageLaw θ x = e^{-x q^{1/θ}}`
for `x ≥ 0`, `q ≥ 0`. -/
theorem integral_exp_neg_passageLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) {q : ℝ} (hq : 0 ≤ q) :
    ∫ t, Real.exp (-q * t) ∂passageLaw θ x = Real.exp (-(x : ℝ) * q ^ (1 / θ)) := by
  have hmeas : Measurable (fun t : ℝ => Real.exp (-q * t)) := by fun_prop
  rw [passageLaw, integral_map
    (measurable_passageTime x).coe_nnreal_real.aemeasurable
    hmeas.aestronglyMeasurable]
  by_cases hx : x = 0
  · subst x
    calc
      _ = ∫ _ : DLoc, (1 : ℝ) ∂(stableLocalLaw θ : Measure DLoc) := by
        apply integral_congr_ae
        filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
        simp [hf.2]
      _ = _ := by simp
  · have hxpos : 0 < (x : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hx)
    exact integral_exp_neg_strictPassageBelow hθ hxpos hq

/-- For `x > 0` the law of `T_x` lives on `(0, ∞)`. -/
theorem passageLaw_Iic_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {x : ℝ≥0} (hx : 0 < x) :
    passageLaw θ x (Iic 0) = 0 := by
  rw [passageLaw, Measure.map_apply
    (measurable_passageTime x).coe_nnreal_real measurableSet_Iic,
    measure_eq_zero_iff_ae_notMem]
  filter_upwards [ae_firstPassageBelow_spec hθ] with f hf
  obtain ⟨hfin, hpos, _⟩ := hf.2 x hx
  obtain ⟨t, ht⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hfin)
  have ht0 : 0 < t := by
    rw [← ht] at hpos
    exact_mod_cast hpos
  have hpt : passageTime x f = t := by
    change (firstPassageBelow x f).untopD 0 = t
    rw [← ht, WithTop.untopD_coe]
  change ¬((passageTime x f : ℝ≥0) : ℝ) ≤ 0
  rw [hpt]
  exact not_le_of_gt (by exact_mod_cast ht0)

/-- **Scaling.** `T_{c x} =d c^θ T_x`, for `c > 0`. -/
theorem passageLaw_scaling {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) {c : ℝ≥0} (hc : 0 < c) :
    passageLaw θ (c * x) = (passageLaw θ x).map (fun t : ℝ => (c : ℝ) ^ θ * t) := by
  let a : ℝ := (c : ℝ) ^ θ
  have hcpos : 0 < (c : ℝ) := by exact_mod_cast hc
  have ha : 0 < a := Real.rpow_pos_of_pos hcpos θ
  let _ := passageLaw_isProbabilityMeasure hθ (c * x)
  let _ := passageLaw_isProbabilityMeasure hθ x
  have hscale : Measurable (fun t : ℝ => a * t) := by fun_prop
  apply measure_eq_of_laplace_on_nonneg (passageLaw_Iio_zero θ (c * x))
  · rw [Measure.map_apply hscale measurableSet_Iio, measure_eq_zero_iff_ae_notMem]
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (passageLaw_Iio_zero θ x)] with t ht
    exact not_lt_of_ge (mul_nonneg ha.le (not_lt.mp ht))
  · intro q hq
    rw [integral_exp_neg_passageLaw hθ (c * x) hq.le]
    have hexp : Measurable (fun t : ℝ => Real.exp (-q * t)) := by fun_prop
    rw [integral_map hscale.aemeasurable hexp.aestronglyMeasurable]
    have hexpa : Measurable (fun t : ℝ => Real.exp (-q * (a * t))) := by fun_prop
    rw [passageLaw, integral_map (measurable_passageTime x).coe_nnreal_real.aemeasurable
      hexpa.aestronglyMeasurable]
    simp_rw [show ∀ t : ℝ, -q * (a * t) = -(a * q) * t by intro t; ring]
    have hN := integral_exp_neg_passageLaw hθ x (q := a * q) (mul_nonneg ha.le hq.le)
    have hexp' : Measurable (fun t : ℝ => Real.exp (-(a * q) * t)) := by fun_prop
    rw [passageLaw, integral_map (measurable_passageTime x).coe_nnreal_real.aemeasurable
      hexp'.aestronglyMeasurable] at hN
    rw [hN]
    have hpow : (a * q) ^ (1 / θ) = (c : ℝ) * q ^ (1 / θ) := by
      dsimp [a]
      rw [Real.mul_rpow (Real.rpow_nonneg hcpos.le θ) hq.le, ← Real.rpow_mul hcpos.le]
      have hθ0 : θ ≠ 0 := ne_of_gt (zero_lt_one.trans hθ.1)
      rw [show θ * (1 / θ) = 1 by field_simp, Real.rpow_one]
    rw [hpow]
    simp only [NNReal.coe_mul]
    ring_nf

/-- **Identification of the law by its Laplace transform**: any probability law on `ℝ` with the
transform `e^{-x q^{1/θ}}` is `passageLaw θ x` (the positive `(1/θ)`-stable law). -/
theorem eq_passageLaw_of_integral_exp_neg {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0)
    {ρ : Measure ℝ} [IsProbabilityMeasure ρ] (h0 : ρ (Iio 0) = 0)
    (hρ : ∀ q : ℝ, 0 < q → ∫ t, Real.exp (-q * t) ∂ρ = Real.exp (-(x : ℝ) * q ^ (1 / θ))) :
    ρ = passageLaw θ x := by
  let _ := passageLaw_isProbabilityMeasure hθ x
  apply measure_eq_of_laplace_on_nonneg h0 (passageLaw_Iio_zero θ x)
  intro q hq
  rw [hρ q hq, integral_exp_neg_passageLaw hθ x hq.le]

end BGW.StableTrees
