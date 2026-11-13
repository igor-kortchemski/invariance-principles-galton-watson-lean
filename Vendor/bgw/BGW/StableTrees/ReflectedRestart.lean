/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableFirstPassage
public import BGW.StableTrees.StableContinuousMinimum
public import BGW.StableTrees.StableLocalMarkov

import BGW.StableTrees.StablePassageSubordinatorPath

/-!
# Reflection, restarts and excursion windows

Deterministic adapters for the Skorokhod reflection of a local càdlàg path: restart formulas,
strict downward passage, and generalized minima on windows around excursion starts (J. Bertoin,
*Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VII, for the reflected process
and its excursions away from the infimum).
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private theorem isRightContinuous_runningInfLoc (f : DLoc) :
    IsRightContinuous (runningInfLoc f) := by
  intro t
  apply tendsto_order.2
  constructor
  · intro a ha
    obtain ⟨a', haa', ha'⟩ := exists_between ha
    have hat : a' < f.1 t := ha'.trans_le (runningInfLoc_le_eval f t ⟨t, by simp⟩)
    have he : {u : ℝ≥0 | a' < f.1 u} ∈ 𝓝[Set.Ioi t] t :=
      (f.2.isRightContinuous t).eventually (isOpen_Ioi.mem_nhds hat)
    obtain ⟨b, htb, hb⟩ := (nhdsGT_basis t).mem_iff.mp he
    filter_upwards [Ioo_mem_nhdsGT htb] with s hs
    apply haa'.trans_le
    apply le_runningInfLoc
    intro u
    by_cases hut : u ≤ t
    · exact ha'.le.trans (runningInfLoc_le_eval f t ⟨u, hut⟩)
    · exact (hb ⟨lt_of_not_ge hut, lt_of_le_of_lt u.2 hs.2⟩).le
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (runningInfLoc_antitone f hs.le).trans_lt hb

private theorem isCadlag_runningInfLoc (f : DLoc) : IsCadlag (runningInfLoc f) where
  isRightContinuous := isRightContinuous_runningInfLoc f
  tendsto_nhdsLT t := ⟨_, (runningInfLoc_antitone f).tendsto_nhdsLT t⟩

/-- The reflected path `t ↦ y + X_t - min 0 (y + I_t)` is càdlàg: `I` is monotone, bounded on
compacts and right-continuous. -/
theorem isCadlag_reflectedFrom (y : ℝ≥0) (f : DLoc) :
    IsCadlag (fun t : ℝ≥0 => (y : ℝ) + f.1 t - min 0 ((y : ℝ) + runningInfLoc f t)) := by
  have hI : IsCadlag (fun t : ℝ≥0 => (y : ℝ) + runningInfLoc f t) :=
    IsCadlag.const.add (isCadlag_runningInfLoc f)
  have hmin : IsCadlag (fun t : ℝ≥0 => min 0 ((y : ℝ) + runningInfLoc f t)) := by
    simpa only [Function.comp_def, id_eq] using
      hI.continuous_comp (continuous_const.min continuous_id)
  exact (IsCadlag.const.add f.2).sub hmin

/-- **Reflection at zero** of `y + X`: `t ↦ y + X_t - min 0 (y + I_t)`. -/
noncomputable def reflectedFrom (y : ℝ≥0) (f : DLoc) : DLoc :=
  ⟨fun t => (y : ℝ) + f.1 t - min 0 ((y : ℝ) + runningInfLoc f t), isCadlag_reflectedFrom y f⟩

/-- Reflection from zero is strongly progressive for the local filtration. -/
theorem isStronglyProgressive_reflectedFrom_zero :
    IsStronglyProgressive DLoc.filtration (fun t (f : DLoc) => (reflectedFrom 0 f).1 t) := by
  apply IsProgressive.isStronglyProgressive
  intro T
  simp only [reflectedFrom, NNReal.coe_zero, zero_add]
  exact (DLoc.isStronglyProgressive_eval.isProgressive T).sub
    (measurable_const.min (isStronglyProgressive_runningInfLoc.isProgressive T))

/-- No-negative-jumps hypothesis, as used in `runningInfLoc_continuous`. -/
def NoNegJumps (f : DLoc) : Prop := ∀ s : ℝ≥0, Function.leftLim f.1 s ≤ f.1 s

/-- **Excursion candidate** of the reflected path from `0`: positive on `(g,d)`, `R(g-) = 0`,
`R(d) = 0`; `R(g) = 0` is NOT required (jump starts allowed). -/
def IsExcursionCandidate (f : DLoc) (g d : ℝ≥0) : Prop :=
  g < d ∧ (∀ t : ℝ≥0, g < t → t < d → 0 < (reflectedFrom 0 f).1 t) ∧
    Function.leftLim (reflectedFrom 0 f).1 g = 0 ∧ (reflectedFrom 0 f).1 d = 0

/-- **Excursion interval** of the reflected path from `0`: an excursion candidate with
`R(g) = 0` (continuous start; jump starts are excluded by design). -/
def IsExcursionInterval (f : DLoc) (g d : ℝ≥0) : Prop :=
  g < d ∧ (∀ t : ℝ≥0, g < t → t < d → 0 < (reflectedFrom 0 f).1 t) ∧
    Function.leftLim (reflectedFrom 0 f).1 g = 0 ∧ (reflectedFrom 0 f).1 g = 0 ∧
      (reflectedFrom 0 f).1 d = 0

private lemma runningInfLoc_zero (f : DLoc) : runningInfLoc f 0 = f.1 0 := by
  apply le_antisymm
  · exact runningInfLoc_le_eval f 0 ⟨0, by simp⟩
  · apply le_runningInfLoc
    intro u
    have hu : (u : ℝ≥0) = 0 := le_antisymm u.2 (by simp)
    rw [hu]

private lemma reflectedFrom_nonneg_aux (y : ℝ≥0) (f : DLoc) (t : ℝ≥0) :
    0 ≤ (reflectedFrom y f).1 t := by
  change 0 ≤ (y : ℝ) + f.1 t - min 0 ((y : ℝ) + runningInfLoc f t)
  have hI := runningInfLoc_le_eval f t ⟨t, by simp⟩
  rcases le_total 0 ((y : ℝ) + runningInfLoc f t) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

private lemma leftLim_reflectedFrom_zero_general {f : DLoc} (hf : NoNegJumps f)
    (g : ℝ≥0) :
    Function.leftLim (reflectedFrom 0 f).1 g =
      Function.leftLim f.1 g - min 0 (runningInfLoc f g) := by
  by_cases hg : g = 0
  · subst g
    rw [leftLim_eq_of_isBot isBot_zero, leftLim_eq_of_isBot isBot_zero]
    simp only [reflectedFrom, NNReal.coe_zero, zero_add]
  let _ : (𝓝[<] g).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr hg⟩
  have hlim : Tendsto (reflectedFrom 0 f).1 (𝓝[<] g)
      (𝓝 (Function.leftLim f.1 g - min 0 (runningInfLoc f g))) := by
    have hf' := f.2.tendsto_nhdsLT_leftLim g
    have hI : ContinuousWithinAt (runningInfLoc f) (Set.Iio g) g :=
      (runningInfLoc_continuous hf).continuousAt.continuousWithinAt
    change Tendsto (fun t => ((0 : ℝ≥0) : ℝ) + f.1 t -
      min 0 (((0 : ℝ≥0) : ℝ) + runningInfLoc f t)) _ _
    simp only [NNReal.coe_zero, zero_add]
    exact hf'.sub (continuousWithinAt_const.min hI)
  exact leftLim_eq_of_tendsto hlim

private lemma leftLim_reflectedFrom_zero {f : DLoc} (hf : NoNegJumps f) (h0 : f.1 0 = 0)
    (g : ℝ≥0) :
    Function.leftLim (reflectedFrom 0 f).1 g = Function.leftLim f.1 g - runningInfLoc f g := by
  rw [leftLim_reflectedFrom_zero_general hf]
  rw [min_eq_right ((runningInfLoc_antitone f (show 0 ≤ g by simp)).trans_eq
    ((runningInfLoc_zero f).trans h0))]

/-- **(i)** Under `NoNegJumps`, `R g = 0` implies `R(g-) = 0` (`R ≥ 0`, `I` continuous, so
`R(g-) = X(g-) - min 0 I_g ≤ X g - min 0 I_g = R g`). -/
theorem leftLim_reflectedFrom_eq_zero_of_noNegJumps {f : DLoc} (hf : NoNegJumps f) {g : ℝ≥0}
    (hg : (reflectedFrom 0 f).1 g = 0) : Function.leftLim (reflectedFrom 0 f).1 g = 0 := by
  by_cases hzero : g = 0
  · subst g
    rw [leftLim_eq_of_isBot isBot_zero]
    exact hg
  let _ : (𝓝[<] g).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, pos_iff_ne_zero.mpr hzero⟩
  have hnonneg : 0 ≤ Function.leftLim (reflectedFrom 0 f).1 g := by
    apply ge_of_tendsto ((reflectedFrom 0 f).2.tendsto_nhdsLT_leftLim g)
    exact Eventually.of_forall (reflectedFrom_nonneg_aux 0 f)
  have hle : Function.leftLim (reflectedFrom 0 f).1 g ≤ (reflectedFrom 0 f).1 g := by
    calc
      Function.leftLim (reflectedFrom 0 f).1 g =
          Function.leftLim f.1 g - min 0 (runningInfLoc f g) :=
        leftLim_reflectedFrom_zero_general hf g
      _ ≤ f.1 g - min 0 (runningInfLoc f g) := sub_le_sub_right (hf g) _
      _ = (reflectedFrom 0 f).1 g := by
        simp only [reflectedFrom, NNReal.coe_zero, zero_add]
  exact le_antisymm (hle.trans_eq hg) hnonneg

/-- **(ii)** An excursion candidate with `R g = 0` is an excursion interval. -/
theorem isExcursionInterval_of_isExcursionCandidate {f : DLoc} {g d : ℝ≥0}
    (h : IsExcursionCandidate f g d) (hg : (reflectedFrom 0 f).1 g = 0) :
    IsExcursionInterval f g d :=
  ⟨h.1, h.2.1, h.2.2.1, hg, h.2.2.2⟩

/-- An excursion interval is a candidate. -/
theorem IsExcursionInterval.isExcursionCandidate {f : DLoc} {g d : ℝ≥0}
    (h : IsExcursionInterval f g d) : IsExcursionCandidate f g d :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.2⟩

/-- Reflection is nonnegative. -/
theorem reflectedFrom_nonneg (y : ℝ≥0) (f : DLoc) (t : ℝ≥0) : 0 ≤ (reflectedFrom y f).1 t := by
  change 0 ≤ (y : ℝ) + f.1 t - min 0 ((y : ℝ) + runningInfLoc f t)
  have hI := runningInfLoc_le_eval f t ⟨t, by simp⟩
  rcases le_total 0 ((y : ℝ) + runningInfLoc f t) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h]
    linarith

/-- For `X_0 = 0` the reflection from `0` is `X - I`. -/
theorem reflectedFrom_zero_apply {f : DLoc} (h0 : f.1 0 = 0) (t : ℝ≥0) :
    (reflectedFrom 0 f).1 t = f.1 t - runningInfLoc f t := by
  change ((0 : ℝ≥0) : ℝ) + f.1 t - min 0 (((0 : ℝ≥0) : ℝ) + runningInfLoc f t) = _
  simp only [NNReal.coe_zero, zero_add]
  rw [min_eq_right ((runningInfLoc_antitone f (show 0 ≤ t by simp)).trans_eq
    ((runningInfLoc_zero f).trans h0))]

private lemma bddBelow_future_range_reflected (f : DLoc) (s t : ℝ≥0) :
    BddBelow (Set.range (fun u : Set.Iic t => f.1 (s + u))) := by
  apply (bddBelow_runningInf_range f (s + t)).mono
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨s + u, add_le_add le_rfl u.2⟩, rfl⟩

private lemma runningInfLoc_shift_eq (f : DLoc) (s t : ℝ≥0) :
    runningInfLoc (DLoc.shift s f) t =
      (⨅ u : Set.Iic t, f.1 (s + u)) - f.1 s := by
  let A : ℝ := ⨅ u : Set.Iic t, f.1 (s + u)
  have hA (u : Set.Iic t) : A ≤ f.1 (s + u) :=
    ciInf_le (bddBelow_future_range_reflected f s t) u
  apply le_antisymm
  · apply le_of_forall_gt
    intro a ha
    have ha' : A < a + f.1 s := by linarith
    obtain ⟨u, hu⟩ := (ciInf_lt_iff (bddBelow_future_range_reflected f s t)).mp ha'
    exact (ciInf_le (bddBelow_runningInf_range (DLoc.shift s f) t) u).trans_lt
      (by change f.1 (s + u) - f.1 s < a; linarith)
  · apply le_ciInf
    intro u
    exact sub_le_sub_right (hA u) (f.1 s)

private lemma runningInfLoc_add_eq_min (f : DLoc) (s t : ℝ≥0) :
    runningInfLoc f (s + t) =
      min (runningInfLoc f s) (f.1 s + runningInfLoc (DLoc.shift s f) t) := by
  let A : ℝ := ⨅ u : Set.Iic t, f.1 (s + u)
  have hA (u : Set.Iic t) : A ≤ f.1 (s + u) :=
    ciInf_le (bddBelow_future_range_reflected f s t) u
  have hshift : f.1 s + runningInfLoc (DLoc.shift s f) t = A := by
    rw [runningInfLoc_shift_eq]
    dsimp [A]
    ring
  rw [hshift]
  apply le_antisymm
  · apply le_min
    · exact runningInfLoc_antitone f (by simp)
    · apply le_ciInf
      intro u
      exact runningInfLoc_le_eval f (s + t) ⟨s + u, add_le_add le_rfl u.2⟩
  · apply le_ciInf
    intro v
    by_cases hvs : (v : ℝ≥0) ≤ s
    · exact (min_le_left _ _).trans (runningInfLoc_le_eval f s ⟨v, hvs⟩)
    · have hsv : s ≤ (v : ℝ≥0) := le_of_not_ge hvs
      let u : ℝ≥0 := (v : ℝ≥0) - s
      have hut : u ≤ t := by
        apply tsub_le_iff_right.mpr
        have hv : (v : ℝ≥0) ≤ s + t := v.2
        simpa only [add_comm t s] using hv
      have huv : s + u = (v : ℝ≥0) := add_tsub_cancel_of_le hsv
      rw [← huv]
      exact (min_le_right _ _).trans (hA ⟨u, hut⟩)

/-- **Deterministic restart.** Reflection from `y` at time `s + u` is the reflection, from the
value `R_s` reached at `s`, of the centered shifted path at time `u`.  No hypothesis on `f`. -/
theorem reflectedFrom_restart (y : ℝ≥0) (f : DLoc) (s u : ℝ≥0) :
    (reflectedFrom y f).1 (s + u) =
      (reflectedFrom (⟨(reflectedFrom y f).1 s, reflectedFrom_nonneg y f s⟩ : ℝ≥0)
        (DLoc.shift s f)).1 u := by
  change (y : ℝ) + f.1 (s + u) - min 0 ((y : ℝ) + runningInfLoc f (s + u)) =
    ((y : ℝ) + f.1 s - min 0 ((y : ℝ) + runningInfLoc f s)) +
      (f.1 (s + u) - f.1 s) -
      min 0 (((y : ℝ) + f.1 s - min 0 ((y : ℝ) + runningInfLoc f s)) +
        runningInfLoc (DLoc.shift s f) u)
  rw [runningInfLoc_add_eq_min]
  simp only [min_def]
  split_ifs <;> ring_nf at * <;> linarith

/-- **Restart at a random time** (everywhere form; on `{τ f < ⊤}`; junk shift otherwise). -/
theorem reflectedFrom_restart_shiftAt (y : ℝ≥0) (τ : DLoc → ℝ≥0∞) {f : DLoc} (hτ : τ f < ⊤)
    (u : ℝ≥0) :
    (reflectedFrom y f).1 ((τ f).toNNReal + u) =
      (reflectedFrom (⟨(reflectedFrom y f).1 (τ f).toNNReal,
        reflectedFrom_nonneg y f _⟩ : ℝ≥0) (DLoc.shiftAt τ f)).1 u := by
  have _hτ := hτ
  exact reflectedFrom_restart y f (τ f).toNNReal u

/-- Joint measurability of the reflection in `(y, f)`. -/
theorem measurable_reflectedFrom : Measurable (fun p : ℝ≥0 × DLoc => reflectedFrom p.1 p.2) := by
  rw [measurable_iff_comap_le]
  change (⨆ t : ℝ≥0, MeasurableSpace.comap (DLoc.eval t) inferInstance).comap
      (fun p : ℝ≥0 × DLoc => reflectedFrom p.1 p.2) ≤ _
  rw [MeasurableSpace.comap_iSup, iSup_le_iff]
  intro t
  rw [MeasurableSpace.comap_comp]
  have hcoord : Measurable (fun p : ℝ≥0 × DLoc => (reflectedFrom p.1 p.2).1 t) := by
    change Measurable (fun p : ℝ≥0 × DLoc =>
      (p.1 : ℝ) + p.2.1 t - min 0 ((p.1 : ℝ) + runningInfLoc p.2 t))
    have hf : Measurable (fun p : ℝ≥0 × DLoc => p.2.1 t) :=
      (DLoc.measurable_eval t).comp measurable_snd
    have hI : Measurable (fun p : ℝ≥0 × DLoc => runningInfLoc p.2 t) :=
      measurable_runningInfLoc_uncurry.comp (measurable_const.prodMk measurable_snd)
    exact ((measurable_coe_nnreal_real.comp measurable_fst).add hf).sub
      (measurable_const.min ((measurable_coe_nnreal_real.comp measurable_fst).add hI))
  have hcoord' : Measurable (fun p : ℝ≥0 × DLoc => DLoc.eval t (reflectedFrom p.1 p.2)) := by
    simpa only [DLoc.eval] using hcoord
  exact hcoord'.comap_le

/-- Joint measurability of `(y, f, t) ↦ (reflectedFrom y f) t`. -/
theorem measurable_reflectedFrom_eval :
    Measurable (fun p : ℝ≥0 × DLoc × ℝ≥0 => (reflectedFrom p.1 p.2.1).1 p.2.2) := by
  have hpath : Measurable (fun p : ℝ≥0 × DLoc × ℝ≥0 => reflectedFrom p.1 p.2.1) :=
    measurable_reflectedFrom.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
  exact DLoc.measurable_eval₂.comp (hpath.prodMk (measurable_snd.comp measurable_snd))

/-- **First passage as the generalized inverse of the running infimum.** Everywhere (no
hypothesis): `T_x = inf {t | I_t < -x}`. -/
theorem firstPassageBelow_eq_inf_runningInf (x : ℝ≥0) (f : DLoc) :
    firstPassageBelow x f = ⨅ (t : ℝ≥0) (_ : runningInfLoc f t < -(x : ℝ)), (t : WithTop ℝ≥0) := by
  apply le_antisymm
  · apply le_iInf
    intro t
    apply le_iInf
    intro ht
    obtain ⟨u, hut, hu⟩ := exists_eval_lt_of_runningInfLoc_lt ht
    exact (iInf_le_of_le u (iInf_le _ hu)).trans (by exact_mod_cast hut)
  · apply le_iInf
    intro t
    apply le_iInf
    intro ht
    exact iInf_le_of_le t (iInf_le _
      ((runningInfLoc_le_eval f t ⟨t, by simp⟩).trans_lt ht))

/-- **Reflection vanishes at the passage time** (creeping): for a spectrally positive path with
`X_0 = 0` and `T_x` finite, `I_{T_x} = -x = X_{T_x}`, hence `R_{T_x} = 0`. -/
theorem reflectedFrom_firstPassageBelow {f : DLoc} (hf : NoNegJumps f) (h0 : f.1 0 = 0)
    {x : ℝ≥0} (hx : 0 < x) (hT : firstPassageBelow x f < ⊤) :
    runningInfLoc f ((firstPassageBelow x f).untopD 0) = -(x : ℝ) ∧
      (reflectedFrom 0 f).1 ((firstPassageBelow x f).untopD 0) = 0 := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hT)
  have hs' : firstPassageBelow x f = (s : WithTop ℝ≥0) := hs.symm
  have hval : f.1 s = -(x : ℝ) := by
    apply eval_eq_of_strictPassageBelow_eq_coe hf hs'
    simpa only [h0] using (show -(x : ℝ) < 0 by
      exact neg_lt_zero.mpr (by exact_mod_cast hx))
  have hI : runningInfLoc f s = -(x : ℝ) :=
    runningInfLoc_eq_of_firstPassageBelow_eq_coe hs' hval
  have hsu : ((firstPassageBelow x f).untopD 0) = s := by simp only [hs', WithTop.untopD_coe]
  rw [hsu]
  refine ⟨hI, ?_⟩
  rw [reflectedFrom_zero_apply h0, hval, hI]
  ring

/-- **Restart at the passage time**: the reflected path after `T_x` is the reflection from `0`
of the centered post-`T_x` path. -/
theorem reflectedFrom_restart_firstPassageBelow {f : DLoc} (hf : NoNegJumps f) (h0 : f.1 0 = 0)
    {x : ℝ≥0} (hx : 0 < x) (hT : firstPassageBelow x f < ⊤) (u : ℝ≥0) :
    (reflectedFrom 0 f).1 ((firstPassageBelow x f).untopD 0 + u) =
      (reflectedFrom 0 (DLoc.shiftAt (firstPassageBelow x) f)).1 u := by
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp (ne_of_lt hT)
  have hs' : firstPassageBelow x f = (s : WithTop ℝ≥0) := hs.symm
  have hval : f.1 s = -(x : ℝ) := by
    apply eval_eq_of_strictPassageBelow_eq_coe hf hs'
    simpa only [h0] using (show -(x : ℝ) < 0 by
      exact neg_lt_zero.mpr (by exact_mod_cast hx))
  have hsu : ((firstPassageBelow x f).untopD 0) = s := by simp only [hs', WithTop.untopD_coe]
  have hshift : DLoc.shiftAt (firstPassageBelow x) f = DLoc.shift s f := by
    unfold DLoc.shiftAt
    rw [hs']
    rfl
  rw [hsu, reflectedFrom_zero_apply h0, hshift, reflectedFrom_zero_apply]
  · exact reflected_shift_of_creeping hs' hval u
  · change f.1 (s + 0) - f.1 s = 0
    simp

private lemma leftLim_eq_runningInf_of_candidate {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d : ℝ≥0} (h : IsExcursionCandidate f g d) :
    Function.leftLim f.1 g = runningInfLoc f g := by
  have hleft := h.2.2.1
  rw [leftLim_reflectedFrom_zero hf h0] at hleft
  linarith

private lemma runningInf_start_le_eval_of_candidate {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d : ℝ≥0} (h : IsExcursionCandidate f g d) {u : ℝ≥0}
    (hud : u < d) : runningInfLoc f g ≤ f.1 u := by
  by_contra hnot
  have hu : f.1 u < runningInfLoc f g := lt_of_not_ge hnot
  let a : ℝ := (f.1 u + runningInfLoc f g) / 2
  have hua : f.1 u < a := by dsimp [a]; linarith
  have haI : a < runningInfLoc f g := by dsimp [a]; linarith
  have hI0 : runningInfLoc f g ≤ 0 :=
    (runningInfLoc_le_eval f g ⟨0, by simp⟩).trans_eq h0
  have ha0 : a < f.1 0 := h0 ▸ haI.trans_le hI0
  let x : ℝ≥0 := Real.toNNReal (-a)
  have hx : 0 < x := Real.toNNReal_pos.mpr (neg_pos.mpr (ha0.trans_eq h0))
  have hxval : -(x : ℝ) = a := by
    change -max (-a) 0 = a
    rw [max_eq_left (neg_nonneg.mpr (ha0.trans_eq h0).le), neg_neg]
  have hpass : firstPassageBelow x f ≤ (u : WithTop ℝ≥0) :=
    firstPassageBelow_le_of_eval_lt (hxval ▸ hua)
  obtain ⟨s, hs⟩ := WithTop.ne_top_iff_exists.mp
    (ne_top_of_le_ne_top WithTop.coe_ne_top hpass)
  have hs' : firstPassageBelow x f = (s : WithTop ℝ≥0) := hs.symm
  have hval : f.1 s = -(x : ℝ) := by
    apply eval_eq_of_strictPassageBelow_eq_coe hf hs'
    exact hxval ▸ ha0
  have hI : runningInfLoc f s = -(x : ℝ) :=
    runningInfLoc_eq_of_firstPassageBelow_eq_coe hs' hval
  have hgs : g < s := by
    by_contra hng
    have hsg : s ≤ g := le_of_not_gt hng
    have := runningInfLoc_le_eval f g ⟨s, hsg⟩
    rw [hval, hxval] at this
    linarith
  have hsu : s ≤ u := by
    rw [hs'] at hpass
    exact_mod_cast hpass
  have hpos := h.2.1 s hgs (hsu.trans_lt hud)
  rw [reflectedFrom_zero_apply h0, hval, hI] at hpos
  linarith

private lemma runningInfLoc_const_of_candidate_lt {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d : ℝ≥0} (h : IsExcursionCandidate f g d) {t : ℝ≥0}
    (hgt : g ≤ t) (htd : t < d) : runningInfLoc f t = runningInfLoc f g := by
  apply le_antisymm (runningInfLoc_antitone f hgt)
  apply le_runningInfLoc
  intro u
  exact runningInf_start_le_eval_of_candidate hf h0 h (u.2.trans_lt htd)

private lemma runningInfLoc_const_of_candidate {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d : ℝ≥0} (h : IsExcursionCandidate f g d) {t : ℝ≥0}
    (hgt : g ≤ t) (htd : t ≤ d) : runningInfLoc f t = runningInfLoc f g := by
  rcases htd.eq_or_lt with hteq | htd
  · subst t
    let _ : (𝓝[<] d).NeBot := nhdsLT_neBot_of_exists_lt ⟨g, h.1⟩
    have hlim : Tendsto (runningInfLoc f) (𝓝[<] d) (𝓝 (runningInfLoc f g)) := by
      apply tendsto_const_nhds.congr'
      filter_upwards [Ioo_mem_nhdsLT h.1] with u hu
      exact (runningInfLoc_const_of_candidate_lt hf h0 h hu.1.le hu.2).symm
    have hleft : Function.leftLim (runningInfLoc f) d = runningInfLoc f g :=
      leftLim_eq_of_tendsto hlim
    have hcont : ContinuousWithinAt (runningInfLoc f) (Set.Iic d) d :=
      (runningInfLoc_continuous hf).continuousAt.continuousWithinAt
    exact hcont.leftLim_eq.symm.trans hleft
  · exact runningInfLoc_const_of_candidate_lt hf h0 h hgt htd

/-- **The running infimum is constant on an excursion interval** (spectrally positive,
`X_0 = 0`): `I_t = I_g` for `g ≤ t ≤ d`. -/
theorem runningInfLoc_const_of_isExcursionInterval {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d : ℝ≥0} (h : IsExcursionInterval f g d) {t : ℝ≥0}
    (hgt : g ≤ t) (htd : t ≤ d) : runningInfLoc f t = runningInfLoc f g :=
  runningInfLoc_const_of_candidate hf h0 h.isExcursionCandidate hgt htd

/-- The left limit of `X` at the start of an excursion is the running infimum there. -/
theorem leftLim_eq_runningInf_of_isExcursionInterval {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d : ℝ≥0} (h : IsExcursionInterval f g d) :
    Function.leftLim f.1 g = runningInfLoc f g :=
  leftLim_eq_runningInf_of_candidate hf h0 h.isExcursionCandidate

/-- **Rational windows around the start `g`.** Every excursion interval with `0 < g` has
nonnegative rationals `r < g < q < d` (for `g = 0` no `r` exists, hence `0 < g`). -/
theorem exists_rat_window_of_isExcursionInterval {f : DLoc} {g d : ℝ≥0}
    (h : IsExcursionInterval f g d) (hg : 0 < g) :
    ∃ r q : ℚ≥0, (r : ℝ≥0) < g ∧ g < (q : ℝ≥0) ∧ (q : ℝ≥0) < d := by
  obtain ⟨r, hr0, hrg⟩ := exists_rat_btwn (show (0 : ℝ) < g by exact_mod_cast hg)
  obtain ⟨q, hgq, hqd⟩ := exists_rat_btwn (show (g : ℝ) < d by exact_mod_cast h.1)
  have hr0' : (0 : ℚ) ≤ r := by exact_mod_cast hr0.le
  have hq0R : (0 : ℝ) ≤ q := (show (0 : ℝ) ≤ g by positivity).trans hgq.le
  have hq0 : (0 : ℚ) ≤ q := by exact_mod_cast hq0R
  refine ⟨⟨r, hr0'⟩, ⟨q, hq0⟩, ?_, ?_, ?_⟩
  · exact_mod_cast hrg
  · exact_mod_cast hgq
  · exact_mod_cast hqd

private lemma bddBelow_window_range (f : DLoc) (r q : ℝ≥0) :
    BddBelow (Set.range (fun u : Set.Icc r q => f.1 u)) := by
  apply (bddBelow_runningInf_range f q).mono
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨u, u.2.2⟩, rfl⟩

/-- **Candidate version of the window infimum**: for an excursion candidate `(g,d)` (no `R g = 0`
needed) under `NoNegJumps`, the infimum of `X` over `[r,q]`, `r < g < q < d`, equals `X(g-)`. -/
theorem iInf_window_eq_leftLim_of_isExcursionCandidate {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d r q : ℝ≥0} (h : IsExcursionCandidate f g d) (hrg : r < g) (hgq : g < q)
    (hqd : q < d) :
    (⨅ u : Set.Icc r q, f.1 u) = Function.leftLim f.1 g := by
  let _ : Nonempty (Set.Icc r q) := ⟨⟨r, le_rfl, hrg.le.trans hgq.le⟩⟩
  let _ : (𝓝[<] g).NeBot := nhdsLT_neBot_of_exists_lt ⟨r, hrg⟩
  apply le_antisymm
  · apply ge_of_tendsto (f.2.tendsto_nhdsLT_leftLim g)
    filter_upwards [Ioo_mem_nhdsLT hrg] with u hu
    exact ciInf_le (bddBelow_window_range f r q) ⟨u, hu.1.le, hu.2.le.trans hgq.le⟩
  · rw [leftLim_eq_runningInf_of_candidate hf h0 h]
    apply le_ciInf
    intro u
    by_cases hug : (u : ℝ≥0) ≤ g
    · exact runningInfLoc_le_eval f g ⟨u, hug⟩
    · have hgu : g < (u : ℝ≥0) := lt_of_not_ge hug
      have huI : runningInfLoc f u = runningInfLoc f g :=
        runningInfLoc_const_of_candidate_lt hf h0 h hgu.le (u.2.2.trans_lt hqd)
      have hpos := h.2.1 u hgu (u.2.2.trans_lt hqd)
      rw [reflectedFrom_zero_apply h0, huI] at hpos
      linarith

/-- **The window infimum is the left limit at the start.** If `(g,d)` is an excursion interval and
`r < g < q < d`, the infimum of `X` over `[r,q]` equals `X(g-) = I_g`. -/
theorem iInf_window_eq_leftLim_of_isExcursionInterval {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d r q : ℝ≥0} (h : IsExcursionInterval f g d) (hrg : r < g) (hgq : g < q)
    (hqd : q < d) :
    (⨅ u : Set.Icc r q, f.1 u) = Function.leftLim f.1 g :=
  iInf_window_eq_leftLim_of_isExcursionCandidate hf h0 h.isExcursionCandidate hrg hgq hqd

/-- The time `g - r`, as a point of the horizon `[0, q - r]` of the shifted window. -/
noncomputable def shiftedWindowTime (r g q : ℝ≥0) (hrg : r ≤ g) (hgq : g ≤ q) :
    Set.Icc (0 : ℝ) ((q - r : ℝ≥0) : ℝ) :=
  ⟨(g : ℝ) - r, sub_nonneg.2 (by exact_mod_cast hrg), by
    rw [NNReal.coe_sub (hrg.trans hgq)]
    have : (g : ℝ) ≤ q := by exact_mod_cast hgq
    linarith⟩

private theorem leftLim_dloc_restrict_reflected {f : DLoc} {t T : ℝ≥0}
    (ht : 0 < t) (htT : t < T) :
    Function.leftLim (DLoc.restrict T f)
      ⟨t, t.2, (show (t : ℝ) ≤ (T : ℝ) from htT.le)⟩ = Function.leftLim f.1 t := by
  let t' : Set.Icc (0 : ℝ) (T : ℝ) := ⟨t, t.2, htT.le⟩
  let inc : Set.Icc (0 : ℝ) (T : ℝ) → ℝ≥0 := fun u => ⟨u, u.2.1⟩
  have hinc : Continuous inc := Continuous.subtype_mk continuous_subtype_val fun u => u.2.1
  have hleft : Tendsto inc (𝓝[<] t') (𝓝[<] t) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hinc.continuousAt, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hu
  let z : Set.Icc (0 : ℝ) (T : ℝ) := ⟨0, le_rfl, T.2⟩
  have hz : z < t' := ht
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  let _ : (𝓝[<] t').NeBot := nhdsLT_neBot_of_exists_lt ⟨z, hz⟩
  apply leftLim_eq_of_tendsto
  exact (f.2.tendsto_nhdsLT_leftLim t).comp hleft

private lemma leftLim_shift_reflected (f : DLoc) {r g : ℝ≥0} (hrg : r < g) :
    Function.leftLim (DLoc.shift r f).1 (g - r) =
      Function.leftLim f.1 g - f.1 r := by
  let t : ℝ≥0 := g - r
  have hrt : r + t = g := add_tsub_cancel_of_le hrg.le
  have hmap : Tendsto (fun u : ℝ≥0 => r + u) (𝓝[<] t) (𝓝[<] g) := by
    apply tendsto_nhdsWithin_iff.mpr
    constructor
    · have hc : Continuous (fun u : ℝ≥0 => r + u) := continuous_const.add continuous_id
      have htend : Tendsto (fun u : ℝ≥0 => r + u) (𝓝 t) (𝓝 g) := by
        rw [← hrt]
        exact hc.continuousAt
      exact htend.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with u hu
      change r + u < g
      have hlt : r + u < r + t := (add_lt_add_iff_left r).mpr hu
      simpa only [hrt] using hlt
  have ht : 0 < t := tsub_pos_of_lt hrg
  let _ : (𝓝[<] t).NeBot := nhdsLT_neBot_of_exists_lt ⟨0, ht⟩
  apply leftLim_eq_of_tendsto
  exact ((f.2.tendsto_nhdsLT_leftLim g).comp hmap).sub_const (f.1 r)

private lemma leftLim_shiftedWindowTime {f : DLoc} {g r q : ℝ≥0}
    (hrg : r < g) (hgq : g < q) :
    Function.leftLim (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le) = Function.leftLim f.1 g - f.1 r := by
  have ht : 0 < g - r := tsub_pos_of_lt hrg
  have htT : g - r < q - r := by
    rw [← NNReal.coe_lt_coe, NNReal.coe_sub hrg.le, NNReal.coe_sub (hrg.le.trans hgq.le)]
    exact sub_lt_sub_right (show (g : ℝ) < q by exact_mod_cast hgq) _
  have htime : shiftedWindowTime r g q hrg.le hgq.le =
      (⟨((g - r : ℝ≥0) : ℝ), (g - r).2,
        (show ((g - r : ℝ≥0) : ℝ) ≤ ((q - r : ℝ≥0) : ℝ) from htT.le)⟩ :
        Set.Icc (0 : ℝ) ((q - r : ℝ≥0) : ℝ)) := by
    apply Subtype.ext
    exact (NNReal.coe_sub hrg.le).symm
  rw [htime, leftLim_dloc_restrict_reflected ht htT, leftLim_shift_reflected f hrg]

private lemma isGenMinimizer_shift_restrict_of_candidate_aux {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d r q : ℝ≥0} (h : IsExcursionCandidate f g d) (hrg : r < g) (hgq : g < q)
    (hqd : q < d) :
    IsGenMinimizer (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le) := by
  let _ : Nonempty (Set.Icc (0 : ℝ) ((q - r : ℝ≥0) : ℝ)) :=
    ⟨⟨0, le_rfl, (q - r).2⟩⟩
  have hleft := leftLim_shiftedWindowTime (f := f) hrg hgq
  have hval : (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le) = f.1 g - f.1 r := by
    let gt : ℝ≥0 := ⟨(shiftedWindowTime r g q hrg.le hgq.le : ℝ),
      (shiftedWindowTime r g q hrg.le hgq.le).2.1⟩
    change f.1 (r + gt) - f.1 r = _
    have htime : r + gt = g := by
      apply NNReal.coe_injective
      change (r : ℝ) + ((g : ℝ) - r) = g
      ring
    rw [htime]
  have hgen : genVal (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le) = Function.leftLim f.1 g - f.1 r := by
    rw [genVal, min_eq_left, hleft]
    rw [hleft, hval]
    exact sub_le_sub_right (hf g) _
  rw [IsGenMinimizer, hgen]
  apply le_antisymm
  · apply le_ciInf
    intro t
    let u : ℝ≥0 := r + ⟨(t : ℝ), t.2.1⟩
    have huq : u ≤ q := by
      rw [← NNReal.coe_le_coe]
      have ht : (t : ℝ) ≤ ((q - r : ℝ≥0) : ℝ) := t.2.2
      have hqr : ((q - r : ℝ≥0) : ℝ) = (q : ℝ) - (r : ℝ) :=
        NNReal.coe_sub (hrg.le.trans hgq.le)
      change (r : ℝ) + (t : ℝ) ≤ (q : ℝ)
      linarith
    have hru : r ≤ u := by
      rw [← NNReal.coe_le_coe]
      change (r : ℝ) ≤ (r : ℝ) + (t : ℝ)
      have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
      linarith
    have hinf := ciInf_le (bddBelow_window_range f r q) ⟨u, hru, huq⟩
    rw [iInf_window_eq_leftLim_of_isExcursionCandidate hf h0 h hrg hgq hqd] at hinf
    change Function.leftLim f.1 g - f.1 r ≤ f.1 u - f.1 r
    exact sub_le_sub_right hinf _
  · exact (iInf_le_genVal _ _).trans_eq hgen

/-- **Window minimizer adapter** (feeds `IsStableLevyLaw.ae_continuousAt_of_isGenMinimizer`):
for an excursion interval `(g,d)` and `r < g < q < d`, `g - r` is a generalized minimizer of the
centered shift at `r`, restricted to the horizon `[0, q - r]`.  (Here `g` is generalized, through
its left limit.) -/
theorem isGenMinimizer_shift_restrict_of_isExcursionInterval {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d r q : ℝ≥0} (h : IsExcursionInterval f g d) (hrg : r < g) (hgq : g < q)
    (hqd : q < d) :
    IsGenMinimizer (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le) :=
  isGenMinimizer_shift_restrict_of_candidate_aux hf h0 h.isExcursionCandidate hrg hgq hqd

/-- **Window minimizer adapter for candidates**: the same statement for an excursion candidate
`(g,d)` (jump start allowed); the generalized minimum over the rational window is attained at `g`
as a left limit.  Sealed continuity of minimizers on countably many rational windows then gives
`R g = 0` (a.s., stochastic step). -/
theorem isGenMinimizer_shift_restrict_of_isExcursionCandidate {f : DLoc} (hf : NoNegJumps f)
    (h0 : f.1 0 = 0) {g d r q : ℝ≥0} (h : IsExcursionCandidate f g d) (hrg : r < g) (hgq : g < q)
    (hqd : q < d) :
    IsGenMinimizer (DLoc.restrict (q - r) (DLoc.shift r f))
      (shiftedWindowTime r g q hrg.le hgq.le) :=
  isGenMinimizer_shift_restrict_of_candidate_aux hf h0 h hrg hgq hqd

/-- **End of an excursion = first zero of the reflection after any interior rational time**:
`d = inf {t ≥ r | R_t = 0}` for `r ∈ (g,d)`. -/
theorem excursionEnd_eq_sInf_zero {f : DLoc} {g d r : ℝ≥0} (h : IsExcursionInterval f g d)
    (hgr : g < r) (hrd : r < d) :
    d = sInf {t : ℝ≥0 | r ≤ t ∧ (reflectedFrom 0 f).1 t = 0} := by
  have hd : d ∈ {t : ℝ≥0 | r ≤ t ∧ (reflectedFrom 0 f).1 t = 0} :=
    ⟨hrd.le, h.2.2.2.2⟩
  apply le_antisymm
  · apply le_csInf ⟨d, hd⟩
    intro t ht
    apply le_of_not_gt
    intro htd
    have hgt : g < t := hgr.trans_le ht.1
    exact (ne_of_gt (h.2.1 t hgt htd)) ht.2
  · exact csInf_le (OrderBot.bddBelow _) hd

/-- **Excursion intervals are disjoint**: a later start cannot lie inside an earlier interval. -/
theorem IsExcursionInterval.eq_of_lt {f : DLoc} {g d g' d' : ℝ≥0}
    (h : IsExcursionInterval f g d) (h' : IsExcursionInterval f g' d') (hlt : g < g')
    (hover : g' < d) : False := by
  exact (ne_of_gt (h.2.1 g' hlt hover)) h'.2.2.2.1

end BGW.StableTrees
