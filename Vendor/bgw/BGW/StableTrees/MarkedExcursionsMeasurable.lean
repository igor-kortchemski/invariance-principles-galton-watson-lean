/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarkedExcursionsBasic
import BGW.StableTrees.MarkedExcursionsSupport
import Mathlib.Data.NNRat.Encodable

/-!
# Measurability of the marked excursion measure

Rational physical times enumerate all passage-jump labels through local time. Keeping the
first occurrence of each label yields a measurable sum of Dirac masses.

(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV, Sections 2–4; K. Itô,
Poisson point processes attached to Markov processes, Proc. Sixth Berkeley Symp. Math. Statist.
Probab. 3 (1972), 225–239.)
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private noncomputable def rationalTimes : ℕ → ℚ≥0 :=
  (exists_surjective_nat ℚ≥0).choose

private theorem rationalTimes_surjective : Function.Surjective rationalTimes :=
  (exists_surjective_nat ℚ≥0).choose_spec

private noncomputable def rationalLabel (n : ℕ) (f : DLoc) : ℝ≥0 :=
  localTimeNN f (rationalTimes n)

private theorem measurable_rationalLabel (n : ℕ) : Measurable (rationalLabel n) :=
  (measurable_localTime_uncurry.comp (measurable_const.prodMk measurable_id)).real_toNNReal

private def firstLabel (n : ℕ) (f : DLoc) : Prop :=
  rationalLabel n f ∈ passageJumpSet f ∧ ∀ k < n, rationalLabel k f ≠ rationalLabel n f

private theorem measurableSet_firstLabel (n : ℕ) : MeasurableSet {f | firstLabel n f} := by
  have hT := measurable_passageTime_uncurry.comp
    ((measurable_rationalLabel n).prodMk measurable_id)
  have hS := measurable_passageTimeMinus_uncurry.comp
    ((measurable_rationalLabel n).prodMk measurable_id)
  have hJ : MeasurableSet {f | rationalLabel n f ∈ passageJumpSet f} := by
    change MeasurableSet {f | (0 : ℝ≥0) < rationalLabel n f ∧
      passageTimeMinus (rationalLabel n f) f < passageTime (rationalLabel n f) f}
    exact (measurableSet_lt measurable_const (measurable_rationalLabel n)).inter
      (measurableSet_lt (α := ℝ≥0) hS hT)
  change MeasurableSet ({f | rationalLabel n f ∈ passageJumpSet f} ∩
    {f | ∀ k < n, rationalLabel k f ≠ rationalLabel n f})
  apply hJ.inter
  rw [Set.ofPred_forall]
  apply MeasurableSet.iInter
  intro k
  by_cases hk : k < n
  · simpa only [hk, true_implies, ← Set.compl_ofPred] using
      (measurableSet_eq_fun (measurable_rationalLabel k) (measurable_rationalLabel n)).compl
  · simp only [hk, false_implies, ofPred_true, MeasurableSet.univ]

private theorem measurable_rationalMark (n : ℕ) :
    Measurable (fun f => (rationalLabel n f, jumpExcursion (rationalLabel n f) f)) := by
  have hT := measurable_passageTime_uncurry.comp
    ((measurable_rationalLabel n).prodMk measurable_id)
  have hS := measurable_passageTimeMinus_uncurry.comp
    ((measurable_rationalLabel n).prodMk measurable_id)
  exact (measurable_rationalLabel n).prodMk
    (measurable_excursionCut.comp (hS.prodMk (hT.prodMk measurable_id)))

private noncomputable def enumeratedPointMeasure (f : DLoc) : Measure (ℝ≥0 × Excursion) :=
  Measure.sum fun n =>
    letI := Classical.propDecidable (firstLabel n f)
    if firstLabel n f then Measure.dirac (rationalLabel n f, jumpExcursion (rationalLabel n f) f)
    else 0

private theorem measurable_enumeratedPointMeasure : Measurable enumeratedPointMeasure := by
  classical
  apply Measure.measurable_of_measurable_coe
  intro s hs
  simp only [enumeratedPointMeasure, Measure.sum_apply _ hs]
  apply Measurable.tsum
  intro n
  have hmeasure : Measurable (fun f => if firstLabel n f then
      Measure.dirac (rationalLabel n f, jumpExcursion (rationalLabel n f) f) else 0) :=
    (Measure.measurable_dirac.comp (measurable_rationalMark n)).ite
      (measurableSet_firstLabel n) measurable_const
  exact (Measure.measurable_coe hs).comp hmeasure

private theorem enumeratedPointMeasure_eq {f : DLoc} (hf : (passageJumpSet f).Countable)
    (hcover : ∀ x ∈ passageJumpSet f, ∃ n, rationalLabel n f = x) :
    enumeratedPointMeasure f = excursionPointMeasure f := by
  classical
  let e₀ : {n : ℕ | firstLabel n f} → passageJumpSet f :=
    fun n => ⟨rationalLabel n f, n.2.1⟩
  have hinj : Function.Injective e₀ := by
    intro n m h
    have heq : rationalLabel n f = rationalLabel m f := congrArg Subtype.val h
    apply Subtype.ext
    rcases lt_trichotomy (n : ℕ) m with hlt | he | hgt
    · exact False.elim (m.2.2 n hlt heq)
    · exact he
    · exact False.elim (n.2.2 m hgt heq.symm)
  have hsurj : Function.Surjective e₀ := by
    intro x
    have hex := hcover x x.2
    let n := Nat.find hex
    have hn : rationalLabel n f = x := Nat.find_spec hex
    have hfirst : firstLabel n f := by
      refine ⟨hn ▸ x.2, ?_⟩
      intro k hk he
      exact Nat.find_min hex hk (he.trans hn)
    exact ⟨⟨n, hfirst⟩, Subtype.ext hn⟩
  let e := Equiv.ofBijective e₀ ⟨hinj, hsurj⟩
  ext s hs
  rw [excursionPointMeasure, ite_eq_left hf, enumeratedPointMeasure,
    Measure.sum_apply _ hs, Measure.sum_apply _ hs]
  rw [← e.tsum_eq (fun x : passageJumpSet f =>
    Measure.dirac ((x : ℝ≥0), jumpExcursion x f) s)]
  change (∑' n : ℕ, (if firstLabel n f then
      Measure.dirac (rationalLabel n f, jumpExcursion (rationalLabel n f) f) else 0) s) =
    ∑' n : {n : ℕ | firstLabel n f},
      Measure.dirac (rationalLabel n f, jumpExcursion (rationalLabel n f) f) s
  rw [tsum_subtype {n : ℕ | firstLabel n f}
    (fun n => Measure.dirac (rationalLabel n f, jumpExcursion (rationalLabel n f) f) s)]
  apply tsum_congr
  intro n
  by_cases hn : firstLabel n f <;> simp [hn]

private theorem ae_rationalLabel_covers {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      ∀ x ∈ passageJumpSet f, ∃ n, rationalLabel n f = x := by
  filter_upwards [ae_localTime_passageTime hθ] with f hL
  intro x hx
  obtain ⟨q, hqg, hqd⟩ := exists_rat_btwn
    (show (passageTimeMinus x f : ℝ) < passageTime x f by exact_mod_cast hx.2)
  have hq0 : 0 ≤ q := by
    exact_mod_cast (show (0 : ℝ) ≤ q from (passageTimeMinus x f).coe_nonneg.trans hqg.le)
  let r : ℚ≥0 := ⟨q, hq0⟩
  obtain ⟨n, hn⟩ := rationalTimes_surjective r
  refine ⟨n, ?_⟩
  have hgt : passageTimeMinus x f ≤ (r : ℝ≥0) := by exact_mod_cast hqg.le
  have htd : (r : ℝ≥0) ≤ passageTime x f := by exact_mod_cast hqd.le
  have hg := (hL x).2
  have hd := (hL x).1
  have hlo := runningInfLoc_antitone f htd
  have hup := runningInfLoc_antitone f hgt
  have heq : localTime f (r : ℝ≥0) = (x : ℝ) := by
    dsimp [localTime] at hg hd ⊢
    linarith
  simp only [rationalLabel, hn, localTimeNN, heq, Real.toNNReal_coe]

/-- **Random-measure measurability**: the map `f ↦ excursionPointMeasure f` is `AEMeasurable`
(into `Measure (ℝ≥0 × Excursion)` with its Giry/evaluation `σ`-algebra). -/
theorem aemeasurable_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    AEMeasurable excursionPointMeasure (stableLocalLaw θ : Measure DLoc) := by
  apply measurable_enumeratedPointMeasure.aemeasurable.congr
  filter_upwards [ae_passageJumpSet_countable hθ, ae_rationalLabel_covers hθ] with f hf hc
  exact enumeratedPointMeasure_eq hf hc

/-- **Measurable modification** (the `measurable` field of `IsTimeSimpleLevy`): there is a
measurable map `ξ : DLoc → Measure (ℝ≥0 × Excursion)` a.s. equal to `excursionPointMeasure`. -/
theorem exists_measurable_modification_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) :
    ∃ ξ : DLoc → Measure (ℝ≥0 × Excursion), Measurable ξ ∧
      ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure := by
  exact ⟨_, (aemeasurable_excursionPointMeasure hθ).measurable_mk,
    (aemeasurable_excursionPointMeasure hθ).ae_eq_mk.symm⟩

/-- **Box counts are AE-measurable** (all measurable boxes/sets). -/
theorem aemeasurable_excursionPointMeasure_apply {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {s : Set (ℝ≥0 × Excursion)} (hs : MeasurableSet s) :
    AEMeasurable (fun f => excursionPointMeasure f s) (stableLocalLaw θ : Measure DLoc) := by
  exact (Measure.measurable_coe hs).comp_aemeasurable (aemeasurable_excursionPointMeasure hθ)

private noncomputable def stoppedLocalPath (τ : DLoc → ℝ≥0∞) (f : DLoc) : DLoc :=
  if τ f = ⊤ then f else stopLoc (τ f).toNNReal f

private theorem stoppedLocalPath_eval (τ : DLoc → ℝ≥0∞) (f : DLoc) (t : ℝ≥0) :
    (stoppedLocalPath τ f).1 t = f.1 (min (τ f) (t : ℝ≥0∞)).toNNReal := by
  classical
  by_cases hf : τ f = ⊤
  · rw [stoppedLocalPath, ite_eq_left hf]
    apply congrArg f.1
    rw [hf]
    exact (congrArg ENNReal.toNNReal
      (min_eq_right (show (t : ℝ≥0∞) ≤ ⊤ from le_top))).symm
  · obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hf
    rw [stoppedLocalPath, ite_eq_right hf]
    change f.1 (min t (τ f).toNNReal) = _
    apply congrArg f.1
    rw [← hr]
    change min t r = _
    by_cases hrt : r ≤ t
    · have hco : (r : ℝ≥0∞) ≤ (t : ℝ≥0∞) := by exact_mod_cast hrt
      rw [min_eq_right hrt]
      exact (congrArg ENNReal.toNNReal (min_eq_left hco)).symm
    · have htr := (not_le.mp hrt).le
      have hco : (t : ℝ≥0∞) ≤ (r : ℝ≥0∞) := by exact_mod_cast htr
      rw [min_eq_left htr]
      exact (congrArg ENNReal.toNNReal (min_eq_right hco)).symm

private theorem measurable_stoppedLocalPath {τ : DLoc → ℝ≥0∞}
    (hτ : IsStoppingTime DLoc.filtration τ) :
    Measurable[hτ.measurableSpace] (stoppedLocalPath τ) := by
  rw [measurable_iff_comap_le]
  change (⨆ t : ℝ≥0, MeasurableSpace.comap (DLoc.eval t) inferInstance).comap
    (stoppedLocalPath τ) ≤ _
  rw [MeasurableSpace.comap_iSup, iSup_le_iff]
  intro t
  rw [MeasurableSpace.comap_comp]
  have hm := DLoc.measurable_eval_toNNReal_stopped (hτ.min_const t)
    (fun f => lt_of_le_of_lt (min_le_right _ _) ENNReal.coe_lt_top)
  have hm' := hm.mono ((hτ.min_const t).measurableSpace_mono hτ
    (fun _ => min_le_left _ _)) le_rfl
  have heq : (fun f => (stoppedLocalPath τ f).1 t) =
      (fun f => DLoc.eval (min (τ f) (t : ℝ≥0∞)).toNNReal f) := by
    funext f
    exact stoppedLocalPath_eval τ f t
  exact (heq ▸ hm').comap_le

private theorem firstPassageBelow_stopLoc_of_lt {f : DLoc} {s x : ℝ≥0}
    (hfs : f.1 s < -(x : ℝ)) :
    firstPassageBelow x (stopLoc s f) = firstPassageBelow x f := by
  have hstop : firstPassageBelow x (stopLoc s f) ≤ (s : WithTop ℝ≥0) :=
    firstPassageBelow_le_of_eval_lt (by simpa only [stopLoc, min_self] using hfs)
  apply le_antisymm
  · change firstPassageBelow x (stopLoc s f) ≤ ⨅ (t : ℝ≥0) (_ : f.1 t < -(x : ℝ)),
      (t : WithTop ℝ≥0)
    apply le_iInf
    intro t
    apply le_iInf
    intro ht
    by_cases hts : t ≤ s
    · apply firstPassageBelow_le_of_eval_lt
      change f.1 (min t s) < -(x : ℝ)
      rwa [min_eq_left hts]
    · exact hstop.trans (by exact_mod_cast (le_of_not_ge hts))
  · change firstPassageBelow x f ≤ ⨅ (t : ℝ≥0)
      (_ : (stopLoc s f).1 t < -(x : ℝ)), (t : WithTop ℝ≥0)
    apply le_iInf
    intro t
    apply le_iInf
    intro ht
    have h' : firstPassageBelow x f ≤ (min t s : WithTop ℝ≥0) :=
      firstPassageBelow_le_of_eval_lt ht
    exact h'.trans (by exact_mod_cast min_le_left t s)

private theorem firstPassageBelow_stopLoc_eq_top {f : DLoc} {s a x : ℝ≥0} (hax : a ≤ x)
    (hb : ∀ t ≤ s, -(a : ℝ) ≤ f.1 t) :
    firstPassageBelow x (stopLoc s f) = ⊤ := by
  have hn (t : ℝ≥0) : ¬ (stopLoc s f).1 t < -(x : ℝ) := by
    apply not_lt.mpr
    change -(x : ℝ) ≤ f.1 (min t s)
    exact (neg_le_neg (show (a : ℝ) ≤ x from by exact_mod_cast hax)).trans
      (hb _ (min_le_right _ _))
  simp only [firstPassageBelow, DLoc.strictPassageBelow, hn, iInf_of_empty, iInf_const]

private theorem runningInfLoc_stopLoc {f : DLoc} {s t : ℝ≥0} (ht : t ≤ s) :
    runningInfLoc (stopLoc s f) t = runningInfLoc f t := by
  unfold runningInfLoc
  apply iInf_congr
  intro u
  change f.1 (min u s) = f.1 u
  exact congrArg f.1 (min_eq_left (u.2.trans ht))

private theorem excursionCut_stopLoc {f : DLoc} {s g d : ℝ≥0} (hd : d ≤ s)
    (hc : cutValid g d f) : excursionCut g d (stopLoc s f) = excursionCut g d f := by
  have hg : g ≤ s := hc.1.le.trans hd
  have hc' : cutValid g d (stopLoc s f) := by
    refine ⟨hc.1, ?_, ?_⟩
    · change f.1 (min d s) = f.1 (min g s)
      simpa only [min_eq_left hd, min_eq_left hg] using hc.2.1
    · intro t hgt htd
      change f.1 (min g s) ≤ f.1 (min t s)
      simpa only [min_eq_left hg, min_eq_left (htd.trans hd)] using hc.2.2 t hgt htd
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    funext t
    change (excursionCut g d (stopLoc s f)).path.1 t = (excursionCut g d f).path.1 t
    rw [excursionCut_eval hc', excursionCut_eval hc]
    change f.1 (min (min (g + t) d) s) - f.1 (min g s) = _
    rw [min_eq_left ((min_le_right _ _).trans hd), min_eq_left hg]
  · apply Subtype.ext
    exact (excursionCut_lifetime hc').trans (excursionCut_lifetime hc).symm

private theorem ae_not_passageJumpSet {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), a ∉ passageJumpSet f := by
  filter_upwards [ae_continuousAt_jumpStart hθ, ae_firstHitBelow_eq_firstPassageBelow hθ a,
    ae_passageTime_eq_firstPassageBelow hθ] with f hstart hhit hT
  intro ha
  have hle : firstHitBelow a f ≤ (passageTimeMinus a f : WithTop ℝ≥0) :=
    sInf_le ⟨passageTimeMinus a f, rfl, (hstart a ha).2.1.le⟩
  rw [hhit, hT.1 a] at hle
  have hle' : passageTime a f ≤ passageTimeMinus a f := by exact_mod_cast hle
  exact ha.2.not_ge hle'

private theorem stopped_passage_data {f : DLoc} {a : ℝ≥0}
    (hT : ∀ x, firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0))
    (hc : ∀ x, f.1 (passageTime x f) = -(x : ℝ)) :
    (∀ x < a, passageTime x (stopLoc (passageTime a f) f) = passageTime x f ∧
      passageTimeMinus x (stopLoc (passageTime a f) f) = passageTimeMinus x f) ∧
    passageJumpSet (stopLoc (passageTime a f) f) = passageJumpSet f ∩ Iio a := by
  let g := stopLoc (passageTime a f) f
  have hb (t : ℝ≥0) (ht : t ≤ passageTime a f) : -(a : ℝ) ≤ f.1 t := by
    rcases ht.eq_or_lt with h | h
    · rw [h, hc a]
    · apply le_eval_of_lt_strictPassageBelow
      change (t : WithTop ℝ≥0) < firstPassageBelow a f
      rw [hT a]
      exact_mod_cast h
  have hpass (x : ℝ≥0) (hx : x < a) : firstPassageBelow x g = firstPassageBelow x f :=
    firstPassageBelow_stopLoc_of_lt (by rw [hc a]; exact neg_lt_neg (by exact_mod_cast hx))
  have hdata (x : ℝ≥0) (hx : x < a) : passageTime x g = passageTime x f ∧
      passageTimeMinus x g = passageTimeMinus x f := by
    constructor
    · unfold passageTime
      rw [hpass x hx]
    · unfold passageTimeMinus
      congr 1
      apply iSup_congr
      intro y
      exact hpass y (y.2.trans hx)
  refine ⟨hdata, ?_⟩
  ext x
  change (x ∈ passageJumpSet g) ↔ (x ∈ passageJumpSet f ∧ x < a)
  constructor
  · intro hx
    have hxa : x < a := by
      by_contra hn
      have htop := firstPassageBelow_stopLoc_eq_top (le_of_not_gt hn) hb
      have hzero : passageTime x g = 0 := by
        unfold passageTime
        rw [htop]
        rfl
      change 0 < x ∧ passageTimeMinus x g < passageTime x g at hx
      rw [hzero] at hx
      exact (not_lt_of_ge (show 0 ≤ passageTimeMinus x g from bot_le)) hx.2
    refine ⟨?_, hxa⟩
    change 0 < x ∧ passageTimeMinus x g < passageTime x g at hx
    change 0 < x ∧ passageTimeMinus x f < passageTime x f
    rwa [(hdata x hxa).1, (hdata x hxa).2] at hx
  · rintro ⟨hx, hxa⟩
    change 0 < x ∧ passageTimeMinus x g < passageTime x g
    rw [(hdata x hxa).1, (hdata x hxa).2]
    exact hx

private theorem ae_enumerated_stopped_restrict {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      (enumeratedPointMeasure (stoppedLocalPath (firstPassageBelow a) f)).restrict
        (Iio a ×ˢ univ) = (excursionPointMeasure f).restrict (Iio a ×ˢ univ) := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ, ae_creeping_passageTime hθ,
    ae_passageJumpSet_countable hθ, ae_localTime_passageTime hθ, ae_jumpExcursion_spec hθ]
    with f hT hc hcount hL hspec
  classical
  have hst : stoppedLocalPath (firstPassageBelow a) f = stopLoc (passageTime a f) f := by
    change (if firstPassageBelow a f = ⊤ then f else
      stopLoc (ENNReal.toNNReal (firstPassageBelow a f)) f) = _
    rw [ite_eq_right (by rw [hT.1 a]; exact WithTop.coe_ne_top)]
    apply congrArg (fun t => stopLoc t f)
    rw [hT.1 a]
    rfl
  rw [hst]
  let g := stopLoc (passageTime a f) f
  obtain ⟨hdata, hJ⟩ := stopped_passage_data hT.1 hc (a := a)
  have hcountg : (passageJumpSet g).Countable := by
    rw [hJ]
    exact hcount.mono inter_subset_left
  have hmono : Monotone (fun x => passageTime x f) :=
    (strictMono_passageTime_of_creeping hT.1 hc).monotone
  have hcover : ∀ x ∈ passageJumpSet g, ∃ n, rationalLabel n g = x := by
    intro x hx
    have hx' : x ∈ passageJumpSet f ∩ Iio a := by
      rw [← hJ]
      exact hx
    obtain ⟨q, hqg, hqd⟩ := exists_rat_btwn
      (show (passageTimeMinus x f : ℝ) < passageTime x f by exact_mod_cast hx'.1.2)
    have hq0 : 0 ≤ q := by
      exact_mod_cast (passageTimeMinus x f).coe_nonneg.trans hqg.le
    let r : ℚ≥0 := ⟨q, hq0⟩
    obtain ⟨n, hn⟩ := rationalTimes_surjective r
    have hrg : passageTimeMinus x f ≤ (r : ℝ≥0) := by exact_mod_cast hqg.le
    have hrd : (r : ℝ≥0) ≤ passageTime x f := by exact_mod_cast hqd.le
    have hLr : localTime f (r : ℝ≥0) = (x : ℝ) := by
      have hg := (hL x).2
      have hd := (hL x).1
      have hlo := runningInfLoc_antitone f hrd
      have hup := runningInfLoc_antitone f hrg
      dsimp [localTime] at hg hd ⊢
      linarith
    refine ⟨n, ?_⟩
    change localTimeNN g (rationalTimes n) = x
    rw [hn]
    unfold localTimeNN localTime
    rw [runningInfLoc_stopLoc (hrd.trans (hmono hx'.2.le))]
    change (localTime f (r : ℝ≥0)).toNNReal = x
    rw [hLr, Real.toNNReal_coe]
  rw [enumeratedPointMeasure_eq hcountg hcover]
  have hmark (x : ℝ≥0) (hx : x ∈ passageJumpSet g) :
      jumpExcursion x g = jumpExcursion x f := by
    have hx' : x ∈ passageJumpSet f ∩ Iio a := by
      rw [← hJ]
      exact hx
    unfold jumpExcursion
    rw [(hdata x hx'.2).1, (hdata x hx'.2).2]
    exact excursionCut_stopLoc (hmono hx'.2.le) (hspec x hx'.1).1
  ext s hs
  rw [Measure.restrict_apply' (measurableSet_Iio.prod MeasurableSet.univ),
    Measure.restrict_apply' (measurableSet_Iio.prod MeasurableSet.univ),
    excursionPointMeasure_apply hcountg (hs.inter
      (measurableSet_Iio.prod MeasurableSet.univ)),
    excursionPointMeasure_apply hcount (hs.inter
      (measurableSet_Iio.prod MeasurableSet.univ))]
  congr 1
  congr 1
  ext x
  constructor
  · rintro ⟨hx, hxs⟩
    have hx' : x ∈ passageJumpSet f ∩ Iio a := by
      rw [← hJ]
      exact hx
    exact ⟨hx'.1, by simpa only [hmark x hx] using hxs⟩
  · rintro ⟨hx, hxs⟩
    have hxa : x < a := hxs.2.1
    have hxg : x ∈ passageJumpSet g := by
      rw [hJ]
      exact ⟨hx, hxa⟩
    exact ⟨hxg, by simpa only [hmark x hxg] using hxs⟩

/-- **Past labels are `F_{T_a}`-measurable** (up to a null set): the restriction of `μ` to labels
`≤ a` agrees a.s. with an `F_{T_a}`-measurable random measure
(all those excursions end by `T_a`). -/
theorem exists_stopped_measurable_restrict_Iic {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    ∃ G : DLoc → Measure (ℝ≥0 × Excursion),
      Measurable[(isStoppingTime_firstPassageBelow a).measurableSpace] G ∧
        (fun f => (excursionPointMeasure f).restrict (Iic a ×ˢ univ)) =ᵐ[
          (stableLocalLaw θ : Measure DLoc)] G := by
  let G := fun f => (enumeratedPointMeasure (stoppedLocalPath (firstPassageBelow a) f)).restrict
    (Iio a ×ˢ univ)
  refine ⟨G, ?_, ?_⟩
  · have henum : Measurable[(isStoppingTime_firstPassageBelow a).measurableSpace]
        (fun f => enumeratedPointMeasure (stoppedLocalPath (firstPassageBelow a) f)) :=
      measurable_enumeratedPointMeasure.comp
        (measurable_stoppedLocalPath (isStoppingTime_firstPassageBelow a))
    apply Measure.measurable_of_measurable_coe
    intro s hs
    change Measurable[(isStoppingTime_firstPassageBelow a).measurableSpace]
      (fun f => (enumeratedPointMeasure (stoppedLocalPath (firstPassageBelow a) f)).restrict
        (Iio a ×ˢ univ) s)
    simp only [Measure.restrict_apply' (measurableSet_Iio.prod MeasurableSet.univ)]
    exact (Measure.measurable_coe (hs.inter
      (measurableSet_Iio.prod MeasurableSet.univ))).comp henum
  · filter_upwards [ae_enumerated_stopped_restrict hθ a, ae_not_passageJumpSet hθ a,
      ae_passageJumpSet_countable hθ] with f hstop hno hc
    rw [show G f = (excursionPointMeasure f).restrict (Iio a ×ˢ univ) from hstop]
    ext s hs
    rw [Measure.restrict_apply' (measurableSet_Iic.prod MeasurableSet.univ),
      Measure.restrict_apply' (measurableSet_Iio.prod MeasurableSet.univ),
      excursionPointMeasure_apply hc (hs.inter
        (measurableSet_Iic.prod MeasurableSet.univ)),
      excursionPointMeasure_apply hc (hs.inter
        (measurableSet_Iio.prod MeasurableSet.univ))]
    congr 1
    congr 1
    ext x
    simp only [mem_ofPred_eq, mem_inter_iff, mem_prod, mem_Iic, mem_Iio, mem_univ, and_true]
    constructor
    · rintro ⟨hx, hxs, hxa⟩
      refine ⟨hx, hxs, lt_of_le_of_ne hxa ?_⟩
      intro heq
      exact hno (heq ▸ hx)
    · rintro ⟨hx, hxs, hxa⟩
      exact ⟨hx, hxs, hxa.le⟩

end BGW.StableTrees
