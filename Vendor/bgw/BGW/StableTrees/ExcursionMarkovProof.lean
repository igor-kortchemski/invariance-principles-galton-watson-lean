/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMarkovKernel
public import BGW.StableTrees.ExcursionMarkovAge

/-!
# The Markov property of the stable excursion measure

The strong Markov property at strict age crossings gives the identity for each selected
excursion. Exact-once reindexing, compensation and nonnegative summation give the identity
under the excursion measure.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private lemma tsum_eq_of_unique_relation {ι κ : Type*} (R : ι → κ → Prop)
    (hι : ∀ i, ∃! k, R i k) (hκ : ∀ k, ∃! i, R i k)
    (F : ι → ℝ≥0∞) (G : κ → ℝ≥0∞) (hFG : ∀ i k, R i k → F i = G k) :
    (∑' i, F i) = ∑' k, G k := by
  classical
  choose φ hφ using hι
  have hinj : Function.Injective φ := by
    intro i j hij
    exact (hκ (φ i)).unique (hφ i).1 (hij.symm ▸ (hφ j).1)
  have hsurj : Function.Surjective φ := by
    intro k
    obtain ⟨i, hi, _⟩ := hκ k
    exact ⟨i, ((hφ i).2 k hi).symm⟩
  calc
    (∑' i, F i) = ∑' i, G (φ i) := tsum_congr fun i => hFG i (φ i) (hφ i).1
    _ = ∑' k, G k := (Equiv.ofBijective φ ⟨hinj, hsurj⟩).tsum_eq G

private noncomputable def selectedAgeLabel (t : ℝ≥0) (τ : DLoc → WithTop ℝ≥0)
    (f : DLoc) : ℝ≥0 :=
  (-(stopLocAt (τ f) f).1 ((τ f).untopD 0 - t)).toNNReal

private noncomputable def selectedAgeMark (t : ℝ≥0) (τ ρ : DLoc → WithTop ℝ≥0)
    (f : DLoc) : Excursion :=
  excursionCut ((τ f).untopD 0 - t) ((ρ f).untopD 0) f

private noncomputable def prefixValue (t : ℝ≥0) (p : D (t : ℝ) ℝ) : ℝ≥0 :=
  (p ⟨t, t.2, le_rfl⟩).toNNReal

private lemma measurable_prefixValue (t : ℝ≥0) : Measurable (prefixValue t) :=
  (BGW.Skorokhod.measurable_eval _).real_toNNReal

private lemma prefixValue_excursionRestrict (t : ℝ≥0) (e : Excursion) :
    prefixValue t (excursionRestrict t e) = e.valueNN t := rfl

private lemma measurable_selectedAgeLabel (t : ℝ≥0) {τ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) :
    Measurable[hτ.measurableSpace] (selectedAgeLabel t τ) := by
  exact (DLoc.measurable_eval₂.comp ((measurable_stopLocAt_stopped hτ).prodMk
    ((hτ.measurable.untopD 0).sub measurable_const))).neg.real_toNNReal

private lemma measurable_selectedAgeMark (t : ℝ≥0) {τ ρ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) (hρ : IsStoppingTime DLoc.filtration ρ) :
    Measurable (selectedAgeMark t τ ρ) :=
  measurable_excursionCut.comp (((hτ.measurable'.untopD 0).sub measurable_const).prodMk
    ((hρ.measurable'.untopD 0).prodMk measurable_id))

private lemma selectedAgeMark_eq {t g d : ℝ≥0} {τ ρ : DLoc → WithTop ℝ≥0} {f : DLoc}
    (hτ : τ f = ((g + t : ℝ≥0) : WithTop ℝ≥0)) (hρ : ρ f = (d : WithTop ℝ≥0)) :
    selectedAgeMark t τ ρ f = excursionCut g d f := by
  simp only [selectedAgeMark, hτ, hρ, WithTop.untopD_coe, add_tsub_cancel_right]

private lemma selectedAgeLabel_eq {t g x : ℝ≥0} {τ : DLoc → WithTop ℝ≥0} {f : DLoc}
    (hτ : τ f = ((g + t : ℝ≥0) : WithTop ℝ≥0)) (hg : f.1 g = -(x : ℝ)) :
    selectedAgeLabel t τ f = x := by
  simp only [selectedAgeLabel, hτ, WithTop.untopD_coe, add_tsub_cancel_right,
    stopLocAt, stopLoc, min_eq_left (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ t)), hg,
    neg_neg, Real.toNNReal_coe]

private lemma lintegral_mark_window {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {J : Excursion → ℝ≥0∞} (hJ : Measurable J) :
    (∫⁻ f, ∫⁻ p in Ioc 0 1 ×ˢ univ, J p.2 ∂excursionPointMeasure f
      ∂(stableLocalLaw θ : Measure DLoc)) = ∫⁻ e, J e ∂excursionMeasure θ := by
  have h := excursion_compensation_predictable hθ 1
    (H := fun _ _ => 1) (fun _ => measurable_const) (fun _ _ _ => continuousWithinAt_const) hJ
  simpa [lebNN_Ioc] using h

private def AgeMatch (t : ℝ≥0) (f : DLoc)
    (τ ρ : ℕ → DLoc → WithTop ℝ≥0) (n : ℕ) (x : ℝ≥0) : Prop :=
  τ n f = ((passageTimeMinus x f + t : ℝ≥0) : WithTop ℝ≥0) ∧
    ρ n f = (passageTime x f : WithTop ℝ≥0)

private lemma selected_sum_eq_pointMeasure {t : ℝ≥0} {f : DLoc}
    {τ ρ : ℕ → DLoc → WithTop ℝ≥0}
    (hcount : (passageJumpSet f).Countable)
    (hcover : ∀ x ∈ passageJumpSet f, t < (jumpExcursion x f).lifetime →
      ∃! n, AgeMatch t f τ ρ n x)
    (hsel : ∀ n, τ n f < ⊤ → ∃ x ∈ passageJumpSet f,
      t < (jumpExcursion x f).lifetime ∧ AgeMatch t f τ ρ n x)
    (hdisj : ∀ x ∈ passageJumpSet f, ∀ y ∈ passageJumpSet f, x < y →
      passageTime x f < passageTimeMinus y f)
    (hstart : ∀ x ∈ passageJumpSet f, f.1 (passageTimeMinus x f) = -(x : ℝ))
    {J : Excursion → ℝ≥0∞} (hJ : Measurable J) :
    (∑' n : ℕ, if τ n f < ⊤ ∧ selectedAgeLabel t (τ n) f ∈ Ioc 0 1
      then J (selectedAgeMark t (τ n) (ρ n) f) else 0) =
      ∫⁻ p in Ioc 0 1 ×ˢ univ,
        (if t < p.2.lifetime then J p.2 else 0) ∂excursionPointMeasure f := by
  classical
  let N : Set ℕ := {n | τ n f < ⊤}
  let X : Set ℝ≥0 := {x | x ∈ passageJumpSet f ∧ t < (jumpExcursion x f).lifetime}
  let R (n : N) (x : X) := AgeMatch t f τ ρ n x
  have hc : ∀ x : X, ∃! n : N, R n x := by
    intro x
    obtain ⟨n, hn, hnu⟩ := hcover x x.2.1 x.2.2
    have hnfin : τ n f < ⊤ := by rw [hn.1]; exact WithTop.coe_lt_top _
    exact ⟨⟨n, hnfin⟩, hn, fun m hm => Subtype.ext (hnu m hm)⟩
  have hs : ∀ n : N, ∃! x : X, R n x := by
    intro n
    obtain ⟨x, hx, htx, hnx⟩ := hsel n n.2
    refine ⟨⟨x, hx, htx⟩, hnx, ?_⟩
    intro y hny
    apply Subtype.ext
    have hdeq : passageTime y f = passageTime x f :=
      WithTop.coe_injective (hny.2.symm.trans hnx.2)
    rcases lt_trichotomy (y : ℝ≥0) x with hyx | hyx | hxy
    · exact ((hdisj y y.2.1 x hx hyx).trans hx.2).ne hdeq |>.elim
    · exact hyx
    · exact ((hdisj x hx y y.2.1 hxy).trans y.2.1.2).ne hdeq.symm |>.elim
  have hreindex := tsum_eq_of_unique_relation R hs hc
    (fun n : N => if selectedAgeLabel t (τ n) f ∈ Ioc 0 1
      then J (selectedAgeMark t (τ n) (ρ n) f) else 0)
    (fun x : X => if (x : ℝ≥0) ∈ Ioc 0 1 then J (jumpExcursion x f) else 0)
    (fun n x hnx => by
      rw [selectedAgeLabel_eq hnx.1 (hstart x x.2.1), selectedAgeMark_eq hnx.1 hnx.2]
      rfl)
  have hleft : (∑' n : ℕ, if τ n f < ⊤ ∧ selectedAgeLabel t (τ n) f ∈ Ioc 0 1
      then J (selectedAgeMark t (τ n) (ρ n) f) else 0) =
      ∑' n : N, if selectedAgeLabel t (τ n) f ∈ Ioc 0 1
        then J (selectedAgeMark t (τ n) (ρ n) f) else 0 := by
    rw [tsum_subtype N (fun n => if selectedAgeLabel t (τ n) f ∈ Ioc 0 1
      then J (selectedAgeMark t (τ n) (ρ n) f) else 0)]
    apply tsum_congr
    intro n
    by_cases hn : τ n f < ⊤ <;>
      by_cases hl : selectedAgeLabel t (τ n) f ∈ Ioc 0 1 <;>
        simp_all [N]
  rw [hleft, hreindex]
  have hwindow : MeasurableSet (Ioc (0 : ℝ≥0) 1 ×ˢ (univ : Set Excursion)) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hsurv : MeasurableSet {p : ℝ≥0 × Excursion | t < p.2.lifetime} :=
    measurableSet_lt measurable_const (measurable_excursion_lifetime.comp measurable_snd)
  have hfun : Measurable (fun p : ℝ≥0 × Excursion =>
      (Ioc (0 : ℝ≥0) 1 ×ˢ univ).indicator
        (fun p : ℝ≥0 × Excursion => if t < p.2.lifetime then J p.2 else 0) p) :=
    (Measurable.ite hsurv (hJ.comp measurable_snd) measurable_const).indicator hwindow
  rw [← lintegral_indicator hwindow, excursionPointMeasure, ite_eq_left hcount,
    lintegral_sum_measure]
  simp_rw [lintegral_dirac' _ hfun]
  rw [tsum_subtype X (fun x => if x ∈ Ioc 0 1 then J (jumpExcursion x f) else 0),
    tsum_subtype (passageJumpSet f) (fun x =>
      (Ioc (0 : ℝ≥0) 1 ×ˢ univ).indicator
        (fun p : ℝ≥0 × Excursion => if t < p.2.lifetime then J p.2 else 0)
          (x, jumpExcursion x f))]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ passageJumpSet f <;>
    by_cases ht : t < (jumpExcursion x f).lifetime <;>
      by_cases hl : x ∈ Ioc 0 1 <;> simp_all [X]

private noncomputable def selectedSummand (t : ℝ≥0) (τ ρ : DLoc → WithTop ℝ≥0)
    (J : Excursion → ℝ≥0∞) (f : DLoc) : ℝ≥0∞ :=
  if τ f < ⊤ ∧ selectedAgeLabel t τ f ∈ Ioc 0 1 then J (selectedAgeMark t τ ρ f) else 0

private lemma measurable_selectedSummand (t : ℝ≥0) {τ ρ : DLoc → WithTop ℝ≥0}
    (hτ : IsStoppingTime DLoc.filtration τ) (hρ : IsStoppingTime DLoc.filtration ρ)
    {J : Excursion → ℝ≥0∞} (hJ : Measurable J) : Measurable (selectedSummand t τ ρ J) := by
  have hset : MeasurableSet {f : DLoc | τ f < ⊤ ∧ selectedAgeLabel t τ f ∈ Ioc 0 1} := by
    simpa only [Set.ofPred_and, Set.preimage] using
      (measurableSet_lt hτ.measurable' measurable_const).inter
        ((measurable_selectedAgeLabel t hτ).mono hτ.measurableSpace_le le_rfl
          measurableSet_Ioc)
  exact Measurable.ite hset (hJ.comp (measurable_selectedAgeMark t hτ hρ)) measurable_const

private def ExcursionAgeEnumeration (t : ℝ≥0) (τ ρ : ℕ → DLoc → WithTop ℝ≥0)
    (f : DLoc) : Prop :=
  (∀ x ∈ passageJumpSet f, t < (jumpExcursion x f).lifetime →
    ∃! n, AgeMatch t f τ ρ n x) ∧
  (∀ n, τ n f < ⊤ → ∃ x ∈ passageJumpSet f,
    t < (jumpExcursion x f).lifetime ∧ AgeMatch t f τ ρ n x)

private lemma expected_selected_sum {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    {τ ρ : ℕ → DLoc → WithTop ℝ≥0}
    (hEnum : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ExcursionAgeEnumeration t τ ρ f)
    {J : Excursion → ℝ≥0∞} (hJ : Measurable J) :
    (∫⁻ f, ∑' n, selectedSummand t (τ n) (ρ n) J f ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ e in {e : Excursion | t < e.lifetime}, J e ∂excursionMeasure θ := by
  classical
  have hsurv : MeasurableSet {e : Excursion | t < e.lifetime} :=
    measurableSet_lt measurable_const measurable_excursion_lifetime
  have hJsurv : Measurable (fun e : Excursion => if t < e.lifetime then J e else 0) :=
    Measurable.ite hsurv hJ measurable_const
  calc
    _ = ∫⁻ f, ∫⁻ p in Ioc 0 1 ×ˢ univ,
        (if t < p.2.lifetime then J p.2 else 0) ∂excursionPointMeasure f
          ∂(stableLocalLaw θ : Measure DLoc) := by
      apply lintegral_congr_ae
      filter_upwards [hEnum, ae_passageJumpSet_countable hθ, ae_jump_intervals_disjoint hθ,
        ae_continuousAt_jumpStart hθ] with f henum hcount hdisj hstart
      exact selected_sum_eq_pointMeasure hcount henum.1 henum.2 hdisj
        (fun x hx => (hstart x hx).2.1) hJ
    _ = ∫⁻ e, (if t < e.lifetime then J e else 0) ∂excursionMeasure θ :=
      lintegral_mark_window hθ hJsurv
    _ = _ := by
      simpa only [Set.indicator_apply, Set.mem_ofPred_eq] using lintegral_indicator hsurv J

private lemma selected_markov_lintegral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0)
    {τ ρ : ℕ → DLoc → WithTop ℝ≥0}
    (hτ : ∀ n, IsStoppingTime DLoc.filtration (τ n))
    (hEnum : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ExcursionAgeEnumeration t τ ρ f)
    (F : D (t : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F)
    (G : DLoc → ℝ≥0∞) (hG : Measurable G) (n : ℕ) :
    (∫⁻ f, selectedSummand t (τ n) (ρ n)
        (fun e => F (excursionRestrict t e) * G (futureFrom t e)) f
          ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ f, selectedSummand t (τ n) (ρ n)
        (fun e => F (excursionRestrict t e) *
          (∫⁻ g, G g ∂killedStableKernel θ (e.valueNN t))) f
            ∂(stableLocalLaw θ : Measure DLoc) := by
  classical
  let A : Set DLoc := {f | τ n f < ⊤ ∧ selectedAgeLabel t (τ n) f ∈ Ioc 0 1}
  have hA : MeasurableSet[(hτ n).measurableSpace] A := by
    simpa only [A, Set.ofPred_and, Set.preimage, Set.mem_Iio] using
      ((hτ n).measurable measurableSet_Iio).inter
        (measurable_selectedAgeLabel t (hτ n) measurableSet_Ioc)
  have hA0 := (hτ n).measurableSpace_le A hA
  have hprefix : ∀ᵐ f ∂((stableLocalLaw θ : Measure DLoc).restrict A),
      selectedAgePrefix t (τ n) f =
        excursionRestrict t (selectedAgeMark t (τ n) (ρ n) f) ∧
      futureFrom t (selectedAgeMark t (τ n) (ρ n) f) =
        killedPath (prefixValue t (selectedAgePrefix t (τ n) f)) (DLoc.shiftAt (τ n) f) := by
    apply (ae_restrict_iff' hA0).2
    filter_upwards [hEnum, ae_jumpExcursion_spec hθ, ae_continuousAt_jumpStart hθ,
      ae_passageTime_eq_firstPassageBelow hθ] with f henum he hs hP hfA
    obtain ⟨x, hx, htx, hnx, hρx⟩ := henum.2 n hfA.1
    have hxd : passageTimeMinus x f + t < passageTime x f := by
      rw [← lt_tsub_iff_left, ← (he x hx).2.1]
      exact htx
    have hm := selectedAgeMark_eq hnx hρx
    have hp := selectedAgePrefix_eq_excursionRestrict hnx (he x hx).1 hxd
    refine ⟨by rw [hm]; exact hp, ?_⟩
    rw [hm, hp, prefixValue_excursionRestrict,
      futureFrom_excursionCut_eq_killedPath (he x hx).1 (hP.1 x) (hs x hx).2.1 hxd]
    congr 1
    change DLoc.shift (passageTimeMinus x f + t) f =
      DLoc.shift (ENNReal.toNNReal (τ n f)) f
    rw [hnx]
    rfl
  have hH : Measurable (fun p : D (t : ℝ) ℝ × DLoc =>
      F p.1 * G (killedPath (prefixValue t p.1) p.2)) :=
    (hF.comp measurable_fst).mul (hG.comp (measurable_killedPath_uncurry.comp
      (((measurable_prefixValue t).comp measurable_fst).prodMk measurable_snd)))
  have hSM := lintegral_past_shiftAt hθ (hτ n) hA (fun _ hf => hf.1)
    (measurable_selectedAgePrefix t (hτ n)) hH
  have hleft : (∫⁻ f in A,
      F (excursionRestrict t (selectedAgeMark t (τ n) (ρ n) f)) *
        G (futureFrom t (selectedAgeMark t (τ n) (ρ n) f))
          ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ f in A, F (selectedAgePrefix t (τ n) f) *
        G (killedPath (prefixValue t (selectedAgePrefix t (τ n) f))
          (DLoc.shiftAt (τ n) f)) ∂(stableLocalLaw θ : Measure DLoc) := by
    apply lintegral_congr_ae
    filter_upwards [hprefix] with f hf
    rw [hf.2, hf.1]
  have hkm (y : ℝ≥0) : Measurable (killedPath y) :=
    measurable_killedPath_uncurry.comp (measurable_const.prodMk measurable_id)
  have hright : (∫⁻ f in A, ∫⁻ g, F (selectedAgePrefix t (τ n) f) *
      G (killedPath (prefixValue t (selectedAgePrefix t (τ n) f)) g)
        ∂(stableLocalLaw θ : Measure DLoc) ∂(stableLocalLaw θ : Measure DLoc)) =
      ∫⁻ f in A, F (excursionRestrict t (selectedAgeMark t (τ n) (ρ n) f)) *
        (∫⁻ g, G g ∂killedStableKernel θ ((selectedAgeMark t (τ n) (ρ n) f).valueNN t))
          ∂(stableLocalLaw θ : Measure DLoc) := by
    apply lintegral_congr_ae
    filter_upwards [hprefix] with f hf
    rw [lintegral_const_mul (f := fun g : DLoc =>
      G (killedPath (prefixValue t (selectedAgePrefix t (τ n) f)) g)) _
      (hG.comp (measurable_killedPath_uncurry.comp (measurable_const.prodMk measurable_id))),
      hf.1, prefixValue_excursionRestrict,
      killedStableKernel_apply, lintegral_map hG (hkm _)]
  have hsummand (J : Excursion → ℝ≥0∞) : selectedSummand t (τ n) (ρ n) J =
      A.indicator (fun f => J (selectedAgeMark t (τ n) (ρ n) f)) := by
    funext f
    simp only [selectedSummand, Set.indicator_apply, A, Set.mem_ofPred_eq]
  rw [hsummand, hsummand, lintegral_indicator hA0, lintegral_indicator hA0,
    hleft, hSM, hright]

/-- **Excursion Markov property**.  For nonnegative
measurable `F` on the prefix path space `D t ℝ` (through `excursionRestrict t`) and `G` on the
whole future (through the uncentred `futureFrom t`):
`N[1_{ζ>t} F(r_t e) G(e(t+·))] = N[1_{ζ>t} F(r_t e) (K_{e(t)} G)]`. -/
theorem excursion_markov_lintegral {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (t : ℝ≥0) (ht : 0 < t)
    (F : D (t : ℝ) ℝ → ℝ≥0∞) (hF : Measurable F) (G : DLoc → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ e in {e : Excursion | t < e.lifetime},
        F (excursionRestrict t e) * G (futureFrom t e) ∂(excursionMeasure θ)) =
      ∫⁻ e in {e : Excursion | t < e.lifetime},
        F (excursionRestrict t e) *
          (∫⁻ f, G f ∂(killedStableKernel θ (e.valueNN t))) ∂(excursionMeasure θ) := by
  classical
  let _ := isMarkovKernel_killedStableKernel θ
  obtain ⟨τ, ρ, hτ, hρ, henumerate⟩ := exists_excursionAge_stoppingTimes hθ t ht
  have hEnum : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), ExcursionAgeEnumeration t τ ρ f :=
    henumerate.mono fun _ hf => ⟨hf.1, hf.2.1⟩
  let JL : Excursion → ℝ≥0∞ := fun e =>
    F (excursionRestrict t e) * G (futureFrom t e)
  let JR : Excursion → ℝ≥0∞ := fun e =>
    F (excursionRestrict t e) * (∫⁻ g, G g ∂killedStableKernel θ (e.valueNN t))
  have hJL : Measurable JL :=
    (hF.comp (measurable_excursionRestrict t)).mul (hG.comp (measurable_futureFrom t))
  have hJR : Measurable JR :=
    (hF.comp (measurable_excursionRestrict t)).mul
      (hG.lintegral_kernel.comp (measurable_excursion_valueNN t))
  calc
    _ = ∫⁻ f, ∑' n, selectedSummand t (τ n) (ρ n) JL f
        ∂(stableLocalLaw θ : Measure DLoc) := (expected_selected_sum hθ t hEnum hJL).symm
    _ = ∑' n, ∫⁻ f, selectedSummand t (τ n) (ρ n) JL f
        ∂(stableLocalLaw θ : Measure DLoc) :=
      lintegral_tsum fun n => (measurable_selectedSummand t (hτ n) (hρ n) hJL).aemeasurable
    _ = ∑' n, ∫⁻ f, selectedSummand t (τ n) (ρ n) JR f
        ∂(stableLocalLaw θ : Measure DLoc) :=
      tsum_congr fun n => selected_markov_lintegral hθ t hτ hEnum F hF G hG n
    _ = ∫⁻ f, ∑' n, selectedSummand t (τ n) (ρ n) JR f
        ∂(stableLocalLaw θ : Measure DLoc) :=
      (lintegral_tsum fun n =>
        (measurable_selectedSummand t (hτ n) (hρ n) hJR).aemeasurable).symm
    _ = _ := expected_selected_sum hθ t hEnum hJR

end BGW.StableTrees
