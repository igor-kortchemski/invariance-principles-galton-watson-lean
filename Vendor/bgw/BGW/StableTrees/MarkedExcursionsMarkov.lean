/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarkedExcursionsMeasurable
public import BGW.StableTrees.MarkedExcursionsRestart
public import BGW.StableTrees.StableStrongMarkov
public import BGW.StableTrees.MarkedExcursionsLifetime

/-!
# The fresh marked measure at a passage time

Whole-path strong Markov transfers to arbitrary measurable modifications of the marked measure.
Stopped-history measurability gives independent consecutive windows and the time-simple Lévy
adapter with finite long-excursion rates.

(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV, Sections 2–4; K. Itô,
Poisson point processes attached to Markov processes, Proc. Sixth Berkeley Symp. Math. Statist.
Probab. 3 (1972), 225–239.)
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

private theorem ae_finite_passage {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc), firstPassageBelow a f < ⊤ := by
  filter_upwards [ae_passageTime_eq_firstPassageBelow hθ] with f hf
  rw [hf.1 a]
  exact WithTop.coe_lt_top _

private theorem map_shiftAt_passage {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.shiftAt (firstPassageBelow a)) =
      (stableLocalLaw θ : Measure DLoc) := by
  have hfin : ∀ᵐ f ∂(stableLocalLaw θ : Measure DLoc),
      f ∈ {g : DLoc | (firstPassageBelow a g : ℝ≥0∞) < ⊤} := by
    filter_upwards [ae_finite_passage hθ a] with f hf
    exact hf
  have h := map_shiftAt_restrict_stableLocalLaw hθ (isStoppingTime_firstPassageBelow a)
  have hre : (stableLocalLaw θ : Measure DLoc).restrict
      {f | (firstPassageBelow a f : ℝ≥0∞) < ⊤} = (stableLocalLaw θ : Measure DLoc) :=
    Measure.restrict_eq_self_of_ae_mem hfin
  erw [hre] at h
  have hmass : (stableLocalLaw θ : Measure DLoc) {f | firstPassageBelow a f < ⊤} = 1 := by
    calc
      _ = (stableLocalLaw θ : Measure DLoc) univ := by
        apply measure_congr
        filter_upwards [hfin] with f hf
        simp only [hf, mem_univ]
      _ = 1 := measure_univ
  erw [hmass, one_smul] at h
  exact h

private theorem ae_comp_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)}
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure) :
    (fun f => ξ (DLoc.shiftAt (firstPassageBelow a) f)) =ᵐ[
      (stableLocalLaw θ : Measure DLoc)]
      (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)) := by
  have hmap : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc).map
      (DLoc.shiftAt (firstPassageBelow a))] excursionPointMeasure := by
    rw [map_shiftAt_passage hθ a]
    exact hae
  exact ae_of_ae_map (DLoc.measurable_shiftAt
    (isStoppingTime_firstPassageBelow a)).aemeasurable hmap

/-- **Law of the future point measure**: the post-`T_a` point measure has the same law as the
whole point measure. -/
theorem map_excursionPointMeasure_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)) =
      (stableLocalLaw θ : Measure DLoc).map excursionPointMeasure := by
  obtain ⟨ξ, hξ, hae⟩ := exists_measurable_modification_excursionPointMeasure hθ
  calc
    _ = (stableLocalLaw θ : Measure DLoc).map
        (fun f => ξ (DLoc.shiftAt (firstPassageBelow a) f)) :=
      Measure.map_congr (ae_comp_shiftAt hθ a hae).symm
    _ = ((stableLocalLaw θ : Measure DLoc).map (DLoc.shiftAt (firstPassageBelow a))).map ξ :=
      (Measure.map_map hξ (DLoc.measurable_shiftAt (isStoppingTime_firstPassageBelow a))).symm
    _ = (stableLocalLaw θ : Measure DLoc).map ξ := by rw [map_shiftAt_passage hθ a]
    _ = _ := Measure.map_congr hae

/-- **Independence of the future point measure from `F_{T_a}`** (whole-path strong Markov at `T_a`
plus the shift identity; scalar passage-increment independence is not enough). -/
theorem measure_inter_excursionPointMeasure_shiftAt {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a : ℝ≥0)
    {A : Set DLoc} (hA : MeasurableSet[(isStoppingTime_firstPassageBelow a).measurableSpace] A)
    {B : Set (Measure (ℝ≥0 × Excursion))} (hB : MeasurableSet B) :
    (stableLocalLaw θ : Measure DLoc)
        (A ∩ (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)) ⁻¹' B) =
      (stableLocalLaw θ : Measure DLoc) A *
        (stableLocalLaw θ : Measure DLoc) (excursionPointMeasure ⁻¹' B) := by
  obtain ⟨ξ, hξ, hae⟩ := exists_measurable_modification_excursionPointMeasure hθ
  let A' := A ∩ {f | firstPassageBelow a f < ⊤}
  have hA' : MeasurableSet[(isStoppingTime_firstPassageBelow a).measurableSpace] A' :=
    hA.inter (DLoc.measurableSet_lt_top_stopped (isStoppingTime_firstPassageBelow a))
  have hstrong := measure_inter_preimage_shiftAt hθ (isStoppingTime_firstPassageBelow a)
    hA' (fun _ hf => hf.2) (hξ hB)
  have heq : (stableLocalLaw θ : Measure DLoc)
      (A ∩ (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)) ⁻¹' B) =
      (stableLocalLaw θ : Measure DLoc)
        (A' ∩ DLoc.shiftAt (firstPassageBelow a) ⁻¹' (ξ ⁻¹' B)) := by
    apply measure_congr
    filter_upwards [ae_comp_shiftAt hθ a hae, ae_finite_passage hθ a] with f hf hfin
    simp only [A', mem_inter_iff, mem_preimage, mem_ofPred_eq, hfin, and_true, hf]
  have hPA : (stableLocalLaw θ : Measure DLoc) A' = (stableLocalLaw θ : Measure DLoc) A := by
    apply measure_congr
    filter_upwards [ae_finite_passage hθ a] with f hf
    simp only [A', mem_inter_iff, mem_ofPred_eq, hf, and_true]
  rw [heq, hstrong, hPA]
  congr 1
  apply measure_congr
  filter_upwards [hae] with f hf
  simp only [mem_preimage, hf]

private theorem windowShift_restart (μ : Measure (ℝ≥0 × Excursion)) (a h : ℝ≥0) :
    windowShift a (a + h) μ = windowShift 0 h
      (Measure.map (fun p : ℝ≥0 × Excursion => (p.1 - a, p.2))
        (μ.restrict (Ioi a ×ˢ univ))) := by
  have hm : Measurable (fun p : ℝ≥0 × Excursion => (p.1 - a, p.2)) := by fun_prop
  have hm0 : Measurable (fun p : ℝ≥0 × Excursion => (p.1 - 0, p.2)) := by fun_prop
  ext s hs
  rw [windowShift, windowRestrict, Measure.map_apply hm hs,
    Measure.restrict_apply (hm hs), windowShift, windowRestrict,
    Measure.map_apply hm0 hs, Measure.restrict_apply (hm0 hs),
    Measure.map_apply hm ((hm0 hs).inter (measurableSet_Ioc.prod MeasurableSet.univ)),
    Measure.restrict_apply (hm ((hm0 hs).inter
      (measurableSet_Ioc.prod MeasurableSet.univ)))]
  congr 1
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Ioc, mem_Ioi, mem_univ,
    and_true, tsub_zero, tsub_pos_iff_lt, tsub_le_iff_right, add_comm h a]
  tauto

/-- **Stationarity of window restrictions** (the `stationary` field of `IsTimeSimpleLevy`; for the
AE-measurable `μ`, through `P.map`). -/
theorem map_windowShift_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a h : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map
        (fun f => windowShift a (a + h) (excursionPointMeasure f)) =
      (stableLocalLaw θ : Measure DLoc).map
        (fun f => windowShift 0 h (excursionPointMeasure f))  := by
  have hμ := aemeasurable_excursionPointMeasure hθ
  have hsh := DLoc.measurable_shiftAt (isStoppingTime_firstPassageBelow a)
  have hfresh : AEMeasurable
      (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f))
      (stableLocalLaw θ : Measure DLoc) := by
    have hμ' : AEMeasurable excursionPointMeasure
        ((stableLocalLaw θ : Measure DLoc).map (DLoc.shiftAt (firstPassageBelow a))) := by
      rw [map_shiftAt_passage hθ a]
      exact hμ
    exact hμ'.comp_measurable hsh
  have hw : Measurable (windowShift (M := Excursion) 0 h) :=
    measurable_windowShift measurable_id 0 h
  calc
    _ = (stableLocalLaw θ : Measure DLoc).map (fun f =>
        windowShift 0 h (excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f))) := by
      apply Measure.map_congr
      filter_upwards [ae_excursionPointMeasure_shift hθ] with f hf
      rw [hf a]
      exact windowShift_restart _ a h
    _ = ((stableLocalLaw θ : Measure DLoc).map (fun f =>
        excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f))).map
          (windowShift 0 h) :=
      (hw.aemeasurable.map_map_of_aemeasurable hfresh).symm
    _ = ((stableLocalLaw θ : Measure DLoc).map excursionPointMeasure).map
        (windowShift 0 h) := by rw [map_excursionPointMeasure_shiftAt hθ a]
    _ = _ := hw.aemeasurable.map_map_of_aemeasurable hμ

private theorem unshift_window (μ : Measure (ℝ≥0 × Excursion)) (a b : ℝ≥0) :
    Measure.map (fun p : ℝ≥0 × Excursion => (a + p.1, p.2)) (windowShift a b μ) =
      windowRestrict a b μ := by
  have hp : Measurable (fun p : ℝ≥0 × Excursion => (a + p.1, p.2)) := by fun_prop
  have hm : Measurable (fun p : ℝ≥0 × Excursion => (p.1 - a, p.2)) := by fun_prop
  ext s hs
  simp only [windowShift, windowRestrict]
  rw [Measure.map_apply hp hs, Measure.map_apply hm (hp hs),
    Measure.restrict_apply (hm (hp hs)), Measure.restrict_apply hs]
  congr 1
  ext p
  simp only [mem_inter_iff, mem_preimage, mem_prod, mem_Ioc, mem_univ, and_true]
  constructor
  · rintro ⟨hp, hw⟩
    exact ⟨by simpa only [add_tsub_cancel_of_le hw.1.le, Prod.eta] using hp, hw⟩
  · rintro ⟨hp, hw⟩
    exact ⟨by simpa only [add_tsub_cancel_of_le hw.1.le, Prod.eta] using hp, hw⟩

private noncomputable def futureWindow (a b : ℝ≥0) (ν : Measure (ℝ≥0 × Excursion)) :
    Measure (ℝ≥0 × Excursion) :=
  Measure.map (fun p : ℝ≥0 × Excursion => (a + p.1, p.2)) (windowShift 0 (b - a) ν)

private theorem measurable_futureWindow (a b : ℝ≥0) : Measurable (futureWindow a b) :=
  (Measure.measurable_map _ (by fun_prop)).comp
    (measurable_windowShift measurable_id 0 (b - a))

private theorem ae_futureWindow {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a b : ℝ≥0) (hab : a ≤ b)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)}
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure) :
    (fun f => windowRestrict a b (ξ f)) =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      (fun f => futureWindow a b (excursionPointMeasure
        (DLoc.shiftAt (firstPassageBelow a) f))) := by
  filter_upwards [hae, ae_excursionPointMeasure_shift hθ] with f hf hshift
  rw [hf, futureWindow, hshift a, ← windowShift_restart, add_tsub_cancel_of_le hab]
  exact (unshift_window _ a b).symm

private theorem windowRestrict_restrict_Iic (μ : Measure (ℝ≥0 × Excursion))
    {a b c : ℝ≥0} (hca : c ≤ a) :
    windowRestrict b c (μ.restrict (Iic a ×ˢ univ)) = windowRestrict b c μ := by
  unfold windowRestrict
  rw [Measure.restrict_restrict (measurableSet_Ioc.prod MeasurableSet.univ)]
  congr 1
  apply Set.inter_eq_left.mpr
  intro p hp
  exact ⟨hp.1.2.trans hca, hp.2⟩

/-- **Independence of consecutive window restrictions** (the `indep` field of `IsTimeSimpleLevy`),
for any measurable modification `ξ` of the point measure (so that the `σ`-algebras involved are
honest). -/
theorem iIndepFun_windowRestrict_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    (n : ℕ) (t : Fin (n + 1) → ℝ≥0) (ht : Monotone t) :
    iIndepFun (fun i : Fin n => fun f : DLoc =>
      windowRestrict (t i.castSucc) (t i.succ) (ξ f)) (stableLocalLaw θ : Measure DLoc)  := by
  classical
  induction n with
  | zero => exact iIndepFun.of_subsingleton
  | succ n ih =>
    let P : Measure DLoc := stableLocalLaw θ
    let W := fun (b c : ℝ≥0) (f : DLoc) => windowRestrict b c (ξ f)
    let F := fun (f : DLoc) (i : Fin (n + 1)) => W (t i.castSucc) (t i.succ) f
    have hFm : Measurable F := Measurable.of_eval fun _ =>
      measurable_windowRestrict hξ _ _
    apply (iIndepFun_iff_map_fun_eq_pi_map
      (fun _ => (measurable_windowRestrict hξ _ _).aemeasurable)).mpr
    change P.map F = Measure.pi (fun i => P.map (fun f => F f i))
    refine (Measure.pi_eq fun S hS => ?_).symm
    let a := t (Fin.last n).castSucc
    let b := t (Fin.last n).succ
    have hab : a ≤ b := ht (Fin.castSucc_le_succ _)
    let z : Fin (n + 1) → ℝ≥0 := fun i => t i.castSucc
    have hz : Monotone z := ht.comp Fin.strictMono_castSucc.monotone
    obtain ⟨G, hG, hGeq⟩ := exists_stopped_measurable_restrict_Iic hθ a
    let A : Set DLoc := ⋂ i : Fin n,
      (fun f => windowRestrict (z i.castSucc) (z i.succ) (G f)) ⁻¹' S i.castSucc
    let A₀ : Set DLoc := ⋂ i : Fin n, W (z i.castSucc) (z i.succ) ⁻¹' S i.castSucc
    have hbound (i : Fin n) : z i.succ ≤ a :=
      ht (Fin.castSucc_le_castSucc_iff.mpr (Fin.le_last _))
    have hA : MeasurableSet[(isStoppingTime_firstPassageBelow a).measurableSpace] A := by
      apply MeasurableSet.iInter
      intro i
      have hm : Measurable[(isStoppingTime_firstPassageBelow a).measurableSpace]
          (fun f => windowRestrict (z i.castSucc) (z i.succ) (G f)) :=
        @measurable_windowRestrict DLoc Excursion
          (isStoppingTime_firstPassageBelow a).measurableSpace inferInstance G hG _ _
      exact hm (hS i.castSucc)
    have hAeq : A =ᵐ[P] A₀ := by
      filter_upwards [hGeq, hae] with f hfG hfξ
      apply propext
      simp only [A, A₀, mem_iInter, mem_preimage]
      apply forall_congr'
      intro i
      rw [← hfG, windowRestrict_restrict_Iic _ (hbound i), ← hfξ]
    have hprefix := (ih z hz).map_fun_eq_pi_map
      (fun _ => (measurable_windowRestrict hξ _ _).aemeasurable)
    have hAG := congrArg (fun μ => μ (Set.univ.pi fun i : Fin n => S i.castSucc)) hprefix
    have hZm : Measurable (fun (f : DLoc) (i : Fin n) =>
        windowRestrict (z i.castSucc) (z i.succ) (ξ f)) :=
      Measurable.of_eval fun _ => measurable_windowRestrict hξ _ _
    rw [Measure.map_apply hZm (MeasurableSet.univ_pi
      (fun i : Fin n => hS i.castSucc)), Measure.pi_pi] at hAG
    have hPA : P A = ∏ i : Fin n, P (W (z i.castSucc) (z i.succ) ⁻¹' S i.castSucc) := by
      rw [measure_congr hAeq]
      have hset : (fun f i => windowRestrict (z i.castSucc) (z i.succ) (ξ f)) ⁻¹'
          (Set.univ.pi fun i : Fin n => S i.castSucc) = A₀ := by
        ext f
        simp only [A₀, W, mem_preimage, Set.mem_pi, mem_univ, forall_true_left, mem_iInter]
      rw [hset] at hAG
      simpa only [Measure.map_apply (measurable_windowRestrict hξ _ _) (hS _)] using hAG
    let B := (futureWindow a b) ⁻¹' S (Fin.last n)
    have hB : MeasurableSet B := measurable_futureWindow a b (hS _)
    have hstrong := measure_inter_excursionPointMeasure_shiftAt hθ a hA hB
    have hlast := measure_inter_excursionPointMeasure_shiftAt hθ a
      (A := univ) MeasurableSet.univ hB
    have hfuture := ae_futureWindow hθ a b hab hae
    have hPL : P (W a b ⁻¹' S (Fin.last n)) = P (excursionPointMeasure ⁻¹' B) := by
      calc
        _ = P ((fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)) ⁻¹' B) := by
          apply measure_congr
          filter_upwards [hfuture] with f hf
          exact congrArg (fun ν => ν ∈ S (Fin.last n)) hf
        _ = _ := by simpa only [univ_inter, measure_univ, one_mul] using hlast
    have hfull : F ⁻¹' (univ.pi S) =ᵐ[P]
        A ∩ (fun f => excursionPointMeasure (DLoc.shiftAt (firstPassageBelow a) f)) ⁻¹' B := by
      filter_upwards [hAeq, hfuture] with f hAf hff
      apply propext
      simp only [mem_preimage, Set.mem_pi, mem_univ, forall_true_left]
      rw [Fin.forall_fin_succ']
      change ((∀ i : Fin n, F f i.castSucc ∈ S i.castSucc) ∧
        W a b f ∈ S (Fin.last n)) ↔ _
      have hpast : (∀ i : Fin n, F f i.castSucc ∈ S i.castSucc) ↔ f ∈ A₀ := by
        simp only [A₀, mem_iInter, mem_preimage, F, W, z, Fin.succ_castSucc]
      rw [hpast, ← hAf]
      exact and_congr Iff.rfl (Iff.of_eq (congrArg (fun ν => ν ∈ S (Fin.last n)) hff))
    rw [Measure.map_apply hFm (MeasurableSet.univ_pi hS), measure_congr hfull,
      hstrong, hPA, ← hPL, Fin.prod_univ_castSucc]
    congr 1
    · apply Finset.prod_congr rfl
      intro i _
      rw [Measure.map_apply (measurable_windowRestrict hξ _ _) (hS i.castSucc)]
      rfl
    · rw [Measure.map_apply (measurable_windowRestrict hξ _ _) (hS (Fin.last n))]

/-- **Poisson characterization adapter**: every measurable modification of the excursion point
measure is a time-simple Lévy point measure, and every `{ε < lifetime}` has finite rate. -/
theorem isTimeSimpleLevy_of_ae_eq_excursionPointMeasure {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure) :
    IsTimeSimpleLevy (stableLocalLaw θ : Measure DLoc) ξ ∧
      ∀ ε : ℝ≥0, 0 < ε →
        MeasurableSet {e : Excursion | ε < e.lifetime} ∧
        IsFiniteRate (stableLocalLaw θ : Measure DLoc) ξ {e : Excursion | ε < e.lifetime} := by
    refine ⟨?_, ?_⟩
    · refine ⟨hξ, ?_, ?_, ?_, ?_, ?_⟩
      · filter_upwards [hae] with f hf
        rw [hf]
        exact excursionPointMeasure_atZero f
      · filter_upwards [hae, ae_excursionPointMeasure_counting hθ] with f hf hc
        rwa [hf]
      · filter_upwards [hae, ae_excursionPointMeasure_timeSimple hθ] with f hf hc
        rwa [hf]
      · intro a h
        calc
          _ = (stableLocalLaw θ : Measure DLoc).map
              (fun f => windowShift a (a + h) (excursionPointMeasure f)) :=
            Measure.map_congr (hae.mono fun _ hf => congrArg (windowShift a (a + h)) hf)
          _ = _ := map_windowShift_excursionPointMeasure hθ a h
          _ = (stableLocalLaw θ : Measure DLoc).map (fun f => windowShift 0 h (ξ f)) :=
            Measure.map_congr (hae.mono fun _ hf => (congrArg (windowShift 0 h) hf).symm)
      · exact iIndepFun_windowRestrict_excursionPointMeasure hθ hξ hae
    · intro ε hε
      have hs : MeasurableSet {e : Excursion | ε < e.lifetime} :=
        measurableSet_lt (α := ℝ≥0) measurable_const measurable_excursion_lifetime
      refine ⟨hs, hs, ?_⟩
      intro t
      filter_upwards [hae, ae_finite_excursionCount hθ] with f hf hfinite
      rw [hf]
      by_cases ht : t = 0
      · subst t
        simp only [Ioc_self, empty_prod, measure_empty, ENNReal.zero_lt_top]
      · exact (hfinite t ε (pos_iff_ne_zero.mpr ht) hε).2

end BGW.StableTrees
