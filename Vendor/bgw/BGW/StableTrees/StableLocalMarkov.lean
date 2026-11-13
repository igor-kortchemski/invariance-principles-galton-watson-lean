/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLoc
public import BGW.Skorokhod.ShiftIncrement
public import BGW.StableTrees.StableLocalLaw
public import BGW.StableTrees.StableProcessMarkov
public import BGW.StableTrees.StableLaw

import BGW.Skorokhod.MeasurableLaws
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosedProd
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Martingale.Basic

/-!
# Markov property of the stable process on local càdlàg paths

This module establishes the simple Markov property of the local stable process for its natural
right-continuous filtration, together with its integral and conditional-expectation forms, the
germ zero-one law, and the exponential martingale
(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter I, Proposition 6 and
Chapter VIII; R. M. Blumenthal, An extended Markov property, Trans. Amer. Math. Soc. 85 (1957),
for the zero-one law).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal
open BGW.Skorokhod

namespace BGW.Skorokhod.DLoc

/-- The centered shift by a fixed time is measurable (restriction of `measurable_shift`). -/
theorem measurable_shift_fixed (s : ℝ≥0) : Measurable (DLoc.shift s) := by
  exact measurable_shift.comp (measurable_const.prodMk measurable_id)

/-- Evaluation of the shift: `eval u (shift s f) = eval (s + u) f - eval s f`. -/
theorem eval_shift (s u : ℝ≥0) (f : DLoc) :
    DLoc.eval u (DLoc.shift s f) = DLoc.eval (s + u) f - DLoc.eval s f := by
  rfl

end BGW.Skorokhod.DLoc

namespace BGW.StableTrees

/-- The raw past is precisely the σ-algebra of the restriction to the same horizon. -/
private theorem rawFiltration_eq_comap_restrict (s : ℝ≥0) :
    DLoc.rawFiltration s =
      MeasurableSpace.comap (DLoc.restrict s) (inferInstance : MeasurableSpace (D (s : ℝ) ℝ)) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    apply iSup_le
    intro hts
    let t' : Set.Icc (0 : ℝ) (s : ℝ) := ⟨t, t.2, by exact_mod_cast hts⟩
    have heq : DLoc.eval t = (fun g : D (s : ℝ) ℝ => g t') ∘ DLoc.restrict s := by
      rfl
    rw [heq, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (BGW.Skorokhod.measurable_eval t').comap_le
  · change _ ≤ ⨆ t ≤ s, MeasurableSpace.comap (DLoc.eval t) inferInstance
    rw [BGW.Skorokhod.measurableSpace_eq_iSup_comap_eval
      (T := (s : ℝ)) (E := ℝ) (S := Set.univ) dense_univ s.2 (by simp)]
    simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp,
      Function.comp_def, Set.mem_univ, iSup_true, iSup_le_iff]
    intro t
    let u : ℝ≥0 := ⟨t, t.2.1⟩
    have hus : u ≤ s := by exact_mod_cast t.2.2
    exact le_iSup_of_le u (le_iSup_of_le hus le_rfl)

/-- Transport a compact path along an equality of horizons. -/
private def castD {a b : ℝ} (h : a = b) (f : D a ℝ) : D b ℝ := h ▸ f

/-- The transported restriction map is measurable. -/
private theorem measurable_castD {a b : ℝ} (h : a = b) :
    Measurable (fun f : D a ℝ => castD h f) := by
  cases h
  exact measurable_id

/-- Evaluation after transport to an equal horizon. -/
private theorem castD_apply {a b : ℝ} (h : a = b) (f : D a ℝ) (t : Set.Icc (0 : ℝ) b) :
    castD h f t = f ⟨t, t.2.1, by simpa [h] using t.2.2⟩ := by
  cases h
  rfl

/-- The future segment, with its compact horizon written as `U`. -/
private noncomputable def compactFuture (s U : ℝ≥0) (f : D ((s + U : ℝ≥0) : ℝ) ℝ) : D (U : ℝ) ℝ :=
  castD (show ((s + U : ℝ≥0) : ℝ) - (s : ℝ) = (U : ℝ) by simp)
    (shiftIncrement (T := ((s + U : ℝ≥0) : ℝ)) (s := (s : ℝ)) s.2
      (by simp : (s : ℝ) ≤ ((s + U : ℝ≥0) : ℝ)) f)

/-- The compact future map is measurable. -/
private theorem measurable_compactFuture (s U : ℝ≥0) : Measurable (compactFuture s U) := by
  exact (measurable_castD _).comp (measurable_shiftIncrement _ _)

/-- Mapping a measure through horizon transport transports the measure. -/
private theorem map_castD {a b : ℝ} (h : a = b) (μ : Measure (D a ℝ)) :
    μ.map (castD h) = h ▸ μ := by
  cases h
  exact Measure.map_id

/-- Horizon transport of a compact stable process law. -/
private theorem transport_stableProcessLaw (θ : ℝ) {a b : ℝ} (h : a = b) :
    h ▸ (stableProcessLaw θ a : Measure (D a ℝ)) =
      (stableProcessLaw θ b : Measure (D b ℝ)) := by
  cases h
  rfl

/-- The compact stable law of a future segment. -/
private theorem map_compactFuture_stableProcessLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s U : ℝ≥0) (h : 0 < ((s + U : ℝ≥0) : ℝ)) :
    (stableProcessLaw θ ((s + U : ℝ≥0) : ℝ) : Measure _).map (compactFuture s U) =
      (stableProcessLaw θ (U : ℝ) : Measure _) := by
  let hsT : (s : ℝ) ≤ ((s + U : ℝ≥0) : ℝ) := by simp
  let heq : ((s + U : ℝ≥0) : ℝ) - (s : ℝ) = (U : ℝ) := by simp
  have hlaw : (stableProcessLaw θ ((s + U : ℝ≥0) : ℝ) :
      Measure (D ((s + U : ℝ≥0) : ℝ) ℝ)).map (shiftIncrement s.2 hsT) =
        (stableProcessLaw θ (((s + U : ℝ≥0) : ℝ) - (s : ℝ)) :
          Measure (D (((s + U : ℝ≥0) : ℝ) - (s : ℝ)) ℝ)) := by
    have hlaw' := congrArg (fun Q : ProbabilityMeasure
        (D (((s + U : ℝ≥0) : ℝ) - (s : ℝ)) ℝ) =>
          (Q : Measure (D (((s + U : ℝ≥0) : ℝ) - (s : ℝ)) ℝ)))
      (stableProcessLaw_simpleMarkov hθ h s.2 hsT).2
    change (stableProcessLaw θ ((s + U : ℝ≥0) : ℝ) : Measure _).map
      (shiftIncrement s.2 hsT) = _ at hlaw'
    exact hlaw'
  calc
    _ = ((stableProcessLaw θ ((s + U : ℝ≥0) : ℝ) : Measure _).map
        (shiftIncrement s.2 hsT)).map (castD heq) := by
      change (stableProcessLaw θ ((s + U : ℝ≥0) : ℝ) : Measure _).map
        ((fun f => castD heq f) ∘ shiftIncrement s.2 hsT) = _
      exact (Measure.map_map (μ := (stableProcessLaw θ ((s + U : ℝ≥0) : ℝ) : Measure _))
        (measurable_castD heq) (measurable_shiftIncrement s.2 hsT)).symm
    _ = _ := by rw [hlaw]; rfl
    _ = heq ▸ (stableProcessLaw θ (((s + U : ℝ≥0) : ℝ) - (s : ℝ)) : Measure _) :=
      map_castD heq _
    _ = _ := transport_stableProcessLaw θ heq

/-- Restriction and centered shift agree with the compact increment path. -/
private theorem restrict_shift_eq_compactFuture (s U : ℝ≥0) (f : DLoc) :
    DLoc.restrict U (DLoc.shift s f) = compactFuture s U (DLoc.restrict (s + U) f) := by
  apply BGW.Skorokhod.ext
  intro t
  rcases t with ⟨t, ht0, htU⟩
  change f.1 (s + ⟨t, ht0⟩) - f.1 s = _
  rw [compactFuture, castD_apply]
  rfl

/-- The compact future restriction σ-algebras increase with the horizon. -/
private theorem future_restrict_comap_mono {U V : ℝ≥0} (hUV : U ≤ V) (s : ℝ≥0) :
    MeasurableSpace.comap (fun f : DLoc => DLoc.restrict (U : ℝ≥0) (DLoc.shift s f)) inferInstance ≤
      MeasurableSpace.comap (fun f : DLoc => DLoc.restrict V (DLoc.shift s f)) inferInstance := by
  let h : (U : ℝ) ≤ (V : ℝ) := by exact_mod_cast hUV
  have heq : (fun f : DLoc => DLoc.restrict U (DLoc.shift s f)) =
      (Skorokhod.restrict h) ∘ (fun f : DLoc => DLoc.restrict V (DLoc.shift s f)) := by
    funext f
    exact DLoc.restrict_restrict hUV (DLoc.shift s f)
  rw [heq, ← MeasurableSpace.comap_comp]
  exact MeasurableSpace.comap_mono (BGW.Skorokhod.measurable_restrict h).comap_le

/-- **Law of the future.** After any deterministic time `s ≥ 0` the centered path has the
original law (`s = 0` included). -/
theorem map_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc).map (DLoc.shift s) = (stableLocalLaw θ : Measure DLoc) := by
  let Q : ProbabilityMeasure DLoc := (stableLocalLaw θ).map (DLoc.shift s)
  have hQ : Q = stableLocalLaw θ := (eq_stableLocalLaw_iff hθ).mpr (by
    intro U hU
    change ((stableLocalLaw θ : Measure DLoc).map (DLoc.shift s)).map (DLoc.restrict U) = _
    rw [Measure.map_map (DLoc.measurable_restrict U) (DLoc.measurable_shift_fixed s)]
    have heq : DLoc.restrict U ∘ DLoc.shift s = compactFuture s U ∘ DLoc.restrict (s + U) := by
      funext f
      exact restrict_shift_eq_compactFuture s U f
    rw [heq, ← Measure.map_map (measurable_compactFuture s U) (DLoc.measurable_restrict _),
      map_restrict_stableLocalLaw hθ (by positivity : 0 < s + U)]
    exact map_compactFuture_stableProcessLaw hθ s U (by positivity))
  exact congrArg (fun R : ProbabilityMeasure DLoc => (R : Measure DLoc)) hQ

/-- Set integrals factor against a functional of an independent path. -/
private theorem integral_comp_mul_past_of_indep {Ω Χ : Type*} [mΩ : MeasurableSpace Ω]
    [mΧ : MeasurableSpace Χ] (μ : Measure Ω) {m : MeasurableSpace Ω}
    {g : Ω → Χ} {A : Set Ω} {F : Χ → ℝ}
    (hm : m ≤ mΩ)
    (h_ind : Indep m (MeasurableSpace.comap g mΧ) μ)
    (hA : MeasurableSet[m] A) (hg : @Measurable Ω Χ mΩ mΧ g)
    (hF : @Measurable Χ ℝ mΧ inferInstance F) :
    ∫ f in A, F (g f) ∂μ = μ.real A * ∫ f, F (g f) ∂μ := by
  have hAglobal : MeasurableSet[mΩ] A := hm _ hA
  have hind : @IndepFun Ω ℝ ℝ mΩ _ _ (A.indicator (fun _ => (1 : ℝ))) (F ∘ g) μ :=
    (h_ind.indicator_indepFun (1 : ℝ) hA).comp measurable_id hF
  have hprod := _root_.ProbabilityTheory.IndepFun.integral_fun_mul_eq_mul_integral hind
    (measurable_const.indicator hAglobal).aestronglyMeasurable
    (hF.comp hg).aestronglyMeasurable
  have hfun : (fun ω => A.indicator (fun _ => (1 : ℝ)) ω * (F ∘ g) ω) =
      A.indicator (F ∘ g) := by
    funext x
    by_cases hx : x ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hmass : (∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂μ) = μ.real A := by
    simpa only [Pi.one_def] using integral_indicator_one hAglobal
  rw [hfun, integral_indicator hAglobal, hmass] at hprod
  exact hprod

/-- **Bounded-test form.** For every sub-σ-algebra `m ≤ comap (restrict hsT)` of the
natural past, `A` `m`-measurable and bounded Borel `F` on the future path space,
`∫_A F(future) dP = P(A) · ∫ F d(law of the future)`. The measures `P`, `Q` are bound before `m`
(with equations to the stable laws) so that they carry the Borel σ-algebra, not `m`, which would
otherwise become the local `MeasurableSpace (D T ℝ)` instance. -/
theorem integral_shiftIncrement_mul_past_stableProcessLaw {θ T s : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hs : 0 ≤ s) (hsT : s ≤ T)
    (P : Measure (D T ℝ)) (hP : P = (stableProcessLaw θ T : Measure (D T ℝ)))
    (Q : Measure (D (T - s) ℝ)) (hQ : Q = (stableProcessLaw θ (T - s) : Measure (D (T - s) ℝ)))
    {m : MeasurableSpace (D T ℝ)}
    (hm : m ≤ MeasurableSpace.comap (restrict (E := ℝ) hsT)
      (inferInstance : MeasurableSpace (D s ℝ)))
    {A : Set (D T ℝ)} (hA : MeasurableSet[m] A)
    {F : D (T - s) ℝ → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (shiftIncrement hs hsT f) ∂P = P.real A * ∫ g, F g ∂Q := by
  let : MeasurableSpace (D T ℝ) := BGW.Skorokhod.instMeasurableSpace
  have hrestr : @Measurable (D T ℝ) (D s ℝ) BGW.Skorokhod.instMeasurableSpace
      BGW.Skorokhod.instMeasurableSpace (restrict hsT) :=
    BGW.Skorokhod.measurable_restrict hsT
  have hmle : m ≤ BGW.Skorokhod.instMeasurableSpace := hm.trans hrestr.comap_le
  let : IsProbabilityMeasure P := hP.symm ▸ inferInstance
  have _hFb := hFb
  have hbase := (stableProcessLaw_simpleMarkov hθ hT hs hsT).1
  rw [← hP] at hbase
  have hfact : ∫ f in A, F (shiftIncrement hs hsT f) ∂P =
      P.real A * ∫ f, F (shiftIncrement hs hsT f) ∂P :=
    @integral_comp_mul_past_of_indep (D T ℝ) (D (T - s) ℝ)
      BGW.Skorokhod.instMeasurableSpace BGW.Skorokhod.instMeasurableSpace P m
      (shiftIncrement hs hsT) A F hmle (indep_of_indep_of_le_left hbase hm) hA
      (measurable_shiftIncrement hs hsT) hF
  have hmap : P.map (shiftIncrement hs hsT) = Q := by
    have h := congrArg (fun R : ProbabilityMeasure (D (T - s) ℝ) =>
      (R : Measure (D (T - s) ℝ))) (stableProcessLaw_simpleMarkov hθ hT hs hsT).2
    change (stableProcessLaw θ T).toMeasure.map (shiftIncrement hs hsT) = _ at h
    rw [← hP, ← hQ] at h
    exact h
  calc
    _ = P.real A * ∫ f, F (shiftIncrement hs hsT f) ∂P := hfact
    _ = P.real A * ∫ g, F g ∂(P.map (shiftIncrement hs hsT)) := by
      rw [integral_map (measurable_shiftIncrement hs hsT).aemeasurable hF.aestronglyMeasurable]
    _ = _ := by rw [hmap]

/-- Past/future independence in σ-algebra form on `D T ℝ`: the σ-algebra pulled back by
`restrict hsT` (natural past up to `s`) is independent of the σ-algebra of the future increment
path. -/
theorem indep_comap_restrict_shiftIncrement_stableProcessLaw {θ T s : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) (hs : 0 ≤ s) (hsT : s ≤ T) :
    Indep (MeasurableSpace.comap (restrict (E := ℝ) hsT) (inferInstance : MeasurableSpace (D s ℝ)))
      (MeasurableSpace.comap (shiftIncrement hs hsT)
        (inferInstance : MeasurableSpace (D (T - s) ℝ)))
      (stableProcessLaw θ T : Measure (D T ℝ)) := by
  exact (stableProcessLaw_simpleMarkov hθ hT hs hsT).1

/-- Independence of the past up to `s` and the future restricted to a fixed horizon. -/
private theorem indep_raw_restrict_shift_of_pos {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s U : ℝ≥0)
    (hU : 0 < U) :
    Indep (DLoc.rawFiltration s)
      (MeasurableSpace.comap (fun f : DLoc => DLoc.restrict U (DLoc.shift s f)) inferInstance)
      (stableLocalLaw θ : Measure DLoc) := by
  let hsT : (s : ℝ) ≤ ((s + U : ℝ≥0) : ℝ) := by simp
  let heq : ((s + U : ℝ≥0) : ℝ) - (s : ℝ) = (U : ℝ) := by simp
  have hcompfun : IndepFun (Skorokhod.restrict hsT) (compactFuture s U)
      (stableProcessLaw θ ((s + U : ℝ≥0) : ℝ) : Measure _) := by
    have hbase := (stableProcessLaw_simpleMarkov hθ
      (show 0 < ((s + U : ℝ≥0) : ℝ) by exact_mod_cast
        (add_pos_of_nonneg_of_pos s.2 hU)) s.2 hsT).1
    have hcomp := hbase.comp measurable_id (measurable_castD heq)
    exact hcomp
  have hcomp : Indep
      (MeasurableSpace.comap (Skorokhod.restrict hsT) inferInstance)
      (MeasurableSpace.comap (compactFuture s U) inferInstance)
      (stableProcessLaw θ ((s + U : ℝ≥0) : ℝ) : Measure _) := hcompfun
  rw [rawFiltration_eq_comap_restrict] at ⊢
  rw [Indep_iff] at hcomp ⊢
  intro A B hA hB
  obtain ⟨A', hA', rfl⟩ := hA
  obtain ⟨B', hB', rfl⟩ := hB
  have hApast : MeasurableSet[MeasurableSpace.comap (Skorokhod.restrict hsT) inferInstance]
      (Skorokhod.restrict hsT ⁻¹' A') := ⟨A', hA', rfl⟩
  have hBfuture : MeasurableSet[MeasurableSpace.comap (compactFuture s U) inferInstance]
      (compactFuture s U ⁻¹' B') := ⟨B', hB', rfl⟩
  have h := hcomp _ _ hApast hBfuture
  rw [← map_restrict_stableLocalLaw hθ (by exact_mod_cast (add_pos_of_nonneg_of_pos s.2 hU))] at h
  rw [Measure.map_apply (DLoc.measurable_restrict (s + U))
      ((Skorokhod.measurable_restrict hsT hA').inter ((measurable_compactFuture s U) hB')),
    Measure.map_apply (DLoc.measurable_restrict (s + U)) (Skorokhod.measurable_restrict hsT hA'),
    Measure.map_apply (DLoc.measurable_restrict (s + U)) ((measurable_compactFuture s U) hB')] at h
  simpa only [Set.preimage_inter, Set.preimage_preimage, Function.comp_def,
    DLoc.restrict_restrict (show s ≤ s + U by simp),
    restrict_shift_eq_compactFuture] using h

/-- Independence of the raw past and a compact future segment, including zero horizon. -/
private theorem indep_raw_restrict_shift {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s U : ℝ≥0) :
    Indep (DLoc.rawFiltration s)
      (MeasurableSpace.comap (fun f : DLoc => DLoc.restrict U (DLoc.shift s f)) inferInstance)
      (stableLocalLaw θ : Measure DLoc) := by
  by_cases hU : U = 0
  · subst U
    exact indep_of_indep_of_le_right (indep_raw_restrict_shift_of_pos hθ s 1 (by simp))
      (future_restrict_comap_mono (by simp) s)
  · exact indep_raw_restrict_shift_of_pos hθ s U (pos_iff_ne_zero.mpr hU)

/-- The same independence from the raw past `F_s = DLoc.rawFiltration s` (the first, easier
step; follows from the compact simple Markov property). -/
theorem indep_rawFiltration_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0) :
    Indep (DLoc.rawFiltration s)
      (MeasurableSpace.comap (DLoc.shift s) (inferInstance : MeasurableSpace DLoc))
      (stableLocalLaw θ : Measure DLoc) := by
  have hle (U : ℕ) :
      MeasurableSpace.comap (fun f : DLoc => DLoc.restrict (U : ℝ≥0) (DLoc.shift s f))
        inferInstance ≤
        (inferInstance : MeasurableSpace DLoc) :=
    ((DLoc.measurable_restrict (U : ℝ≥0)).comp (DLoc.measurable_shift_fixed s)).comap_le
  have hdir : Directed (· ≤ ·) (fun n : ℕ =>
      MeasurableSpace.comap (fun f : DLoc => DLoc.restrict (n : ℝ≥0) (DLoc.shift s f))
        inferInstance) := by
    intro U V
    exact ⟨max U V, future_restrict_comap_mono (by exact_mod_cast le_max_left U V) s,
      future_restrict_comap_mono (by exact_mod_cast le_max_right U V) s⟩
  have h := indep_iSup_of_directed_le
    (m := fun U : ℕ =>
      MeasurableSpace.comap (fun f : DLoc => DLoc.restrict (U : ℝ≥0) (DLoc.shift s f))
        inferInstance)
    (m1 := DLoc.rawFiltration s)
    (fun U => (indep_raw_restrict_shift hθ s (U : ℝ≥0)).symm) hle (DLoc.rawFiltration.le s) hdir
  have hfuture : MeasurableSpace.comap (DLoc.shift s) (inferInstance : MeasurableSpace DLoc) =
      ⨆ n : ℕ, MeasurableSpace.comap
        (fun f : DLoc => DLoc.restrict (n : ℝ≥0) (DLoc.shift s f)) inferInstance := by
    rw [DLoc.measurableSpace_eq_iSup_comap_restrict]
    simp only [MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp, Function.comp_def]
  rw [← hfuture] at h
  exact h.symm

/-- An event in the right-continuous past is raw-past measurable at every strictly later time. -/
private theorem measurableSet_raw_of_filtration {s r : ℝ≥0} {A : Set DLoc}
    (hA : MeasurableSet[DLoc.filtration s] A) (hsr : s < r) :
    MeasurableSet[DLoc.rawFiltration r] A := by
  have hA' := hA
  change MeasurableSet[DLoc.rawFiltration.rightCont s] A at hA'
  rw [Filtration.rightCont_eq] at hA'
  exact MeasurableSpace.measurableSet_iInf.mp
    (MeasurableSpace.measurableSet_iInf.mp hA' r) hsr

/-- Conditioning on a germ event does not change the finite-dimensional law of a future segment. -/
private theorem map_restrict_shift_cond_finiteDimensional {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (s U : ℝ≥0) {A : Set DLoc} (hA : MeasurableSet[DLoc.filtration s] A)
    (hA0 : (stableLocalLaw θ : Measure DLoc) A ≠ 0) (q : Finset (Set.Icc (0 : ℝ) (U : ℝ))) :
    ((stableLocalLaw θ : Measure DLoc)[|A].map
        (fun f : DLoc => fun t : q => DLoc.restrict U (DLoc.shift s f) t)) =
      (stableLocalLaw θ : Measure DLoc).map
        (fun f : DLoc => fun t : q => DLoc.restrict U (DLoc.shift s f) t) := by
  let P : Measure DLoc := stableLocalLaw θ
  let r : ℕ → ℝ≥0 := fun n => s + (((n + 1 : ℕ) : ℝ≥0)⁻¹)
  let E : ℝ≥0 → DLoc → (q → ℝ) := fun t f u => DLoc.restrict U (DLoc.shift t f) u
  have hr (n : ℕ) : s < r n := by
    dsimp [r]
    exact lt_add_of_pos_right s (inv_pos.mpr (by positivity))
  have htend_eps : Tendsto (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0)⁻¹)) atTop (𝓝 0) := by
    apply NNReal.tendsto_coe.1
    convert tendsto_inv_atTop_zero.comp
      (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop) using 1 <;>
      norm_cast
  have htend_r : Tendsto r atTop (𝓝 s) := by
    simpa only [r, add_zero] using tendsto_const_nhds.add htend_eps
  have hE_measurable (t : ℝ≥0) : Measurable (E t) := by
    apply Measurable.of_eval
    intro u
    exact (BGW.Skorokhod.measurable_eval u.1).comp
      ((DLoc.measurable_restrict U).comp (DLoc.measurable_shift_fixed t))
  have hE_comap (t : ℝ≥0) : MeasurableSpace.comap (E t) inferInstance ≤
      MeasurableSpace.comap (DLoc.shift t) (inferInstance : MeasurableSpace DLoc) := by
    let out : D (U : ℝ) ℝ → (q → ℝ) := fun g u => g u.1
    have hout : Measurable out := Measurable.of_eval fun u => BGW.Skorokhod.measurable_eval u.1
    change MeasurableSpace.comap ((out ∘ DLoc.restrict U) ∘ DLoc.shift t) inferInstance ≤ _
    rw [← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (hout.comp (DLoc.measurable_restrict U)).comap_le
  have hE_law (t : ℝ≥0) : P.map (E t) = P.map (E s) := by
    have hEval : Measurable (fun g : D (U : ℝ) ℝ => fun u : q => g u.1) :=
      Measurable.of_eval fun u => BGW.Skorokhod.measurable_eval u.1
    have hmaps (v : ℝ≥0) : P.map (E v) =
        ((P.map (DLoc.shift v)).map (DLoc.restrict U)).map
          (fun g : D (U : ℝ) ℝ => fun u : q => g u.1) := by
      calc
        P.map (E v) = P.map (((fun g : D (U : ℝ) ℝ => fun u : q => g u.1) ∘
          DLoc.restrict U) ∘ DLoc.shift v) := by rfl
        _ = (P.map (DLoc.shift v)).map
            ((fun g : D (U : ℝ) ℝ => fun u : q => g u.1) ∘ DLoc.restrict U) :=
          (Measure.map_map (hEval.comp (DLoc.measurable_restrict U))
            (DLoc.measurable_shift_fixed v)).symm
        _ = _ := (Measure.map_map hEval (DLoc.measurable_restrict U)).symm
    rw [hmaps t, hmaps s, map_shift_stableLocalLaw hθ t, map_shift_stableLocalLaw hθ s]
  have hpoint (f : DLoc) : Tendsto (fun n => E (r n) f) atTop (𝓝 (E s f)) := by
    rw [tendsto_pi_nhds]
    intro u
    let uu : ℝ≥0 := ⟨u.1.1, u.1.2.1⟩
    have ht : Tendsto (fun n => r n + uu) atTop (𝓝[>] (s + uu)) := by
      apply tendsto_nhdsWithin_iff.mpr
      exact ⟨htend_r.add tendsto_const_nhds, Eventually.of_forall fun n => by
        simpa only [Set.mem_Ioi, add_comm] using add_lt_add_right (hr n) uu⟩
    have heval : Tendsto (fun n => f.1 (r n + uu)) atTop (𝓝 (f.1 (s + uu))) :=
      (f.2.isRightContinuous (s + uu)).tendsto.comp ht
    have hs : Tendsto (fun n => f.1 (r n)) atTop (𝓝 (f.1 s)) := by
      apply (f.2.isRightContinuous s).tendsto.comp
      exact tendsto_nhdsWithin_iff.mpr ⟨htend_r, Eventually.of_forall hr⟩
    exact heval.sub hs
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro F
  have hmass : (P A)⁻¹.toReal * P.real A = 1 := by
    rw [ENNReal.toReal_inv, measureReal_def]
    exact inv_mul_cancel₀ (ENNReal.toReal_ne_zero.mpr ⟨hA0, measure_ne_top P A⟩)
  have hseq (n : ℕ) : (∫ x, F x ∂(P[|A].map (E (r n)))) = ∫ x, F x ∂(P.map (E s)) := by
    have hfact : (∫ f in A, F (E (r n) f) ∂P) =
        P.real A * ∫ f, F (E (r n) f) ∂P :=
      integral_comp_mul_past_of_indep P (DLoc.rawFiltration.le (r n))
        (indep_of_indep_of_le_right (indep_rawFiltration_shift_stableLocalLaw hθ (r n))
          (hE_comap (r n)))
        (measurableSet_raw_of_filtration hA (hr n)) (hE_measurable (r n)) F.measurable
    calc
      _ = ∫ f, F (E (r n) f) ∂P[|A] := by
        exact integral_map (hE_measurable (r n)).aemeasurable F.measurable.aestronglyMeasurable
      _ = (P A)⁻¹.toReal * ∫ f, F (E (r n) f) ∂(P.restrict A) := by
        rw [ProbabilityTheory.cond, integral_smul_measure, smul_eq_mul]
      _ = (P A)⁻¹.toReal * ∫ f in A, F (E (r n) f) ∂P := by rfl
      _ = (P A)⁻¹.toReal * (P.real A * ∫ f, F (E (r n) f) ∂P) := by rw [hfact]
      _ = ∫ f, F (E (r n) f) ∂P := by rw [← mul_assoc, hmass, one_mul]
      _ = ∫ x, F x ∂(P.map (E (r n))) :=
        (integral_map (hE_measurable (r n)).aemeasurable F.measurable.aestronglyMeasurable).symm
      _ = _ := by rw [hE_law (r n)]
  have hlim : Tendsto (fun n => ∫ x, F x ∂(P[|A].map (E (r n)))) atTop
      (𝓝 (∫ x, F x ∂(P[|A].map (E s)))) := by
    have hmapInt (v : ℝ≥0) : (∫ x, F x ∂(P[|A].map (E v))) =
        ∫ f, F (E v f) ∂P[|A] :=
      integral_map (hE_measurable v).aemeasurable F.measurable.aestronglyMeasurable
    simp_rw [hmapInt]
    apply tendsto_integral_filter_of_dominated_convergence (fun _ => ‖F‖)
    · exact Eventually.of_forall fun n =>
        (F.measurable.comp (hE_measurable (r n))).aestronglyMeasurable
    · exact Eventually.of_forall fun n => Eventually.of_forall fun f => F.norm_coe_le_norm _
    · exact integrable_const _
    · exact Eventually.of_forall fun f => (F.continuous.tendsto _).comp (hpoint f)
  exact tendsto_nhds_unique hlim
    (tendsto_const_nhds.congr' (Eventually.of_forall fun n => (hseq n).symm))

/-- Conditioning on a germ event does not change the law of the whole future increment path. -/
private theorem map_shift_cond_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0)
    {A : Set DLoc} (hA : MeasurableSet[DLoc.filtration s] A)
    (hA0 : (stableLocalLaw θ : Measure DLoc) A ≠ 0) :
    (stableLocalLaw θ : Measure DLoc)[|A].map (DLoc.shift s) =
      (stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let L : ProbabilityMeasure DLoc := ⟨P[|A], cond_isProbabilityMeasure hA0⟩
  have hL : L.map (DLoc.shift s) = stableLocalLaw θ := (eq_stableLocalLaw_iff hθ).mpr (by
    intro U hU
    have hPM : (L.map (DLoc.shift s)).map (DLoc.restrict U) = stableProcessLaw θ U := by
      apply Skorokhod.ext_of_finiteDimensional dense_univ U.2 (Set.mem_univ _)
      intro q hq
      apply ProbabilityMeasure.toMeasure_injective
      erw [ProbabilityMeasure.toMeasure_map]
      erw [ProbabilityMeasure.toMeasure_map]
      erw [ProbabilityMeasure.toMeasure_map]
      erw [ProbabilityMeasure.toMeasure_map]
      have hEval : Measurable (fun g : D (U : ℝ) ℝ => fun u : q => g u.1) :=
        Measurable.of_eval fun u => BGW.Skorokhod.measurable_eval u.1
      erw [Measure.map_map hEval (DLoc.measurable_restrict U),
        Measure.map_map (hEval.comp (DLoc.measurable_restrict U)) (DLoc.measurable_shift_fixed s),
        ← map_restrict_stableLocalLaw hθ hU, Measure.map_map hEval (DLoc.measurable_restrict U),
        ← map_shift_stableLocalLaw hθ s,
        Measure.map_map (hEval.comp (DLoc.measurable_restrict U)) (DLoc.measurable_shift_fixed s)]
      exact map_restrict_shift_cond_finiteDimensional hθ s U hA hA0 q
    exact congrArg (fun R : ProbabilityMeasure (D (U : ℝ) ℝ) => (R : Measure (D (U : ℝ) ℝ))) hPM)
  have hout := congrArg (fun R : ProbabilityMeasure DLoc => (R : Measure DLoc)) hL
  exact hout

/-- **Simple Markov property, σ-algebra form.** The future increment path after `s` is
independent of the right-continuous past `F_s^+ = DLoc.filtration s`. -/
theorem indep_filtration_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0) :
    Indep (DLoc.filtration s)
      (MeasurableSpace.comap (DLoc.shift s) (inferInstance : MeasurableSpace DLoc))
      (stableLocalLaw θ : Measure DLoc) := by
  rw [Indep_iff]
  intro A B hA hB
  obtain ⟨B', hB', rfl⟩ := hB
  by_cases hA0 : (stableLocalLaw θ : Measure DLoc) A = 0
  · have hzero : (stableLocalLaw θ : Measure DLoc) (A ∩ DLoc.shift s ⁻¹' B') = 0 :=
      measure_mono_null (Set.inter_subset_left) hA0
    simp [hzero, hA0]
  · have hlaw := map_shift_cond_stableLocalLaw hθ s hA hA0
    have heval := congrArg (fun μ : Measure DLoc => μ B') hlaw
    rw [Measure.map_apply (DLoc.measurable_shift_fixed s) hB'] at heval
    rw [ProbabilityTheory.cond, Measure.coe_smul, Pi.smul_apply,
      Measure.restrict_apply ((DLoc.measurable_shift_fixed s) hB'), smul_eq_mul] at heval
    rw [Set.inter_comm A (DLoc.shift s ⁻¹' B')]
    calc
      _ = ((stableLocalLaw θ : Measure DLoc) A * ((stableLocalLaw θ : Measure DLoc) A)⁻¹) *
          (stableLocalLaw θ : Measure DLoc) (DLoc.shift s ⁻¹' B' ∩ A) := by
        rw [ENNReal.mul_inv_cancel hA0 (measure_ne_top _ _), one_mul]
      _ = (stableLocalLaw θ : Measure DLoc) A *
          (((stableLocalLaw θ : Measure DLoc) A)⁻¹ *
            (stableLocalLaw θ : Measure DLoc) (DLoc.shift s ⁻¹' B' ∩ A)) := mul_assoc _ _ _
      _ = _ := by
        rw [heval, ← Measure.map_apply (DLoc.measurable_shift_fixed s) hB',
          map_shift_stableLocalLaw hθ]

/-- **Bounded-test corollary (whole future).** For `A ∈ F_s^+` and bounded Borel `F` on `DLoc`,
`∫_A F(shift_s f) dP = P(A) · ∫ F dP`. -/
theorem integral_shift_mul_past {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0) {A : Set DLoc}
    (hA : MeasurableSet[DLoc.filtration s] A) {F : DLoc → ℝ} (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.shift s f) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A * ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) := by
  have _hFb := hFb
  calc
    _ = (stableLocalLaw θ : Measure DLoc).real A *
        ∫ f, F (DLoc.shift s f) ∂(stableLocalLaw θ : Measure DLoc) :=
      integral_comp_mul_past_of_indep (stableLocalLaw θ : Measure DLoc)
        (DLoc.filtration.le s) (indep_filtration_shift_stableLocalLaw hθ s) hA
        (DLoc.measurable_shift_fixed s) hF
    _ = (stableLocalLaw θ : Measure DLoc).real A *
        ∫ f, F f ∂((stableLocalLaw θ : Measure DLoc).map (DLoc.shift s)) := by
      rw [integral_map (DLoc.measurable_shift_fixed s).aemeasurable hF.aestronglyMeasurable]
    _ = _ := by rw [map_shift_stableLocalLaw hθ]

/-- **Bounded-test corollary (compact future window).** The blueprint form: the future after `s`
centered and cut at horizon `U`, tested by bounded Borel `F` on `D U ℝ`. The right side uses
`stableProcessLaw θ U`. -/
theorem integral_futureSegment_mul_past {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s U : ℝ≥0) {A : Set DLoc}
    (hA : MeasurableSet[DLoc.filtration s] A) {F : D (U : ℝ) ℝ → ℝ} (hF : Measurable F)
    (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f in A, F (DLoc.restrict U (DLoc.shift s f)) ∂(stableLocalLaw θ : Measure DLoc) =
      (stableLocalLaw θ : Measure DLoc).real A *
        ∫ g, F g ∂(stableProcessLaw θ (U : ℝ) : Measure (D (U : ℝ) ℝ)) := by
  have hbound : ∃ C : ℝ, ∀ f : DLoc, |(F ∘ DLoc.restrict U) f| ≤ C := by
    obtain ⟨C, hC⟩ := hFb
    exact ⟨C, fun f => hC _⟩
  change (∫ f in A, (F ∘ DLoc.restrict U) (DLoc.shift s f) ∂(stableLocalLaw θ)) = _
  rw [integral_shift_mul_past hθ s hA (hF.comp (DLoc.measurable_restrict U)) hbound]
  have hmap : (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict U) =
      (stableProcessLaw θ (U : ℝ) : Measure (D (U : ℝ) ℝ)) := by
    by_cases hU : U = 0
    · subst U
      exact map_restrict_zero_stableLocalLaw hθ
    · exact map_restrict_stableLocalLaw hθ (pos_iff_ne_zero.mpr hU)
  rw [← hmap, integral_map (DLoc.measurable_restrict U).aemeasurable hF.aestronglyMeasurable]
  rfl

/-- Product form: `E[G · F(shift_s)] = E[G] · E[F]` for `G` bounded `F_s^+`-measurable and `F`
bounded Borel. -/
theorem integral_mul_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0)
    {G : DLoc → ℝ} (hG : Measurable[DLoc.filtration s] G) (hGb : ∃ C : ℝ, ∀ x, |G x| ≤ C)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    ∫ f, G f * F (DLoc.shift s f) ∂(stableLocalLaw θ : Measure DLoc) =
      (∫ f, G f ∂(stableLocalLaw θ : Measure DLoc)) *
        ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) := by
  have _hGb := hGb
  have _hFb := hFb
  have hind : IndepFun G (DLoc.shift s) (stableLocalLaw θ : Measure DLoc) :=
    indep_of_indep_of_le_left (indep_filtration_shift_stableLocalLaw hθ s) hG.comap_le
  calc
    _ = (∫ f, G f ∂(stableLocalLaw θ : Measure DLoc)) *
        ∫ f, F (DLoc.shift s f) ∂(stableLocalLaw θ : Measure DLoc) := by
      have hindF := hind.comp measurable_id hF
      have hprod := IndepFun.integral_fun_mul_eq_mul_integral hindF
        (hG.mono (DLoc.filtration.le s) le_rfl).aestronglyMeasurable
        ((hF.comp (DLoc.measurable_shift_fixed s)).aestronglyMeasurable)
      simpa only [Function.comp_apply, id_eq] using hprod
    _ = (∫ f, G f ∂(stableLocalLaw θ : Measure DLoc)) *
        ∫ f, F f ∂((stableLocalLaw θ : Measure DLoc).map (DLoc.shift s)) := by
      rw [integral_map (DLoc.measurable_shift_fixed s).aemeasurable hF.aestronglyMeasurable]
    _ = _ := by rw [map_shift_stableLocalLaw hθ]

/-- **Conditional-expectation form.** Given `F_s^+`, a bounded Borel functional of the future
has the constant conditional expectation `∫ F dP`. -/
theorem condExp_shift_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0)
    {F : DLoc → ℝ} (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ x, |F x| ≤ C) :
    (stableLocalLaw θ : Measure DLoc)[fun f => F (DLoc.shift s f) | DLoc.filtration s] =ᵐ[
      (stableLocalLaw θ : Measure DLoc)]
      fun _ => ∫ f, F f ∂(stableLocalLaw θ : Measure DLoc) := by
  have _hFb := hFb
  have hshift : Measurable[MeasurableSpace.comap (DLoc.shift s) inferInstance] (DLoc.shift s) :=
    Measurable.of_comap_le le_rfl
  have hstrong : StronglyMeasurable[MeasurableSpace.comap (DLoc.shift s) inferInstance]
      (fun f => F (DLoc.shift s f)) := (hF.comp hshift).stronglyMeasurable
  have hint : (∫ f, F (DLoc.shift s f) ∂(stableLocalLaw θ)) =
      ∫ f, F f ∂(stableLocalLaw θ) := by
    calc
      _ = ∫ f, F f ∂((stableLocalLaw θ : Measure DLoc).map (DLoc.shift s)) := by
        rw [integral_map (DLoc.measurable_shift_fixed s).aemeasurable hF.aestronglyMeasurable]
      _ = _ := by rw [map_shift_stableLocalLaw hθ]
  rw [← hint]
  exact condExp_indep_eq (DLoc.measurable_shift_fixed s).comap_le (DLoc.filtration.le s)
    hstrong (indep_filtration_shift_stableLocalLaw hθ s).symm

/-- **Germ zero-one law** (`s = 0`): every event of `F_0^+` has probability `0` or `1`. -/
theorem measure_zeroOne_filtration_zero {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {A : Set DLoc}
    (hA : MeasurableSet[DLoc.filtration 0] A) :
    (stableLocalLaw θ : Measure DLoc) A = 0 ∨ (stableLocalLaw θ : Measure DLoc) A = 1 := by
  let P : Measure DLoc := stableLocalLaw θ
  have hshift : DLoc.shift 0 =ᵐ[P] id := by
    filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
    apply Subtype.ext
    funext t
    simp only [DLoc.shift, zero_add, id_eq]
    rw [hf, sub_zero]
  have hAglobal : MeasurableSet A := DLoc.filtration.le 0 A hA
  have hpre : DLoc.shift 0 ⁻¹' A =ᵐ[P] A := by
    filter_upwards [hshift] with f hf
    change (DLoc.shift 0 f ∈ A) = (f ∈ A)
    rw [hf]
    rfl
  have hinter : A ∩ DLoc.shift 0 ⁻¹' A =ᵐ[P] A := by
    filter_upwards [hpre] with f hf
    change (f ∈ A ∧ DLoc.shift 0 f ∈ A) = (f ∈ A)
    apply propext
    constructor
    · exact And.left
    · intro h
      exact ⟨h, hf ▸ h⟩
  have hfactor := (Indep_iff _ _ _).mp (indep_filtration_shift_stableLocalLaw hθ 0)
    A (DLoc.shift 0 ⁻¹' A) hA ⟨A, hAglobal, rfl⟩
  have hsquare : P A = P A * P A := by
    calc
      P A = P (A ∩ DLoc.shift 0 ⁻¹' A) := (measure_congr hinter).symm
      _ = P A * P (DLoc.shift 0 ⁻¹' A) := hfactor
      _ = P A * P A := by rw [measure_congr hpre]
  have hreal := congrArg ENNReal.toReal hsquare
  rw [ENNReal.toReal_mul] at hreal
  by_cases hzero : P A = 0
  · exact Or.inl hzero
  · apply Or.inr
    rw [← ENNReal.toReal_eq_one_iff]
    have hne : (P A).toReal ≠ 0 :=
      ENNReal.toReal_ne_zero.mpr ⟨hzero, measure_ne_top P A⟩
    have heq : (P A).toReal * (P A).toReal = (P A).toReal * 1 := by
      simpa only [mul_one] using hreal.symm
    exact mul_left_cancel₀ hne heq

/-- The real exponential of a fixed-time coordinate is integrable and has the stable Laplace
transform. -/
private theorem integrable_and_integral_exp_neg_mul_eval {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {u : ℝ} (hu : 0 ≤ u) (t : ℝ≥0) :
    Integrable (fun f => Real.exp (-u * DLoc.eval t f)) (stableLocalLaw θ : Measure DLoc) ∧
      (∫ f, Real.exp (-u * DLoc.eval t f) ∂(stableLocalLaw θ) =
        Real.exp ((t : ℝ) * u ^ θ)) := by
  have hmeas : Measurable (fun x : ℝ => Real.exp (-u * x)) := by fun_prop
  by_cases ht : t = 0
  · subst t
    have hzero : (fun f : DLoc => Real.exp (-u * DLoc.eval 0 f)) =ᵐ[
        (stableLocalLaw θ : Measure DLoc)] (fun _ => 1) := by
      filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
      simp [DLoc.eval, hf]
    have hi : Integrable (fun f : DLoc => Real.exp (-u * DLoc.eval 0 f))
        (stableLocalLaw θ : Measure DLoc) := (integrable_congr hzero).mpr (integrable_const 1)
    refine ⟨hi, ?_⟩
    calc
      _ = ∫ _ : DLoc, (1 : ℝ) ∂(stableLocalLaw θ) := integral_congr_ae hzero
      _ = 1 := by simp
      _ = Real.exp (((0 : ℝ≥0) : ℝ) * u ^ θ) := by simp
  · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
    have hiReal : Integrable (fun x : ℝ => Real.exp (-u * x))
        (stableLawAt θ (t : ℝ) : Measure ℝ) := by
      by_contra h
      have hL := integral_exp_neg_mul_stableLawAt hθ htpos hu
      have hzero : (∫ x : ℝ, Real.exp (-u * x) ∂(stableLawAt θ (t : ℝ))) = 0 :=
        integral_undef h
      exact (Real.exp_pos _).ne' (hL.symm.trans hzero)
    have hiMap : Integrable (fun x : ℝ => Real.exp (-u * x))
        ((stableLocalLaw θ : Measure DLoc).map (DLoc.eval t)) := by
      rw [map_eval_stableLocalLaw hθ htpos]
      exact hiReal
    refine ⟨(integrable_map_measure hmeas.aestronglyMeasurable
      (DLoc.measurable_eval t).aemeasurable).1 hiMap, ?_⟩
    calc
      _ = ∫ x, Real.exp (-u * x) ∂((stableLocalLaw θ : Measure DLoc).map (DLoc.eval t)) := by
        rw [integral_map (DLoc.measurable_eval t).aemeasurable hmeas.aestronglyMeasurable]
      _ = ∫ x, Real.exp (-u * x) ∂(stableLawAt θ (t : ℝ) : Measure ℝ) := by
        rw [map_eval_stableLocalLaw hθ htpos]
      _ = _ := integral_exp_neg_mul_stableLawAt hθ htpos hu

/-- Integrability of an exponential process with a deterministic time factor. -/
private theorem integrable_exp_process {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {u c : ℝ}
    (hu : 0 ≤ u) (t : ℝ≥0) :
    Integrable (fun f => Real.exp (-u * DLoc.eval t f - (t : ℝ) * c))
      (stableLocalLaw θ : Measure DLoc) := by
  have hi := (integrable_and_integral_exp_neg_mul_eval hθ hu t).1.const_mul
    (Real.exp (-(t : ℝ) * c))
  have heq : (fun f : DLoc => Real.exp (-(t : ℝ) * c) *
      Real.exp (-u * DLoc.eval t f)) =
      (fun f => Real.exp (-u * DLoc.eval t f - (t : ℝ) * c)) := by
    funext f
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← heq]
  exact hi

/-- The exponential process with a deterministic time factor is strongly adapted. -/
private theorem stronglyAdapted_exp_process (u c : ℝ) :
    StronglyAdapted DLoc.filtration
      (fun (t : ℝ≥0) (f : DLoc) => Real.exp (-u * DLoc.eval t f - (t : ℝ) * c)) := by
  intro t
  exact (by fun_prop : Continuous (fun x : ℝ => Real.exp (-u * x - (t : ℝ) * c)))
    |>.comp_stronglyMeasurable
    (DLoc.adapted_eval t).stronglyMeasurable

/-- Expectation of an exponential process with a deterministic time factor. -/
private theorem integral_exp_process {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {u c : ℝ}
    (hu : 0 ≤ u) (t : ℝ≥0) :
    (∫ f, Real.exp (-u * DLoc.eval t f - (t : ℝ) * c) ∂(stableLocalLaw θ)) =
      Real.exp (-(t : ℝ) * c + (t : ℝ) * u ^ θ) := by
  have heq : (fun f : DLoc => Real.exp (-u * DLoc.eval t f - (t : ℝ) * c)) =
      (fun f => Real.exp (-(t : ℝ) * c) * Real.exp (-u * DLoc.eval t f)) := by
    funext f
    rw [← Real.exp_add]
    congr 1
    ring
  rw [heq, integral_const_mul, (integrable_and_integral_exp_neg_mul_eval hθ hu t).2,
  ← Real.exp_add]

/-- Integrability is preserved by taking a functional of the centered-shifted stable path. -/
private theorem integrable_comp_shift {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (s : ℝ≥0)
    {F : DLoc → ℝ} (hF : Integrable F (stableLocalLaw θ : Measure DLoc)) :
    Integrable (fun f => F (DLoc.shift s f)) (stableLocalLaw θ : Measure DLoc) := by
  have hmap : Integrable F ((stableLocalLaw θ : Measure DLoc).map (DLoc.shift s)) := by
    rw [map_shift_stableLocalLaw hθ]
    exact hF
  have hFm : AEStronglyMeasurable F ((stableLocalLaw θ : Measure DLoc).map (DLoc.shift s)) := by
    rw [map_shift_stableLocalLaw hθ]
    exact hF.aestronglyMeasurable
  exact (integrable_map_measure hFm (DLoc.measurable_shift_fixed s).aemeasurable).1 hmap

/-- **Martingale export**: for `u ≥ 0` the exponential process
`exp(-u X_t - t u^θ)` is a martingale for the right-continuous filtration. -/
theorem martingale_exp_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {u : ℝ} (hu : 0 ≤ u) :
    Martingale (fun (t : ℝ≥0) (f : DLoc) => Real.exp (-u * DLoc.eval t f - (t : ℝ) * u ^ θ))
      DLoc.filtration (stableLocalLaw θ : Measure DLoc) := by
  let P : Measure DLoc := stableLocalLaw θ
  let M : ℝ≥0 → DLoc → ℝ := fun t f => Real.exp (-u * DLoc.eval t f - (t : ℝ) * u ^ θ)
  have hadapt : StronglyAdapted DLoc.filtration M := stronglyAdapted_exp_process u (u ^ θ)
  refine ⟨hadapt, ?_⟩
  intro s t hst
  let d : ℝ≥0 := t - s
  have hsd : s + d = t := add_tsub_cancel_of_le hst
  let F : DLoc → ℝ := fun g => Real.exp (-u * DLoc.eval d g - (d : ℝ) * u ^ θ)
  have hFM : Measurable F := by
    exact Real.measurable_exp.comp
      ((measurable_const.mul (DLoc.measurable_eval d)).sub measurable_const)
  have hFint : Integrable F P := integrable_exp_process hθ hu d
  have hFshift_int : Integrable (fun f => F (DLoc.shift s f)) P :=
    integrable_comp_shift hθ s hFint
  have hdecomp : ∀ f, M t f = M s f * F (DLoc.shift s f) := by
    intro f
    dsimp [M, F]
    rw [← Real.exp_add, DLoc.eval_shift, ← hsd]
    congr 1
    dsimp [d]
    ring
  have hshift : Measurable[MeasurableSpace.comap (DLoc.shift s) inferInstance] (DLoc.shift s) :=
    Measurable.of_comap_le le_rfl
  have hstrong : StronglyMeasurable[MeasurableSpace.comap (DLoc.shift s) inferInstance]
      (fun f => F (DLoc.shift s f)) := (hFM.comp hshift).stronglyMeasurable
  have hcond : P[fun f => F (DLoc.shift s f) | DLoc.filtration s] =ᵐ[P]
      fun _ => ∫ g, F g ∂P := by
    have hc := condExp_indep_eq (DLoc.measurable_shift_fixed s).comap_le
      (DLoc.filtration.le s) hstrong (indep_filtration_shift_stableLocalLaw hθ s).symm
    have hint : (∫ f, F (DLoc.shift s f) ∂P) = ∫ g, F g ∂P := by
      calc
        _ = ∫ g, F g ∂(P.map (DLoc.shift s)) := by
          rw [integral_map (DLoc.measurable_shift_fixed s).aemeasurable hFM.aestronglyMeasurable]
        _ = _ := by rw [map_shift_stableLocalLaw hθ]
    filter_upwards [hc] with f hf
    rw [hf, hint]
  calc
    P[M t | DLoc.filtration s] =ᵐ[P]
        P[fun f => M s f * F (DLoc.shift s f) | DLoc.filtration s] :=
      condExp_congr_ae (Eventually.of_forall hdecomp)
    _ =ᵐ[P] fun f => M s f * P[fun g => F (DLoc.shift s g) | DLoc.filtration s] f := by
      have hprod : Integrable (fun f => M s f * F (DLoc.shift s f)) P := by
        rw [show (fun f => M s f * F (DLoc.shift s f)) = M t from funext fun f => (hdecomp f).symm]
        exact integrable_exp_process hθ hu t
      exact condExp_mul_of_stronglyMeasurable_left (hadapt s) hprod hFshift_int
    _ =ᵐ[P] fun f => M s f * ∫ g, F g ∂P := by
      filter_upwards [hcond] with f hf
      rw [hf]
    _ =ᵐ[P] M s := by
      have hconst : (∫ g, F g ∂P) = 1 := by
        rw [show (∫ g, F g ∂P) =
          Real.exp (-(d : ℝ) * u ^ θ + (d : ℝ) * u ^ θ) from integral_exp_process hθ hu d]
        simp
      filter_upwards [] with f
      simp [hconst]

end BGW.StableTrees
