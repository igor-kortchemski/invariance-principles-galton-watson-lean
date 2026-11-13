/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.WalkPassageBasic
public import BGW.StableTrees.StableLocalMarkov
public import BGW.StableTrees.StableRegularity
public import BGW.StableTrees.StableDensityAPI
public import BGW.Skorokhod.Restrict
import Mathlib.Probability.Independence.Basic

/-!
# Atom-free running infima and stable passage laws

The running infimum of the stable process has no atoms.  Negative levels are
split at a positive rational time: the value at that time has a density and is
independent of the centered future.  Regularity at zero handles the zero level
(J. Bertoin, *Lévy Processes*, 1996, Chapter VII).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod BGW.StableTrees

namespace BGW.StableTrees

private lemma bddBelow_future_range_walk (f : DLoc) (s t : ℝ≥0) :
    BddBelow (Set.range (fun u : Set.Iic t => f.1 (s + u))) := by
  apply (bddBelow_runningInf_range f (s + t)).mono
  rintro _ ⟨u, rfl⟩
  exact ⟨⟨s + u, add_le_add le_rfl u.2⟩, rfl⟩

private lemma runningInfLoc_shift_walk (f : DLoc) (s t : ℝ≥0) :
    runningInfLoc (DLoc.shift s f) t =
      (⨅ u : Set.Iic t, f.1 (s + u)) - f.1 s := by
  let A : ℝ := ⨅ u : Set.Iic t, f.1 (s + u)
  have hA (u : Set.Iic t) : A ≤ f.1 (s + u) :=
    ciInf_le (bddBelow_future_range_walk f s t) u
  apply le_antisymm
  · apply le_of_forall_gt
    intro a ha
    have ha' : A < a + f.1 s := by linarith
    obtain ⟨u, hu⟩ := (ciInf_lt_iff (bddBelow_future_range_walk f s t)).mp ha'
    exact (ciInf_le (bddBelow_runningInf_range (DLoc.shift s f) t) u).trans_lt
      (by change f.1 (s + u) - f.1 s < a; linarith)
  · apply le_ciInf
    intro u
    exact sub_le_sub_right (hA u) (f.1 s)

private lemma runningInfLoc_add_walk (f : DLoc) (s t : ℝ≥0) :
    runningInfLoc f (s + t) =
      min (runningInfLoc f s) (f.1 s + runningInfLoc (DLoc.shift s f) t) := by
  let A : ℝ := ⨅ u : Set.Iic t, f.1 (s + u)
  have hA (u : Set.Iic t) : A ≤ f.1 (s + u) :=
    ciInf_le (bddBelow_future_range_walk f s t) u
  have hshift : f.1 s + runningInfLoc (DLoc.shift s f) t = A := by
    rw [runningInfLoc_shift_walk]
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

private theorem measurable_runningInf_walk (t : ℝ≥0) :
    Measurable (fun f : DLoc => runningInfLoc f t) :=
  measurable_runningInfLoc_uncurry.comp (measurable_const.prodMk measurable_id)

private theorem indepFun_eval_runningInf_shift_walk {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (a t : ℝ≥0) :
    IndepFun (DLoc.eval a) (fun f : DLoc => runningInfLoc (DLoc.shift a f) t)
      (stableLocalLaw θ : Measure DLoc) := by
  have hle : MeasurableSpace.comap (DLoc.eval a) inferInstance ≤ DLoc.rawFiltration a := by
    change MeasurableSpace.comap (DLoc.eval a) inferInstance ≤
      ⨆ s ≤ a, MeasurableSpace.comap (DLoc.eval s) inferInstance
    exact le_iSup_of_le a (le_iSup_of_le le_rfl le_rfl)
  have hind : IndepFun (DLoc.eval a) (DLoc.shift a) (stableLocalLaw θ : Measure DLoc) :=
    indep_of_indep_of_le_left (indep_rawFiltration_shift_stableLocalLaw hθ a) hle
  exact hind.comp measurable_id (measurable_runningInf_walk t)

private theorem measure_add_runningInf_shift_eq_zero_walk {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {a t : ℝ≥0} (ha : 0 < a) (c : ℝ) :
    (stableLocalLaw θ : Measure DLoc)
      {f | f.1 a + runningInfLoc (DLoc.shift a f) t = c} = 0 := by
  let X : DLoc → ℝ := DLoc.eval a
  let Y : DLoc → ℝ := fun f => runningInfLoc (DLoc.shift a f) t
  let E : Set (ℝ × ℝ) := {p | p.1 + p.2 = c}
  let joint : DLoc → ℝ × ℝ := fun f => (X f, Y f)
  have hX : Measurable X := DLoc.measurable_eval a
  have hY : Measurable Y := (measurable_runningInf_walk t).comp (DLoc.measurable_shift_fixed a)
  have hJoint : Measurable joint := hX.prodMk hY
  have hE : MeasurableSet E :=
    measurableSet_eq_fun (measurable_fst.add measurable_snd) measurable_const
  have hind : IndepFun X Y (stableLocalLaw θ : Measure DLoc) :=
    indepFun_eval_runningInf_shift_walk hθ a t
  have hmapX : Measure.map X (stableLocalLaw θ : Measure DLoc) =
      (stableLawAt θ (a : ℝ) : Measure ℝ) := map_eval_stableLocalLaw hθ ha
  calc
    (stableLocalLaw θ : Measure DLoc) {f | f.1 a + runningInfLoc (DLoc.shift a f) t = c} =
        (stableLocalLaw θ : Measure DLoc) (joint ⁻¹' E) := rfl
    _ = Measure.map joint (stableLocalLaw θ : Measure DLoc) E :=
      (Measure.map_apply hJoint hE).symm
    _ = (Measure.map X (stableLocalLaw θ : Measure DLoc)).prod
        (Measure.map Y (stableLocalLaw θ : Measure DLoc)) E := by
      rw [hind.map_prod_eq_prod_map_map hX.aemeasurable hY.aemeasurable]
    _ = ∫⁻ y, Measure.map X (stableLocalLaw θ : Measure DLoc)
        ((fun x => (x, y)) ⁻¹' E) ∂Measure.map Y (stableLocalLaw θ : Measure DLoc) :=
      Measure.prod_apply_symm hE
    _ = ∫⁻ _, (0 : ℝ≥0∞) ∂Measure.map Y (stableLocalLaw θ : Measure DLoc) := by
      have hsec (y : ℝ) : (fun x => (x, y)) ⁻¹' E = {c - y} := by
        ext x
        simp only [Set.mem_preimage, Set.mem_singleton_iff, E]
        constructor
        · intro h
          change x + y = c at h
          linarith
        · intro h
          change x = c - y at h
          change x + y = c
          linarith
      simp_rw [hsec]
      rw [hmapX]
      congr 1
      funext y
      exact stableLawAt_singleton hθ ha (c-y)
    _ = 0 := lintegral_zero

private lemma exists_rat_split_runningInf_walk {f : DLoc} {t : ℝ≥0} {c : ℝ}
    (h0 : f.1 0 = 0) (hc : c < 0) (hIc : runningInfLoc f t = c) :
    ∃ q : ℚ, 0 < q ∧ (q : ℝ) < (t : ℝ) ∧
      f.1 (Real.toNNReal q) + runningInfLoc (DLoc.shift (Real.toNNReal q) f)
        (t - Real.toNNReal q) = c := by
  have hev : ∀ᶠ u in 𝓝[>] (0 : ℝ≥0), c / 2 < f.1 u :=
    (f.2.isRightContinuous 0).eventually (isOpen_Ioi.mem_nhds (by
      show c / 2 < f.1 0
      rw [h0]
      linarith))
  obtain ⟨b, hb, hbmem⟩ := (nhdsGT_basis (0 : ℝ≥0)).mem_iff.mp hev
  have hclt : c < c / 2 := by linarith
  have hIlt : runningInfLoc f t < c / 2 := by rw [hIc]; exact hclt
  obtain ⟨u, hut, hu⟩ := exists_eval_lt_of_runningInfLoc_lt hIlt
  have hu0 : 0 < u := by
    apply pos_iff_ne_zero.mpr
    intro huzero
    subst u
    rw [h0] at hu
    linarith
  have hqt : 0 < min (b : ℝ) (u : ℝ) := lt_min hb hu0
  obtain ⟨q, hq0, hq⟩ := exists_rat_btwn hqt
  have hq0R : (0 : ℝ) ≤ q := hq0.le
  have hqb : (q : ℝ) < (b : ℝ) := hq.trans_le (min_le_left _ _)
  have hqu : (q : ℝ) < (u : ℝ) := hq.trans_le (min_le_right _ _)
  let a : ℝ≥0 := Real.toNNReal q
  have hq0Q : (0 : ℚ) < q := by exact_mod_cast hq0
  have ha0 : 0 < a := Real.toNNReal_pos.mpr hq0
  have haR : (a : ℝ) = (q : ℝ) := Real.coe_toNNReal q hq0R
  have haut : a ≤ t := by
    rw [← NNReal.coe_le_coe, haR]
    exact (hqu.trans_le (by exact_mod_cast hut)).le
  have hsmall {v : ℝ≥0} (hvq : v ≤ a) : c / 2 < f.1 v := by
    have hva : (v : ℝ) ≤ (a : ℝ) := by exact_mod_cast hvq
    rw [haR] at hva
    have hvb : v < b := by
      rw [← NNReal.coe_lt_coe]
      exact hva.trans_lt hqb
    by_cases hvzero : v = 0
    · subst v
      rw [h0]
      linarith
    · have hvpos : 0 < v := pos_iff_ne_zero.mpr hvzero
      exact hbmem ⟨hvpos, hvb⟩
  have hcI : c < runningInfLoc f a := by
    have hfrac : c / 2 ≤ runningInfLoc f a := by
      apply le_runningInfLoc
      intro v
      exact (hsmall v.2).le
    exact hclt.trans_le hfrac
  have hdecomp := runningInfLoc_add_walk f a (t - a)
  rw [add_tsub_cancel_of_le haut, hIc] at hdecomp
  refine ⟨q, hq0Q, ?_, ?_⟩
  · exact hqu.trans_le (by exact_mod_cast hut)
  · change f.1 a + runningInfLoc (DLoc.shift a f) (t - a) = c
    by_contra hne
    have hcright : c ≤ f.1 a + runningInfLoc (DLoc.shift a f) (t - a) := by
      exact hdecomp.le.trans (min_le_right _ _)
    have hright : c < f.1 a + runningInfLoc (DLoc.shift a f) (t - a) :=
      lt_of_le_of_ne hcright (Ne.symm hne)
    have : c < min (runningInfLoc f a)
        (f.1 a + runningInfLoc (DLoc.shift a f) (t - a)) := lt_min hcI hright
    linarith [hdecomp, lt_min hcI hright]

/-- **`runningInf_noAtoms`**: for `t > 0` the running infimum `I_t = inf_{u ≤ t} X_u` has no
atoms. For `c > 0` this is empty (`I_t ≤ X_0 = 0`); for `c = 0` it follows from regularity of
`0`; for `c < 0`, `I_t = inf_{[a,t]} X` for some rational `a > 0` and
`X_a + inf_u (X_{a+u} - X_a)` is a sum with an independent atom-free (density) first term. -/
theorem runningInf_noAtoms {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0} (ht : 0 < t) (c : ℝ) :
    (stableLocalLaw θ : Measure DLoc) {f | runningInfLoc f t = c} = 0 := by
  rcases lt_trichotomy c 0 with hc | hc | hc
  · let E : ℚ → Set DLoc := fun q =>
      if 0 < q ∧ (q : ℝ) < (t : ℝ) then
        {f | f.1 (Real.toNNReal q) + runningInfLoc (DLoc.shift (Real.toNNReal q) f)
          (t - Real.toNNReal q) = c}
      else ∅
    have hE (q : ℚ) : (stableLocalLaw θ : Measure DLoc) (E q) = 0 := by
      by_cases hq : 0 < q ∧ (q : ℝ) < (t : ℝ)
      · have hqR : (0 : ℝ) < q := by exact_mod_cast hq.1
        have hq0 : 0 < Real.toNNReal q := Real.toNNReal_pos.mpr hqR
        simp only [E, hq]
        exact measure_add_runningInf_shift_eq_zero_walk hθ hq0 c
      · simp [E, hq]
    have hEzero : (stableLocalLaw θ : Measure DLoc) (⋃ q, E q) = 0 :=
      measure_iUnion_null hE
    have hstart : (stableLocalLaw θ : Measure DLoc) {f | f.1 0 ≠ 0} = 0 := by
      rw [← ae_iff]
      filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
      exact hf
    apply measure_mono_null ?_ (measure_union_null hEzero hstart)
    intro f hf
    by_cases h0 : f.1 0 = 0
    · obtain ⟨q, hq0, hqt, hq⟩ := exists_rat_split_runningInf_walk h0 hc hf
      apply Or.inl
      apply Set.mem_iUnion.mpr
      refine ⟨q, ?_⟩
      simp only [E, hq0, hqt, and_self]
      exact hq
    · exact Or.inr h0
  · subst c
    rw [show {f : DLoc | runningInfLoc f t = 0} = {f | ¬ runningInfLoc f t ≠ 0} by
      ext f; simp, ← ae_iff]
    filter_upwards [ae_regularBelowAtZero_stableLocalLaw hθ] with f hf
    obtain ⟨u, hu0, hut, hu⟩ := hf t ht
    have hle := (runningInfLoc_le_eval f t ⟨u, hut.le⟩).trans_lt hu
    intro hzero
    rw [hzero] at hle
    exact (lt_irrefl 0) hle
  · rw [show {f : DLoc | runningInfLoc f t = c} = {f | ¬ runningInfLoc f t ≠ c} by
      ext f; simp, ← ae_iff]
    filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
    have hle : runningInfLoc f t ≤ 0 := by
      have h := runningInfLoc_le_eval f t ⟨0, by simp⟩
      rw [hf] at h
      exact h
    intro hpos
    rw [hpos] at hle
    exact (not_le_of_gt hc) hle

/-- The running infimum of a local path agrees with the infimum of its compact restriction. -/
theorem iInf_restrict_stablePath (f : DLoc) (T : ℝ≥0) :
    (⨅ s : Set.Icc (0 : ℝ) (T : ℝ), (DLoc.restrict T f) s) = runningInfLoc f T := by
  let _ : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, le_rfl, T.2⟩⟩
  apply le_antisymm
  · apply le_ciInf
    intro u
    let s : Set.Icc (0 : ℝ) (T : ℝ) := ⟨u, u.1.2, by exact_mod_cast u.2⟩
    exact ciInf_le ((isBounded_range (DLoc.restrict T f)).bddBelow) s
  · apply le_ciInf
    intro s
    let u : Set.Iic T := ⟨(s : ℝ).toNNReal, by
      change (s : ℝ).toNNReal ≤ T
      rw [← NNReal.coe_le_coe, Real.coe_toNNReal _ s.2.1]
      exact_mod_cast s.2.2⟩
    have hv := ciInf_le (bddBelow_runningInf_range f T) u
    have hs : (DLoc.restrict T f) s = f.1 (s : ℝ).toNNReal := by
      apply congrArg f.1
      apply Subtype.ext
      exact (Real.coe_toNNReal _ s.2.1).symm
    rw [hs]
    exact hv

/-- The fixed-horizon form on `D T ℝ`, the one consumed with `StableDomain.tendsto_stepPathLaw`:
the law of `inf_{s ≤ T} g s` under `stableProcessLaw θ T` has no atoms. -/
theorem iInf_noAtoms_stableProcessLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {T : ℝ} (hT : 0 < T) (c : ℝ) :
    (stableProcessLaw θ T : Measure (D T ℝ)) {g | (⨅ s : Set.Icc (0 : ℝ) T, g s) = c} = 0 := by
  let Tnn : ℝ≥0 := T.toNNReal
  have hTnn : 0 < Tnn := Real.toNNReal_pos.mpr hT
  have hTR : (Tnn : ℝ) = T := Real.coe_toNNReal T hT.le
  have hmap := map_restrict_stableLocalLaw (θ := θ) hθ hTnn
  rw [← hTR]
  have hset : MeasurableSet {g : D (Tnn : ℝ) ℝ |
      (⨅ s : Set.Icc (0 : ℝ) (Tnn : ℝ), g s) = c} :=
    measurableSet_eq_fun
      ((lipschitzWith_one_iInf (T := (Tnn : ℝ)) Tnn.2).continuous.measurable) measurable_const
  have heq : (stableProcessLaw θ (Tnn : ℝ) : Measure (D (Tnn : ℝ) ℝ))
      {g | (⨅ s : Set.Icc (0 : ℝ) (Tnn : ℝ), g s) = c} =
      (stableLocalLaw θ : Measure DLoc) {f | runningInfLoc f Tnn = c} := by
    rw [← hmap, Measure.map_apply (DLoc.measurable_restrict Tnn) hset]
    congr 1
    ext f
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [iInf_restrict_stablePath f Tnn]
  rw [heq]
  exact runningInf_noAtoms hθ hTnn c

/-- **CDF of the passage time through the running infimum** (strict vs weak resolved by
`runningInf_noAtoms`): for `x ≥ 0`, `t > 0`,
`P(T_x ≤ t) = P(I_t ≤ -x) = P(I_t < -x)`. -/
theorem passageLaw_Iic_eq_runningInf {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ≥0) {t : ℝ≥0}
    (ht : 0 < t) :
    passageLaw θ x (Iic (t : ℝ)) =
        (stableLocalLaw θ : Measure DLoc) {f | runningInfLoc f t ≤ -(x : ℝ)} ∧
      (stableLocalLaw θ : Measure DLoc) {f | runningInfLoc f t ≤ -(x : ℝ)} =
        (stableLocalLaw θ : Measure DLoc) {f | runningInfLoc f t < -(x : ℝ)} := by
  let P : Measure DLoc := stableLocalLaw θ
  let E : Set DLoc := {f | ((passageTime x f : ℝ≥0) : ℝ) ≤ (t : ℝ)}
  let F : Set DLoc := {f | runningInfLoc f t < -(x : ℝ)}
  let G : Set DLoc := {f | runningInfLoc f t ≤ -(x : ℝ)}
  have hne : ∀ᵐ f ∂P, runningInfLoc f t ≠ -(x : ℝ) := by
    rw [ae_iff]
    simpa only [not_not] using runningInf_noAtoms hθ ht (-(x : ℝ))
  have hEG : E =ᵐ[P] G := by
    filter_upwards [ae_passageTime_eq_firstPassageBelow hθ,
      ae_runningInf_le_of_firstPassageBelow_le hθ, hne] with f hfin hInf hn
    have hcoe : firstPassageBelow x f = (passageTime x f : WithTop ℝ≥0) := hfin.1 x
    have hT_le : firstPassageBelow x f ≤ (t : WithTop ℝ≥0) ↔
        ((passageTime x f : ℝ≥0) : ℝ) ≤ (t : ℝ) := by
      rw [hcoe]
      exact WithTop.coe_le_coe
    apply propext
    change (((passageTime x f : ℝ≥0) : ℝ) ≤ (t : ℝ)) ↔ runningInfLoc f t ≤ -(x : ℝ)
    constructor
    · intro htime
      have hle := hInf x t (hT_le.mpr htime)
      exact lt_of_le_of_ne hle hn |>.le
    · intro hle
      rcases hle.eq_or_lt with heq | hlt
      · exact (hn heq).elim
      · have hpass := (runningInfLoc_lt_sandwich x t f).2 hlt
        exact hT_le.mp hpass
  have hFG : G =ᵐ[P] F := by
    filter_upwards [hne] with f hn
    apply propext
    change runningInfLoc f t ≤ -(x : ℝ) ↔ runningInfLoc f t < -(x : ℝ)
    exact ⟨fun hle => lt_of_le_of_ne hle hn, le_of_lt⟩
  have hmap : passageLaw θ x (Iic (t : ℝ)) = P E := by
    rw [passageLaw, Measure.map_apply (measurable_passageTime x).coe_nnreal_real measurableSet_Iic]
    rfl
  exact ⟨hmap.trans (measure_congr hEG), measure_congr hFG⟩

end BGW.StableTrees
