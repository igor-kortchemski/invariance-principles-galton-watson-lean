/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.DLocBasic
public import BGW.Skorokhod.PathLawFamily

/-!
# Compatible families for the local càdlàg path space

This module extends the basic `DLoc` API with the measurable equivalence between local càdlàg
paths and compatible families of restrictions to integer horizons. It also proves that finite
laws on `DLoc` are determined by these restrictions.

The construction uses `PathLawFamily`; the law-independent carrier, filtrations, and passage
times are provided by `DLocBasic`.
-/

@[expose] public section

open MeasureTheory Set Filter Topology MeasureTheory.Filtration
open scoped NNReal

namespace BGW.Skorokhod

namespace DLoc

private def extendPath (T : ℝ≥0) (f : D (T : ℝ) ℝ) : DLoc := by
  let κ : ℝ≥0 → Set.Icc (0 : ℝ) (T : ℝ) := fun u =>
    ⟨min (u : ℝ) T, le_min u.2 T.2, min_le_right _ _⟩
  have hκ : Continuous κ := Continuous.subtype_mk
    (continuous_subtype_val.min continuous_const) fun u => ⟨le_min u.2 T.2, min_le_right _ _⟩
  refine ⟨fun u => f (κ u), ?_⟩
  constructor
  · intro t
    by_cases ht : (t : ℝ) < T
    · have hmap : MapsTo κ (Set.Ioi t) (Set.Ioi (κ t)) := by
        intro u hu
        change (t : ℝ) < (u : ℝ) at hu
        change (κ t : ℝ) < (κ u : ℝ)
        simp only [κ, min_eq_left ht.le]
        exact (lt_min_iff.mpr ⟨hu, ht⟩)
      exact f.2.isRightContinuous (κ t) |>.comp
        hκ.continuousAt.continuousWithinAt hmap
    · have htT : T ≤ (t : ℝ) := le_of_not_gt ht
      have hconst : ∀ u ∈ Set.Ioi t, κ u = κ t := by
        intro u hu
        change (t : ℝ) < (u : ℝ) at hu
        apply Subtype.ext
        simp [κ, min_eq_right htT, min_eq_right (htT.trans hu.le)]
      exact tendsto_nhdsWithin_congr (fun u hu => congrArg f (hconst u hu).symm)
        tendsto_const_nhds
  · intro t
    by_cases ht : (t : ℝ) ≤ T
    · have hmap : MapsTo κ (Set.Iio t) (Set.Iio (κ t)) := by
        intro u hu
        change (u : ℝ) < (t : ℝ) at hu
        have huT : (u : ℝ) ≤ T := hu.le.trans ht
        change (κ u : ℝ) < (κ t : ℝ)
        simp only [κ, min_eq_left huT, min_eq_left ht]
        exact hu
      obtain ⟨l, hl⟩ := f.2.tendsto_nhdsLT (κ t)
      have hκleft : Tendsto κ (𝓝[Set.Iio t] t) (𝓝[Set.Iio (κ t)] (κ t)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨tendsto_nhdsWithin_of_tendsto_nhds hκ.continuousAt, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact hmap hu
      exact ⟨l, hl.comp hκleft⟩
    · have htT : T < t := by exact_mod_cast (lt_of_not_ge ht)
      have hev : ∀ᶠ u in 𝓝[Set.Iio t] t, T < u :=
        (eventually_gt_nhds htT).filter_mono nhdsWithin_le_nhds
      have hconst : ∀ u : ℝ≥0, T < u → κ u = κ t := by
        intro u hu
        apply Subtype.ext
        have hu' : (T : ℝ) ≤ (u : ℝ) := by exact_mod_cast hu.le
        simp [κ, min_eq_right hu', min_eq_right (show (T : ℝ) ≤ (t : ℝ) from htT.le)]
      have hfg : (fun u : ℝ≥0 => f (κ u)) =ᶠ[𝓝[Set.Iio t] t]
          fun _ => f (κ t) := by
        filter_upwards [hev] with u hu
        exact congrArg f (hconst u hu)
      exact ⟨f (κ t), (tendsto_congr' hfg).2 tendsto_const_nhds⟩

/-- The compatible integer-horizon family of a local path (horizons `n + 1`). -/
def toCompatible (f : DLoc) : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1)
    strictMono_succHorizon :=
  ⟨fun n => restrict ⟨(n : ℝ) + 1, by positivity⟩ f, by
    intro n
    exact BGW.Skorokhod.ext (fun t => rfl)⟩

private noncomputable def glueValue
    (p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon)
    (t : ℝ≥0) : ℝ :=
  (p.1 ⌈(t : ℝ)⌉₊) ⟨t, t.2, by
    have hceil : (t : ℝ) ≤ (⌈(t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    linarith⟩

private theorem compatible_eval_le
    (p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon)
    (k N : ℕ) (hkn : k ≤ N) (u : ℝ≥0) (hu : (u : ℝ) ≤ (k : ℝ) + 1) :
    (p.1 k) ⟨u, u.2, hu⟩ = (p.1 N) ⟨u, u.2, by
      have hcast : (k : ℝ) ≤ N := by exact_mod_cast hkn
      linarith⟩ := by
  induction N, hkn using Nat.le_induction with
  | base => rfl
  | succ N hKN ih =>
      let uN : Set.Icc (0 : ℝ) ((N : ℝ) + 1) :=
        ⟨u, u.2, by
          have hcast : (k : ℝ) ≤ N := by exact_mod_cast hKN
          linarith⟩
      let uNSucc : Set.Icc (0 : ℝ) (((N + 1 : ℕ) : ℝ) + 1) := by
        have hcast : (k : ℝ) ≤ N + 1 := by exact_mod_cast Nat.le_succ_of_le hKN
        exact ⟨u, u.2, by norm_num at hcast ⊢; linarith [hu, hcast]⟩
      have hstep := p.2 N
      have hstepAt := congrArg (fun q : D ((N : ℝ) + 1) ℝ => q uN) hstep
      have hstepAt' : (p.1 (N + 1)) uNSucc = (p.1 N) uN := by
        calc
          (p.1 (N + 1)) uNSucc =
              (BGW.Skorokhod.restrict
                (show (N : ℝ) + 1 ≤ (N + 1 : ℕ) + 1 from by norm_num)
                (p.1 (N + 1))) uN := rfl
          _ = (p.1 N) uN := hstepAt
      have huNSucc : uNSucc =
          (⟨u, u.2, by
            have hcast : (k : ℝ) ≤ N + 1 := by exact_mod_cast Nat.le_succ_of_le hKN
            norm_num at hcast ⊢
            linarith [hu, hcast]⟩ : Set.Icc (0 : ℝ) (((N + 1 : ℕ) : ℝ) + 1)) := by
        apply Subtype.ext
        rfl
      calc
        (p.1 k) ⟨u, u.2, hu⟩ = (p.1 N) uN := ih
        _ = (p.1 (N + 1)) uNSucc := hstepAt'.symm
        _ = (p.1 (N + 1)) _ := congrArg (p.1 (N + 1)) huNSucc

private theorem glueValue_eq_extendPath
    (p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon)
    (N : ℕ) (u : ℝ≥0) (hu : u < N) :
    glueValue p u = (extendPath ⟨(N : ℝ) + 1, by positivity⟩ (p.1 N)).1 u := by
  let k : ℕ := ⌈(u : ℝ)⌉₊
  have hkn : k ≤ N := by
    apply Nat.ceil_le.mpr
    exact_mod_cast hu.le
  have huk : (u : ℝ) ≤ (k : ℝ) + 1 := by
    have hceil : (u : ℝ) ≤ (k : ℝ) := by
      dsimp [k]
      exact Nat.le_ceil _
    linarith
  have hval := compatible_eval_le p k N hkn u huk
  have hT : (u : ℝ) ≤ (N : ℝ) + 1 := by
    have hu' : (u : ℝ) ≤ (N : ℝ) := by exact_mod_cast hu.le
    linarith
  let x : Set.Icc (0 : ℝ) ((N : ℝ) + 1) := ⟨u, u.2, hT⟩
  let T : ℝ≥0 := ⟨(N : ℝ) + 1, by positivity⟩
  have hT' : (u : ℝ) ≤ (T : ℝ) := by
    change (u : ℝ) ≤ (N : ℝ) + 1
    exact hT
  have hext : (extendPath T (p.1 N)).1 u = (p.1 N) x := by
    dsimp [extendPath]
    apply congrArg (p.1 N)
    apply Subtype.ext
    change min (u : ℝ) (T : ℝ) = (u : ℝ)
    exact min_eq_left hT'
  calc
    glueValue p u = (p.1 N) x := by simpa [glueValue, k, x] using hval
    _ = (extendPath T (p.1 N)).1 u := hext.symm

/-- Gluing: a compatible integer-horizon family determines a local càdlàg path. -/
noncomputable def glue
    (p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon) : DLoc :=
  ⟨fun t => (p.1 ⌈(t : ℝ)⌉₊) ⟨t, t.2, by
    have hceil : (t : ℝ) ≤ (⌈(t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
    linarith⟩, by
    have hcad : IsCadlag (glueValue p) := by
      constructor
      · intro t
        let N : ℕ := ⌈(t : ℝ)⌉₊ + 1
        have htN : t < (N : ℝ≥0) := by
          have htN' : (t : ℝ) < (N : ℝ) := by
            dsimp [N]
            have hceil : (t : ℝ) ≤ (⌈(t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
            norm_num
            linarith
          exact_mod_cast htN'
        let T : ℝ≥0 := ⟨(N : ℝ) + 1, by positivity⟩
        let e : DLoc := extendPath T (p.1 N)
        have hpoint : glueValue p t = e.1 t := glueValue_eq_extendPath p N t htN
        have heq : (fun u : ℝ≥0 => glueValue p u) =ᶠ[𝓝[Set.Ioi t] t] e.1 := by
          have hup : ∀ᶠ u in 𝓝[Set.Ioi t] t, u < (N : ℝ≥0) :=
            (eventually_lt_nhds htN).filter_mono nhdsWithin_le_nhds
          filter_upwards [hup] with u hu
          exact glueValue_eq_extendPath p N u hu
        change Tendsto (glueValue p) (𝓝[Set.Ioi t] t) (𝓝 (glueValue p t))
        rw [hpoint]
        exact (tendsto_congr' heq).2 (e.2.isRightContinuous t)
      · intro t
        let N : ℕ := ⌈(t : ℝ)⌉₊ + 1
        have htN : t < (N : ℝ≥0) := by
          have htN' : (t : ℝ) < (N : ℝ) := by
            dsimp [N]
            have hceil : (t : ℝ) ≤ (⌈(t : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
            norm_num
            linarith
          exact_mod_cast htN'
        let T : ℝ≥0 := ⟨(N : ℝ) + 1, by positivity⟩
        let e : DLoc := extendPath T (p.1 N)
        obtain ⟨l, hl⟩ := e.2.tendsto_nhdsLT t
        have heq : (fun u : ℝ≥0 => glueValue p u) =ᶠ[𝓝[Set.Iio t] t] e.1 := by
          have hup : ∀ᶠ u in 𝓝[Set.Iio t] t, u < (N : ℝ≥0) :=
            (eventually_lt_nhds htN).filter_mono nhdsWithin_le_nhds
          filter_upwards [hup] with u hu
          exact glueValue_eq_extendPath p N u hu
        exact ⟨l, (tendsto_congr' heq).2 hl⟩
    change IsCadlag (glueValue p)
    exact hcad⟩

/-- Gluing restricts back to the family. -/
theorem restrict_glue
    (p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon)
    (n : ℕ) (t : Set.Icc (0 : ℝ) ((n : ℝ) + 1)) :
    (glue p).1 ⟨t.1, t.2.1⟩ = p.1 n t := by
  let u : ℝ≥0 := ⟨t, t.2.1⟩
  let k : ℕ := ⌈(t : ℝ)⌉₊
  have hkn : k ≤ n + 1 := by
    apply Nat.ceil_le.mpr
    exact_mod_cast t.2.2
  have huBound : (u : ℝ) ≤ (n : ℝ) + 1 := by
    exact_mod_cast t.2.2
  have huk : (u : ℝ) ≤ (k : ℝ) + 1 := by
    have hceil : (u : ℝ) ≤ (k : ℝ) := by
      dsimp [u, k]
      exact Nat.le_ceil _
    linarith
  have hval := compatible_eval_le p k (n + 1) hkn u huk
  have hstepAt : (p.1 (n + 1)) ⟨u, u.2, by
      have hcast : (n : ℝ) ≤ n + 1 := by exact_mod_cast Nat.le_succ n
      norm_num
      linarith [huBound]⟩ = p.1 n t := by
    have hstep := congrArg (fun q : D ((n : ℝ) + 1) ℝ => q t) (p.2 n)
    calc
      (p.1 (n + 1)) ⟨u, u.2, by
          have hcast : (n : ℝ) ≤ n + 1 := by exact_mod_cast Nat.le_succ n
          norm_num
          linarith [huBound]⟩ =
          (BGW.Skorokhod.restrict
            (show (n : ℝ) + 1 ≤ (n + 1 : ℕ) + 1 from by norm_num)
            (p.1 (n + 1))) t := rfl
      _ = p.1 n t := hstep
  change glueValue p u = p.1 n t
  calc
    glueValue p u = (p.1 k) ⟨u, u.2, huk⟩ := by
      dsimp [glueValue, k]
      rfl
    _ = (p.1 (n + 1)) ⟨u, u.2, by
        have hcast : (n : ℝ) ≤ n + 1 := by exact_mod_cast Nat.le_succ n
        norm_num
        linarith [huBound]⟩ := hval
    _ = p.1 n t := hstepAt

/-- The gluing is inverted by the family of restrictions. -/
theorem glue_toCompatible (f : DLoc) : glue (toCompatible f) = f := by
  apply Subtype.ext
  funext t
  let n : ℕ := ⌈(t : ℝ)⌉₊
  have ht : (t : ℝ) ≤ (n : ℝ) + 1 := by
    have hceil : (t : ℝ) ≤ (n : ℝ) := by dsimp [n]; exact Nat.le_ceil _
    linarith
  let t' : Set.Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨t, t.2, ht⟩
  have h := restrict_glue (toCompatible f) n t'
  change (glue (toCompatible f)).1 t = (toCompatible f).1 n t' at h
  have h' : (toCompatible f).1 n t' = f.1 t := by rfl
  exact h.trans h'

/-- Restricting a glued family recovers the compatible family. -/
theorem toCompatible_glue
    (p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon) :
    toCompatible (glue p) = p := by
  apply Subtype.ext
  funext n
  apply BGW.Skorokhod.ext
  intro t
  change (glue p).1 ⟨t, t.2.1⟩ = p.1 n t
  exact restrict_glue p n t

private theorem measurable_toCompatible : Measurable toCompatible := by
  apply Measurable.subtype_mk
  exact Measurable.of_eval fun n =>
    measurable_restrict ⟨(n : ℝ) + 1, by positivity⟩

private def castCompactPath {T U : ℝ} (h : T = U) (f : D T ℝ) : D U ℝ := h ▸ f

private theorem measurable_castCompactPath {T U : ℝ} (h : T = U) :
    Measurable (castCompactPath h : D T ℝ → D U ℝ) := by
  cases h
  exact measurable_id

private theorem castCompactPath_apply {T U : ℝ} (h : T = U) (f : D T ℝ)
    (t : Set.Icc (0 : ℝ) U) :
    castCompactPath h f t = f ⟨t, t.2.1, by simpa [h] using t.2.2⟩ := by
  cases h
  rfl

/-- `DLoc` is measurably equivalent to the compatible families of restrictions to `[0, n + 1]`,
so laws constructed in `PathLawFamily` transfer to `DLoc`. -/
noncomputable def measurableEquivCompatible :
    DLoc ≃ᵐ CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon where
  toEquiv := ⟨toCompatible, glue, glue_toCompatible, toCompatible_glue⟩
  measurable_toFun := by
    apply Measurable.subtype_mk
    exact Measurable.of_eval fun n =>
      measurable_restrict ⟨(n : ℝ) + 1, by positivity⟩
  measurable_invFun := by
    rw [measurable_iff_comap_le]
    change (⨆ t : ℝ≥0, MeasurableSpace.comap (eval t) inferInstance).comap glue ≤ _
    rw [MeasurableSpace.comap_iSup, iSup_le_iff]
    intro t
    let n : ℕ := ⌈(t : ℝ)⌉₊
    have ht : (t : ℝ) ≤ (n : ℝ) + 1 := by
      have hceil : (t : ℝ) ≤ (n : ℝ) := by dsimp [n]; exact Nat.le_ceil _
      linarith
    let t' : Set.Icc (0 : ℝ) ((n : ℝ) + 1) := ⟨t, t.2, ht⟩
    have hval : (fun p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1)
        strictMono_succHorizon => eval t (glue p)) = fun p => (p.1 n) t' := by
      funext p
      change (glue p).1 t = (p.1 n) t'
      exact restrict_glue p n t'
    rw [MeasurableSpace.comap_comp]
    change MeasurableSpace.comap
        (fun p : CompatiblePaths (fun n : ℕ => (n : ℝ) + 1)
          strictMono_succHorizon => eval t (glue p)) inferInstance ≤ _
    rw [hval]
    exact (BGW.Skorokhod.measurable_eval t').comp
      (BGW.Skorokhod.CompatiblePaths.measurable_coord
        (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon n) |>.comap_le

/-- Two finite measures with equal restrictions to every integer horizon are equal. -/
theorem measure_ext_of_restrict {P Q : Measure DLoc} [IsFiniteMeasure P]
    (h : ∀ n : ℕ, P.map (restrict (n : ℝ≥0)) = Q.map (restrict (n : ℝ≥0))) : P = Q := by
  have hcoord : ∀ n : ℕ,
      ((P.map toCompatible).map (CompatiblePaths.coord (b := fun n : ℕ => (n : ℝ) + 1)
        (hb := strictMono_succHorizon) n)) =
      ((Q.map toCompatible).map (CompatiblePaths.coord (b := fun n : ℕ => (n : ℝ) + 1)
        (hb := strictMono_succHorizon) n)) := by
    intro n
    let hT : (((n + 1 : ℕ) : ℝ≥0) : ℝ) = (n : ℝ) + 1 := by norm_num
    let c : D (((n + 1 : ℕ) : ℝ≥0) : ℝ) ℝ → D ((n : ℝ) + 1) ℝ :=
      castCompactPath hT
    have hc : Measurable c := measurable_castCompactPath hT
    have hfactor : CompatiblePaths.coord (b := fun n : ℕ => (n : ℝ) + 1)
        (hb := strictMono_succHorizon) n ∘ toCompatible =
        c ∘ restrict ((n + 1 : ℕ) : ℝ≥0) := by
      funext f
      apply BGW.Skorokhod.ext
      intro t
      change (toCompatible f).1 n t =
        castCompactPath hT (restrict ((n + 1 : ℕ) : ℝ≥0) f) t
      rw [castCompactPath_apply]
      rfl
    have hrestr : P.map (c ∘ restrict ((n + 1 : ℕ) : ℝ≥0)) =
        Q.map (c ∘ restrict ((n + 1 : ℕ) : ℝ≥0)) := by
      simpa only [Measure.map_map hc (measurable_restrict ((n + 1 : ℕ) : ℝ≥0))] using
        congrArg (fun μ : Measure (D (((n + 1 : ℕ) : ℝ≥0) : ℝ) ℝ) => μ.map c)
          (h (n + 1))
    simp only [Measure.map_map
      (BGW.Skorokhod.CompatiblePaths.measurable_coord
        (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon n)
      measurable_toCompatible]
    simpa only [hfactor] using hrestr
  have hcompatible := BGW.Skorokhod.CompatiblePaths.measure_ext
    (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon
    (Q := P.map toCompatible) (Q' := Q.map toCompatible) hcoord
  have hmap := congrArg (fun μ : Measure
      (CompatiblePaths (fun n : ℕ => (n : ℝ) + 1) strictMono_succHorizon) => μ.map glue)
    hcompatible
  have hmeasGlue : Measurable glue := measurableEquivCompatible.measurable_invFun
  have hleft : (P.map toCompatible).map glue = P := by
    rw [Measure.map_map hmeasGlue measurable_toCompatible]
    simp [Function.comp_def, glue_toCompatible]
  have hright : (Q.map toCompatible).map glue = Q := by
    rw [Measure.map_map hmeasGlue measurable_toCompatible]
    simp [Function.comp_def, glue_toCompatible]
  exact hleft.symm.trans (hmap.trans hright)


end DLoc

end BGW.Skorokhod
