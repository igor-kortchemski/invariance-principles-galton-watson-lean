/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTimePublic
public import BGW.StableTrees.StableProcessReversal
public import Mathlib.MeasureTheory.Measure.Stieltjes

/-!
# Height approximations and reversal

The height approximation uses future interval infima. Reversal is extended constantly
beyond its horizon, with the left-limit convention of `reverseIncrements`.

This module supplies the deterministic and measurability part of H02. The occupation-limit,
ancestral, support, positive-erasure and restart theorems of the H02 contract remain open.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- The interval infimum `I^s_t = inf_{[s ∧ t, t]} X`. -/
noncomputable def futureInf (f : DLoc) (t s : ℝ≥0) : ℝ := ⨅ u : Set.Icc (min s t) t, f.1 u

/-- Minimal-exploration occupation approximation `ε⁻¹ Leb{s ≤ t | X_s < I^s_t + ε}`. -/
noncomputable def heightApprox (ε : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  ε⁻¹ * (volume {s : ℝ | 0 ≤ s ∧ s ≤ (t : ℝ) ∧
    f.1 s.toNNReal < futureInf f t s.toNNReal + ε}).toReal

/-- The time-reversed process at `t`: `u ↦ X_t - X_{(t - u ∧ t)-}` (constant after `t`). -/
noncomputable def reversedPath (t : ℝ≥0) (f : DLoc) : ℝ≥0 → ℝ :=
  fun u => f.1 t - Function.leftLim f.1 (t - min u t)

private theorem tendsto_leftLim_right {g : ℝ≥0 → ℝ} {a : ℝ≥0}
    (h : Tendsto g (𝓝[>] a) (𝓝 (g a))) :
    Tendsto (Function.leftLim g) (𝓝[>] a) (𝓝 (g a)) := by
  apply (closed_nhds_basis (g a)).tendsto_right_iff.2
  rintro S ⟨hS, hclosed⟩
  obtain ⟨c, hac, hc⟩ :=
    (mem_nhdsGT_iff_exists_Ioo_subset' (lt_add_one a)).mp (h.eventually hS)
  filter_upwards [Ioo_mem_nhdsGT hac] with x hx
  apply hclosed.mem_of_mapClusterPt (mapClusterPt_leftLim g x)
  filter_upwards [Ioo_mem_nhdsLE_of_mem hx] with y hy using hc hy

/-- The reversed path is càdlàg (so `reversedAt` is never junk). -/
theorem isCadlag_reversedPath (t : ℝ≥0) (f : DLoc) : IsCadlag (reversedPath t f) := by
  have he : reversedPath t f = fun u => f.1 t - Function.leftLim f.1 (t - u) := by
    funext u
    simp [reversedPath, min_comm u t, tsub_min]
  rw [he]
  have hr (u : ℝ≥0) : ContinuousAt (fun v : ℝ≥0 => t - v) u :=
    (continuous_const.sub continuous_id).continuousAt
  constructor
  · intro u
    have hrev : Tendsto (fun v : ℝ≥0 => t - v) (𝓝[>] u) (𝓝[≤] (t - u)) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(hr u).mono_left nhdsWithin_le_nhds, ?_⟩
      filter_upwards [self_mem_nhdsWithin] with v hv
      change t - v ≤ t - u
      exact tsub_le_tsub_left (show u ≤ v from hv.le) t
    exact tendsto_const_nhds.sub
      ((continuousWithinAt_leftLim_Iic (f.2.tendsto_nhdsLT_leftLim (t - u))).tendsto.comp hrev)
  · intro u
    by_cases hut : u ≤ t
    · refine ⟨f.1 t - f.1 (t - u), ?_⟩
      have hrev : Tendsto (fun v : ℝ≥0 => t - v) (𝓝[<] u) (𝓝[>] (t - u)) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨(hr u).mono_left nhdsWithin_le_nhds, ?_⟩
        filter_upwards [self_mem_nhdsWithin] with v hv
        change t - u < t - v
        exact tsub_lt_tsub_left_of_le hut hv
      exact tendsto_const_nhds.sub ((tendsto_leftLim_right
        (f.2.isRightContinuous (t - u))).comp hrev)
    · have htu : t < u := lt_of_not_ge hut
      refine ⟨f.1 t - Function.leftLim f.1 0, ?_⟩
      have heq : (fun v : ℝ≥0 => f.1 t - Function.leftLim f.1 (t - v))
          =ᶠ[𝓝[<] u] fun _ => f.1 t - Function.leftLim f.1 0 := by
        filter_upwards [(eventually_gt_nhds htu).filter_mono nhdsWithin_le_nhds] with v hv
        rw [tsub_eq_zero_of_le hv.le]
      exact (tendsto_congr' heq).2 tendsto_const_nhds

open scoped Classical in
/-- The reversed process at `t` as a `DLoc` element (junk `DLoc.zero` never occurs). -/
noncomputable def reversedAt (t : ℝ≥0) (f : DLoc) : DLoc :=
  if h : IsCadlag (reversedPath t f) then ⟨reversedPath t f, h⟩ else DLoc.zero


private theorem leftLim_restrict (t : ℝ≥0) (f : DLoc)
    (s : Icc (0 : ℝ) (t : ℝ)) :
    Function.leftLim (DLoc.restrict t f) s = Function.leftLim f.1 ⟨s, s.2.1⟩ := by
  by_cases hs : (s : ℝ) = 0
  · have hbot : IsBot s := fun u => by change (s : ℝ) ≤ (u : ℝ); simpa [hs] using u.2.1
    have hs0 : (⟨s, s.2.1⟩ : ℝ≥0) = 0 := Subtype.ext hs
    have hz : Function.leftLim f.1 (0 : ℝ≥0) = f.1 0 :=
      leftLim_eq_of_isBot (show IsBot (0 : ℝ≥0) from fun _ => zero_le)
    erw [leftLim_eq_of_isBot hbot, hs0, hz]
    change f.1 ⟨s, s.2.1⟩ = f.1 0
    exact congrArg f.1 hs0
  · let inc : Icc (0 : ℝ) (t : ℝ) → ℝ≥0 := fun u => ⟨u, u.2.1⟩
    have hi : Continuous inc := Continuous.subtype_mk continuous_subtype_val _
    have hpos : 0 < (s : ℝ) := lt_of_le_of_ne s.2.1 (Ne.symm hs)
    have : (𝓝[<] s).NeBot := nhdsLT_neBot_of_exists_lt
      ⟨⟨0, le_rfl, t.2⟩, hpos⟩
    apply leftLim_eq_of_tendsto
    apply (f.2.tendsto_nhdsLT_leftLim (inc s)).comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hi.continuousAt.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with u hu
    exact hu

/-- The reversal fallback is excluded at every path and horizon. -/
theorem reversedAt_apply (t : ℝ≥0) (f : DLoc) (u : ℝ≥0) :
    (reversedAt t f).1 u = reversedPath t f u := by
  simp [reversedAt, isCadlag_reversedPath]

/-- On `[0,t]` the reversed path is the sealed `reverseIncrements` of the restriction. -/
theorem restrict_reversedAt (t : ℝ≥0) (f : DLoc) :
    DLoc.restrict t (reversedAt t f) = reverseIncrements t.2 (DLoc.restrict t f) := by
  ext u
  change (reversedAt t f).1 ⟨u, u.2.1⟩ = _
  erw [reversedAt_apply, reverseIncrements_apply, leftLim_restrict]
  unfold reversedPath
  congr 2
  apply Subtype.ext
  have hu : (⟨u, u.2.1⟩ : ℝ≥0) ≤ t := u.2.2
  erw [min_eq_left hu]
  exact NNReal.coe_sub hu

private theorem measurable_leftLim_uncurry :
    Measurable (fun p : DLoc × ℝ≥0 => Function.leftLim p.1.1 p.2) := by
  have hlim (f : DLoc) (t : ℝ≥0) :
      Tendsto (fun n : ℕ => f.1 (t - 1 / (n + 1 : ℝ≥0))) atTop
        (𝓝 (Function.leftLim f.1 t)) := by
    by_cases ht : t = 0
    · simp only [ht, zero_tsub, leftLim_eq_of_isBot isBot_zero]
      exact tendsto_const_nhds
    · have htpos : 0 < t := pos_iff_ne_zero.mpr ht
      apply (f.2.tendsto_nhdsLT_leftLim t).comp
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨?_, Eventually.of_forall fun n => tsub_lt_self htpos (by positivity)⟩
      simpa only [tsub_zero] using (tendsto_const_nhds (x := t)).sub
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))
  apply measurable_of_tendsto_metrizable
    (fun n : ℕ => DLoc.measurable_eval₂.comp
      (measurable_fst.prodMk (measurable_snd.sub measurable_const)))
  exact tendsto_pi_nhds.mpr fun p => hlim p.1 p.2

/-- `(t, f) ↦ reversedAt t f` is jointly measurable. -/
theorem measurable_reversedAt_uncurry :
    Measurable (fun p : ℝ≥0 × DLoc => reversedAt p.1 p.2) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap _ (⨆ u, MeasurableSpace.comap (DLoc.eval u) inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup, iSup_le_iff]
  intro u
  rw [MeasurableSpace.comap_comp]
  have hm : Measurable (fun p : ℝ≥0 × DLoc =>
      p.2.1 p.1 - Function.leftLim p.2.1 (p.1 - min u p.1)) :=
    (DLoc.measurable_eval₂.comp (measurable_snd.prodMk measurable_fst)).sub
      (measurable_leftLim_uncurry.comp
        (measurable_snd.prodMk (measurable_fst.sub (measurable_const.min measurable_fst))))
  simpa only [Function.comp_def, DLoc.eval, reversedAt_apply, reversedPath] using hm.comap_le

/-- **Law of the reversed prefix**: for each `t > 0`, reversal at `t` preserves the law of the
prefix `[0,t]` (sealed `map_reverseIncrements_stableProcessLaw`, transferred to `DLoc`). -/
theorem map_restrict_reversedAt_stableLocalLaw {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {t : ℝ≥0}
    (ht : 0 < t) :
    (stableLocalLaw θ : Measure DLoc).map (fun f => DLoc.restrict t (reversedAt t f)) =
      (stableLocalLaw θ : Measure DLoc).map (DLoc.restrict t) := by
  have he : (fun f => DLoc.restrict t (reversedAt t f)) =
      reverseIncrements t.2 ∘ DLoc.restrict t := funext (restrict_reversedAt t)
  erw [he, ← Measure.map_map (measurable_reverseIncrements t.2) (DLoc.measurable_restrict t),
    map_restrict_stableLocalLaw hθ ht]
  exact congrArg (fun P : ProbabilityMeasure (D (t : ℝ) ℝ) =>
    (P : Measure (D (t : ℝ) ℝ)))
    (map_reverseIncrements_stableProcessLaw hθ ht)

/-- **The height** `H_t = M_t(reversed process at t)`: the H01 supremum local time of the
time-reversed process. -/
noncomputable def height (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ :=
  supLocalTime θ (reversedAt t f) t

/-- The raw (extended-real) height: liminf of the approximations along `supEps θ`. -/
noncomputable def heightRaw (θ : ℝ) (f : DLoc) (t : ℝ≥0) : ℝ≥0∞ :=
  liminf (fun k => ENNReal.ofReal (heightApprox (supEps θ k) f t)) atTop

/-- Joint measurability of the chosen version `(t, f) ↦ H_t(f)`. -/
theorem measurable_height_uncurry (θ : ℝ) :
    Measurable (fun p : ℝ≥0 × DLoc => height θ p.2 p.1) := by
  change Measurable (fun p : ℝ≥0 × DLoc => supLocalTime θ (reversedAt p.1 p.2) p.1)
  have hm : Measurable (fun p : ℝ≥0 × DLoc => (p.1, reversedAt p.1 p.2)) :=
    measurable_fst.prodMk measurable_reversedAt_uncurry
  exact Measurable.comp (g := fun q : ℝ≥0 × DLoc => supLocalTime θ q.2 q.1)
    (f := fun p : ℝ≥0 × DLoc => (p.1, reversedAt p.1 p.2))
    (measurable_supLocalTime_uncurry θ) hm

/-- For every fixed path `f`, `s ↦ H_s(f)` is measurable (so `exploration` is not junk). -/
theorem measurable_height_section (θ : ℝ) (f : DLoc) :
    Measurable (fun s : ℝ≥0 => height θ f s) := by
  have hm : Measurable (fun s : ℝ≥0 => (s, f)) :=
    measurable_id.prodMk measurable_const
  exact Measurable.comp (g := fun p : ℝ≥0 × DLoc => height θ p.2 p.1)
    (f := fun s : ℝ≥0 => (s, f)) (measurable_height_uncurry θ) hm

/-- `x ↦ I^{x⁺}_t` as a function on `ℝ`. -/
noncomputable def futureInfFun (f : DLoc) (t : ℝ≥0) (x : ℝ) : ℝ := futureInf f t x.toNNReal

open scoped Classical in
/-- The Stieltjes function of `x ↦ I^{x⁺}_t` (junk zero only if the spec failed). -/
noncomputable def explorationStieltjes (f : DLoc) (t : ℝ≥0) : StieltjesFunction ℝ :=
  if h : Monotone (futureInfFun f t) ∧ ∀ x, ContinuousWithinAt (futureInfFun f t) (Ici x) x then
    { toFun := futureInfFun f t
      mono' := h.1
      right_continuous' := h.2 }
  else
    { toFun := fun _ => 0
      mono' := monotone_const
      right_continuous' := fun _ => continuousWithinAt_const }

/-- **The minimal exploration measure** `ρ_t = ∫_{(0,t]} 1{H_s ∈ ·} d_s I^s_t`, a measure on
heights (`(·).toNNReal` of the real height; heights are a.s. nonnegative). -/
noncomputable def exploration (θ : ℝ) (f : DLoc) (t : ℝ≥0) : Measure ℝ≥0 :=
  Measure.map (fun s : ℝ => (height θ f s.toNNReal).toNNReal)
    ((explorationStieltjes f t).measure.restrict (Ioc 0 (t : ℝ)))

/-- Guard against the `Measure.map` fallback: the height section is measurable on `ℝ`. -/
theorem measurable_exploration_heightMap (θ : ℝ) (f : DLoc) :
    Measurable (fun s : ℝ => (height θ f s.toNNReal).toNNReal) := by
  exact measurable_real_toNNReal.comp
    ((measurable_height_section θ f).comp measurable_real_toNNReal)

/-- Top of the support of a measure on heights (junk `0` for the zero measure). -/
noncomputable def topHeight (ρ : Measure ℝ≥0) : ℝ≥0 :=
  sSup {h : ℝ≥0 | ∀ ε : ℝ, 0 < ε → 0 < ρ (Metric.ball h ε)}

/-- Cut level for removing the top `m` units of mass of `ρ`. -/
noncomputable def eraseCut (m : ℝ≥0∞) (ρ : Measure ℝ≥0) : ℝ≥0 :=
  sInf {h : ℝ≥0 | ρ (Ioi h) ≤ m}

/-- Remove the top `m` units of mass: for `m = 0` nothing is removed; otherwise keep `ρ`
strictly below the cut, and put the remaining part of the mass of `ρ(Ici cut)` as an atom at the
cut.  (For `m > 0` and finite `ρ` the cut set is nonempty; without the `m = 0` branch an
unbounded support would give junk cut `0`.) -/
noncomputable def eraseMass (m : ℝ≥0∞) (ρ : Measure ℝ≥0) : Measure ℝ≥0 :=
  if m = 0 then ρ else
    ρ.restrict (Iio (eraseCut m ρ)) + (ρ (Ici (eraseCut m ρ)) - m) • Measure.dirac (eraseCut m ρ)

/-- Append `ν` above the support of `ρ`: heights of `ν` are shifted by `topHeight ρ`.
PRECONDITION: this represents the source concatenation only when `ρ` has BOUNDED support
(`topHeight` is an `sSup` in `ℝ≥0`, junk `0` for unbounded support); characterization lemmas
must carry that hypothesis. -/
noncomputable def concatAbove (ρ ν : Measure ℝ≥0) : Measure ℝ≥0 :=
  ρ + ν.map (fun x => x + topHeight ρ)

/-- Erasing zero mass leaves every measure unchanged. -/
theorem eraseMass_zero (ρ : Measure ℝ≥0) : eraseMass 0 ρ = ρ := by
  simp [eraseMass]


private theorem measurable_reversedAt_prefix (t : ℝ≥0) :
    Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance] (reversedAt t) := by
  rw [measurable_iff_comap_le]
  change MeasurableSpace.comap _ (⨆ u, MeasurableSpace.comap (DLoc.eval u) inferInstance) ≤ _
  rw [MeasurableSpace.comap_iSup, iSup_le_iff]
  intro u
  rw [MeasurableSpace.comap_comp]
  let v : Icc (0 : ℝ) (t : ℝ) := ⟨(min u t : ℝ≥0), (min u t).2, min_le_right u t⟩
  have he (f : DLoc) : (reversedAt t f).1 u =
      reverseIncrements t.2 (DLoc.restrict t f) v := by
    have hh := congrArg (fun g : D (t : ℝ) ℝ => g v) (restrict_reversedAt t f)
    change (reversedAt t f).1 (min u t) = _ at hh
    calc
      _ = (reversedAt t f).1 (min u t) := by
        simp only [reversedAt_apply, reversedPath, min_assoc, min_self]
      _ = _ := hh
  have hm : Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      (fun f : DLoc => reverseIncrements t.2 (DLoc.restrict t f) v) :=
    ((BGW.Skorokhod.measurable_eval v).comp
      (measurable_reverseIncrements t.2)).comp (comap_measurable (DLoc.restrict t))
  have hm' : Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      (fun f : DLoc => (reversedAt t f).1 u) := by
    convert hm using 1
    funext f
    exact he f
  exact hm'.comap_le

/-- Raw-prefix measurability: `H_t` is measurable for the σ-algebra generated by
`DLoc.restrict t`. -/
theorem measurable_height_prefix (θ : ℝ) (t : ℝ≥0) :
    Measurable[MeasurableSpace.comap (DLoc.restrict t) inferInstance]
      (fun f : DLoc => height θ f t) := by
  exact (measurable_supLocalTime θ t).comp (measurable_reversedAt_prefix t)

/-- Interval infima of a local càdlàg path have a genuine finite lower bound. -/
theorem futureInf_bddBelow (f : DLoc) (t s : ℝ≥0) :
    BddBelow (range (fun u : Icc (min s t) t => f.1 u)) := by
  have hb := (isBounded_image_of_isCadlag_of_isCompact f.2
    (isCompact_Icc : IsCompact (Icc (min s t) t))).bddBelow
  exact hb.mono (by rintro _ ⟨u, rfl⟩; exact ⟨u, u.2, rfl⟩)

/-- An interval infimum bounds each value in its interval. -/
theorem futureInf_le_eval (f : DLoc) (t s u : ℝ≥0) (hu : u ∈ Icc (min s t) t) :
    futureInf f t s ≤ f.1 u := ciInf_le (futureInf_bddBelow f t s) ⟨u, hu⟩

/-- The infimum at its terminal time is the terminal value. -/
theorem futureInf_self (f : DLoc) (t : ℝ≥0) : futureInf f t t = f.1 t := by
  let : Nonempty (Icc (min t t) t) := ⟨⟨t, by simp⟩⟩
  apply le_antisymm (futureInf_le_eval f t t t (by simp))
  apply le_ciInf
  intro u
  have hu : (u : ℝ≥0) = t := le_antisymm u.2.2 (by simpa only [min_self] using u.2.1)
  exact (congrArg f.1 hu).ge

/-- The future infimum is nondecreasing in its starting time. -/
theorem monotone_futureInf (f : DLoc) (t : ℝ≥0) : Monotone (futureInf f t) := by
  intro s r hsr
  let : Nonempty (Icc (min r t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
  apply le_ciInf
  intro u
  exact futureInf_le_eval f t s u ⟨(min_le_min_right t hsr).trans u.2.1, u.2.2⟩

/-- A future interval infimum is the running infimum of the centered shifted interval. -/
theorem futureInf_eq_runningInf_shift (f : DLoc) (t s : ℝ≥0) :
    futureInf f t s = f.1 (min s t) +
      runningInfLoc (DLoc.shift (min s t) f) (t - min s t) := by
  let a := min s t
  have ha : a ≤ t := min_le_right _ _
  let : Nonempty (Icc (min s t) t) := ⟨⟨t, ha, le_rfl⟩⟩
  apply le_antisymm
  · have hl : futureInf f t s - f.1 a ≤
        runningInfLoc (DLoc.shift a f) (t - a) := by
      apply le_runningInfLoc
      intro v
      have hv : a + v ≤ t := by
        calc
          a + v ≤ a + (t - a) := add_le_add (le_refl a) v.2
          _ = t := add_tsub_cancel_of_le ha
      have h := futureInf_le_eval f t s (a + v)
        ⟨le_add_of_nonneg_right (show 0 ≤ (v : ℝ≥0) from zero_le), hv⟩
      change futureInf f t s - f.1 a ≤ f.1 (a + v) - f.1 a
      exact sub_le_sub_right h _
    linarith only [hl]
  · apply le_ciInf
    intro u
    have hu : (u : ℝ≥0) - a ≤ t - a := tsub_le_tsub_right u.2.2 a
    have h := runningInfLoc_le_eval (DLoc.shift a f) (t - a) ⟨u - a, hu⟩
    change runningInfLoc (DLoc.shift a f) (t - a) ≤ f.1 (a + (u - a)) - f.1 a at h
    rw [add_tsub_cancel_of_le u.2.1] at h
    linarith only [h]

/-- The future interval infimum is jointly measurable in its two times and path. -/
theorem measurable_futureInf_uncurry :
    Measurable (fun p : (ℝ≥0 × ℝ≥0) × DLoc => futureInf p.2 p.1.1 p.1.2) := by
  have hm : Measurable (fun p : (ℝ≥0 × ℝ≥0) × DLoc => min p.1.2 p.1.1) :=
    measurable_fst.snd.min measurable_fst.fst
  have hg : Measurable (fun p : (ℝ≥0 × ℝ≥0) × DLoc =>
      DLoc.shift (min p.1.2 p.1.1) p.2) :=
    Measurable.comp (g := fun q : ℝ≥0 × DLoc => DLoc.shift q.1 q.2)
      (f := fun p : (ℝ≥0 × ℝ≥0) × DLoc => (min p.1.2 p.1.1, p.2))
      DLoc.measurable_shift (hm.prodMk measurable_snd)
  have hi : Measurable (fun p : (ℝ≥0 × ℝ≥0) × DLoc =>
      runningInfLoc (DLoc.shift (min p.1.2 p.1.1) p.2) (p.1.1 - min p.1.2 p.1.1)) :=
    Measurable.comp (g := fun q : ℝ≥0 × DLoc => runningInfLoc q.2 q.1)
      (f := fun p : (ℝ≥0 × ℝ≥0) × DLoc =>
        (p.1.1 - min p.1.2 p.1.1, DLoc.shift (min p.1.2 p.1.1) p.2))
      measurable_runningInfLoc_uncurry ((measurable_fst.fst.sub hm).prodMk hg)
  simp_rw [futureInf_eq_runningInf_shift]
  have hx : Measurable (fun p : (ℝ≥0 × ℝ≥0) × DLoc => p.2.1 (min p.1.2 p.1.1)) :=
    Measurable.comp (g := fun q : DLoc × ℝ≥0 => q.1.1 q.2)
      (f := fun p : (ℝ≥0 × ℝ≥0) × DLoc => (p.2, min p.1.2 p.1.1))
      DLoc.measurable_eval₂ (measurable_snd.prodMk hm)
  exact hx.add hi

/-- Joint measurability of the approximation in `(ε, t, f)`. -/
theorem measurable_heightApprox_uncurry :
    Measurable (fun p : ℝ × ℝ≥0 × DLoc => heightApprox p.1 p.2.2 p.2.1) := by
  let A : Set ((ℝ × (ℝ≥0 × DLoc)) × ℝ) :=
    {p | 0 ≤ p.2 ∧ p.2 ≤ (p.1.2.1 : ℝ) ∧
      p.1.2.2.1 p.2.toNNReal < futureInf p.1.2.2 p.1.2.1 p.2.toNNReal + p.1.1}
  have hA : MeasurableSet A := by
    apply MeasurableSet.inter (measurableSet_le measurable_const measurable_snd)
    apply MeasurableSet.inter (measurableSet_le measurable_snd (by fun_prop))
    have hx : Measurable (fun p : ((ℝ × (ℝ≥0 × DLoc)) × ℝ) =>
        p.1.2.2.1 p.2.toNNReal) :=
      Measurable.comp (g := fun q : DLoc × ℝ≥0 => q.1.1 q.2)
        (f := fun p : ((ℝ × (ℝ≥0 × DLoc)) × ℝ) => (p.1.2.2, p.2.toNNReal))
        DLoc.measurable_eval₂
        (measurable_fst.snd.snd.prodMk (measurable_real_toNNReal.comp measurable_snd))
    have hi : Measurable (fun p : ((ℝ × (ℝ≥0 × DLoc)) × ℝ) =>
        futureInf p.1.2.2 p.1.2.1 p.2.toNNReal) :=
      Measurable.comp
        (g := fun q : (ℝ≥0 × ℝ≥0) × DLoc => futureInf q.2 q.1.1 q.1.2)
        (f := fun p : ((ℝ × (ℝ≥0 × DLoc)) × ℝ) => ((p.1.2.1, p.2.toNNReal), p.1.2.2))
        measurable_futureInf_uncurry
        ((measurable_fst.snd.fst.prodMk
          (measurable_real_toNNReal.comp measurable_snd)).prodMk measurable_fst.snd.snd)
    exact measurableSet_lt hx (hi.add measurable_fst.fst)
  exact measurable_fst.inv.mul (measurable_measure_prodMk_left hA).ennreal_toReal

/-- `heightRaw` is measurable in `f` for each `t`. -/
theorem measurable_heightRaw (θ : ℝ) (t : ℝ≥0) :
    Measurable (fun f : DLoc => heightRaw θ f t) := by
  apply Measurable.liminf
  intro k
  have hm : Measurable (fun f : DLoc => (supEps θ k, t, f)) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  exact (measurable_heightApprox_uncurry.comp hm).ennreal_ofReal

private theorem futureInf_of_ge (f : DLoc) (t s : ℝ≥0) (hs : t ≤ s) :
    futureInf f t s = f.1 t := by
  have he : futureInf f t s = futureInf f t t := by
    unfold futureInf
    erw [min_eq_right hs, min_self]
  exact he.trans (futureInf_self f t)

private theorem isRightContinuous_futureInf (f : DLoc) (t : ℝ≥0) :
    IsRightContinuous (futureInf f t) := by
  intro s
  by_cases hst : s < t
  · let : Nonempty (Icc (min s t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
    apply tendsto_order.2
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact ha.trans_le (monotone_futureInf f t hr.le)
    · intro b hb
      obtain ⟨u, hu⟩ := (ciInf_lt_iff (futureInf_bddBelow f t s)).mp hb
      have hsu : s ≤ (u : ℝ≥0) := by simpa only [min_eq_left hst.le] using u.2.1
      rcases hsu.eq_or_lt with he | hlt
      · have hfs : f.1 s < b := by simpa only [← he] using hu
        have hf := (f.2.isRightContinuous s).eventually (eventually_lt_nhds hfs)
        filter_upwards [hf, (eventually_lt_nhds hst).filter_mono nhdsWithin_le_nhds]
          with r hr hrt
        exact (futureInf_le_eval f t r r ⟨min_le_left _ _, hrt.le⟩).trans_lt hr
      · filter_upwards [(eventually_lt_nhds hlt).filter_mono nhdsWithin_le_nhds] with r hr
        exact (futureInf_le_eval f t r u ⟨(min_le_left _ _).trans hr.le, u.2.2⟩).trans_lt hu
  · have hts : t ≤ s := le_of_not_gt hst
    have he : (futureInf f t) =ᶠ[𝓝[>] s] fun _ => f.1 t := by
      filter_upwards [self_mem_nhdsWithin] with r hr
      exact futureInf_of_ge f t r (hts.trans hr.le)
    change Tendsto (futureInf f t) (𝓝[>] s) (𝓝 (futureInf f t s))
    rw [futureInf_of_ge f t s hts]
    exact (tendsto_congr' he).2 tendsto_const_nhds

/-- For every path, `x ↦ I^x_t` is monotone and right-continuous. -/
theorem explorationStieltjes_spec (f : DLoc) (t : ℝ≥0) :
    Monotone (futureInfFun f t) ∧ ∀ x, ContinuousWithinAt (futureInfFun f t) (Ici x) x := by
  refine ⟨(monotone_futureInf f t).comp (fun _ _ hab => Real.toNNReal_mono hab), ?_⟩
  intro x
  have hc : ContinuousWithinAt (futureInf f t) (Ici x.toNNReal) x.toNNReal :=
    continuousWithinAt_Ioi_iff_Ici.mp (isRightContinuous_futureInf f t x.toNNReal)
  exact hc.comp continuous_real_toNNReal.continuousAt.continuousWithinAt
    (fun _ hy => Real.toNNReal_mono hy)

private theorem explorationStieltjes_apply (f : DLoc) (t : ℝ≥0) (x : ℝ) :
    explorationStieltjes f t x = futureInfFun f t x := by
  simp only [explorationStieltjes, dite_eq_left (explorationStieltjes_spec f t)]

/-- **Total mass** `ρ_t(ℝ≥0) = X_t - I_t` for every path (the atom at `s = t` is kept). -/
theorem exploration_univ (θ : ℝ) (f : DLoc) (t : ℝ≥0) :
    exploration θ f t univ = ENNReal.ofReal (f.1 t - futureInf f t 0) := by
  rw [exploration, Measure.map_apply (measurable_exploration_heightMap θ f) MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply_univ]
  rw [StieltjesFunction.measure_Ioc, explorationStieltjes_apply, explorationStieltjes_apply]
  simp only [futureInfFun, Real.toNNReal_coe, Real.toNNReal_zero, futureInf_self]

private theorem inf_le_leftLim (f : DLoc) {t s r : ℝ≥0}
    (hst : s ≤ t) (hsr : s ≤ r) (hrt : r ≤ t)
    (hs : Function.leftLim f.1 s = f.1 s) :
    futureInf f t s ≤ Function.leftLim f.1 r := by
  rcases hsr.eq_or_lt with he | hlt
  · subst r
    rw [hs]
    exact futureInf_le_eval f t s s ⟨min_le_left _ _, hst⟩
  · have : (𝓝[<] r).NeBot := nhdsLT_neBot_of_exists_lt ⟨s, hlt⟩
    apply ge_of_tendsto (f.2.tendsto_nhdsLT_leftLim r)
    filter_upwards [Ioo_mem_nhdsLT hlt] with v hv
    exact futureInf_le_eval f t s v ⟨(min_le_left _ _).trans hv.1.le, hv.2.le.trans hrt⟩

/-- Reversal turns a terminal window infimum into a prefix supremum at a continuity time. -/
theorem supRunning_reversedAt_window (f : DLoc) {t s : ℝ≥0} (hst : s ≤ t)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r)
    (hs : Function.leftLim f.1 s = f.1 s) :
    supRunning (reversedAt t f) (t - s) = f.1 t - futureInf f t s := by
  let : Nonempty (Icc (min s t) t) := ⟨⟨t, min_le_right _ _, le_rfl⟩⟩
  apply le_antisymm
  · apply ciSup_le
    intro u
    change (reversedAt t f).1 u ≤ _
    rw [reversedAt_apply]
    unfold reversedPath
    have hut : (u : ℝ≥0) ≤ t :=
      le_trans (show (u : ℝ≥0) ≤ t - s from u.2)
        (show t - s ≤ t from tsub_le_self)
    rw [min_eq_left hut]
    apply sub_le_sub_left
    apply inf_le_leftLim f hst _ tsub_le_self hs
    calc
      s = t - (t - s) := (tsub_tsub_cancel_of_le hst).symm
      _ ≤ t - u := tsub_le_tsub_left (show (u : ℝ≥0) ≤ t - s from u.2) t
  · have hl : f.1 t - supRunning (reversedAt t f) (t - s) ≤ futureInf f t s := by
      apply le_ciInf
      intro v
      have hsv : s ≤ (v : ℝ≥0) := by simpa only [min_eq_left hst] using v.2.1
      have huv : t - (v : ℝ≥0) ≤ t - s := tsub_le_tsub_left hsv t
      have hu := le_ciSup (supRunning_bddAbove (reversedAt t f) (t - s)) ⟨t - v, huv⟩
      change (reversedAt t f).1 (t - v) ≤ supRunning (reversedAt t f) (t - s) at hu
      rw [reversedAt_apply] at hu
      unfold reversedPath at hu
      rw [min_eq_left tsub_le_self, tsub_tsub_cancel_of_le v.2.2] at hu
      linarith only [hu, hf v]
    linarith only [hl]

/-- Reflection of the reversal equals the future-infimum gap at continuity times. -/
theorem supReflected_reversedAt_window (f : DLoc) {t s : ℝ≥0} (hst : s ≤ t)
    (hf : ∀ r, Function.leftLim f.1 r ≤ f.1 r)
    (hs : Function.leftLim f.1 s = f.1 s) :
    supReflected (reversedAt t f) (t - s) = f.1 s - futureInf f t s := by
  unfold supReflected
  rw [supRunning_reversedAt_window f hst hf hs, reversedAt_apply]
  unfold reversedPath
  rw [min_eq_left tsub_le_self, tsub_tsub_cancel_of_le hst, hs]
  ring

end BGW.StableTrees

