/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Restrict
public import BGW.Skorokhod.Measurable
public import BGW.Skorokhod.MeasurableCylinders
public import BGW.Skorokhod.Separable
public import BGW.Probability.WeakConvergence
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Determination and convergence of path laws from prefixes

Stopped paths approximate a path near the terminal time. We use this approximation to prove
weak convergence from convergence of restrictions and uniqueness of laws with equal prefixes.
-/

@[expose] public section

open Set Filter Topology MeasureTheory
open scoped Topology BoundedContinuousFunction

namespace BGW.Skorokhod


variable {T : ℝ} {E : Type*}

/-- Restriction to a nonnegative prefix is Borel measurable for the J1 Borel structures. -/
theorem measurable_restrict_of_nonneg [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) : Measurable (restrict (E := E) haT) := by
  let _ : MeasurableSpace E := borel E
  let _ : BorelSpace E := ⟨rfl⟩
  apply Measurable.of_comap_le
  change MeasurableSpace.comap (restrict haT) (borel (D a E)) ≤ _
  rw [show borel (D a E) = _ from measurableSpace_eq_iSup_comap_eval
    (T := a) (E := E) (S := Set.univ) dense_univ ha (Set.mem_univ _)]
  simp only [MeasurableSpace.comap_iSup]
  refine iSup_le fun t => iSup_le fun _ => ?_
  rw [MeasurableSpace.comap_comp]
  exact measurable_iff_comap_le.mp
    (measurable_eval (⟨t, t.2.1, t.2.2.trans haT⟩ : Set.Icc (0 : ℝ) T))

/-- Stopping at a time in `[0, T]` is Borel measurable for the J1 Borel structures. -/
theorem measurable_stop_of_nonneg [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) : Measurable (stop (T := T) (E := E) a) := by
  have heq : stop (T := T) (E := E) a = extendConst ha haT ∘ restrict haT := by
    funext f
    exact stop_eq_extendConst_restrict ha haT f
  rw [heq]
  exact (lipschitzWith_one_extendConst ha haT).continuous.measurable.comp
    (measurable_restrict_of_nonneg ha haT)

/-- Stopped laws converge weakly to the original law along times increasing to the terminal
time, provided the original law is almost surely continuous there. -/
theorem tendsto_map_stop [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    {P : ProbabilityMeasure (D T E)} (hT : 0 < T) {a : ℕ → ℝ}
    (ha0 : ∀ k, 0 ≤ a k) (haT : ∀ k, a k < T) (hlim : Tendsto a atTop (𝓝 T))
    (hcont : ∀ᵐ (f : D T E) ∂(P : Measure (D T E)),
      ContinuousAt f ⟨T, hT.le, le_rfl⟩) :
    Tendsto (fun k => P.map (stop (a k))) atTop (𝓝 P) := by
  have haLT : Tendsto a atTop (𝓝[<] T) :=
    tendsto_nhdsWithin_iff.mpr ⟨hlim, Filter.Eventually.of_forall haT⟩
  have hstop (f : D T E) (hf : ContinuousAt f ⟨T, hT.le, le_rfl⟩) :
      Tendsto (fun k => stop (a k) f) atTop (𝓝 f) := by
    simpa only [Function.comp_def] using (tendsto_stop_nhdsLT hT hf).comp haLT
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  have hmeas (k : ℕ) : AEMeasurable (stop (a k)) (P : Measure (D T E)) :=
    (measurable_stop_of_nonneg (ha0 k) (haT k).le).aemeasurable
  simp_rw [ProbabilityMeasure.toMeasure_map,
    integral_map (hmeas _) φ.continuous.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro k
    exact (φ.continuous.measurable.comp
      (measurable_stop_of_nonneg (ha0 k) (haT k).le)).aestronglyMeasurable
  · exact integrable_const _
  · intro k
    exact Filter.Eventually.of_forall fun f => φ.norm_coe_le_norm (stop (a k) f)
  · filter_upwards [hcont] with f hf
    simpa only [Function.comp_def] using φ.continuous.continuousAt.tendsto.comp (hstop f hf)

/-- Constant extension after restriction is the same operation on laws as stopping. -/
theorem map_extendConst_restrict [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    (P : ProbabilityMeasure (D T E)) {a : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) :
    (P.map (restrict haT)).map (extendConst ha haT) = P.map (stop a) := by
  apply Subtype.ext
  change Measure.map (extendConst ha haT) (Measure.map (restrict haT) (P : Measure (D T E))) =
    Measure.map (stop a) (P : Measure (D T E))
  rw [Measure.map_map (lipschitzWith_one_extendConst ha haT).continuous.measurable
    (measurable_restrict_of_nonneg ha haT)]
  congr 1
  funext f
  exact (stop_eq_extendConst_restrict ha haT f).symm


/-- Convergence in law in `D` from convergence of the restrictions to `[0, a k]` for times
`a k ↑ T`, a limit almost surely continuous at `T`, and control of the oscillation after
`a k` (Billingsley 1999, Theorem 3.2 with C7; C11(2)). -/
theorem tendsto_of_tendsto_restrict_of_oscillation {Ω : ℕ → Type*}
    [∀ n, MeasurableSpace (Ω n)] [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    (μ : (n : ℕ) → ProbabilityMeasure (Ω n)) {Y : (n : ℕ) → Ω n → D T E}
    (hY : ∀ n, Measurable (Y n)) {ν : ProbabilityMeasure (D T E)} (hT : 0 < T)
    {a : ℕ → ℝ} (ha0 : ∀ k, 0 ≤ a k) (haT : ∀ k, a k < T) (hlim : Tendsto a atTop (𝓝 T))
    (hpre : ∀ k, Tendsto (fun n => (μ n).map (restrict (haT k).le ∘ Y n)) atTop
      (𝓝 (ν.map (restrict (haT k).le))))
    (hcont : ∀ᵐ (f : D T E) ∂(ν : Measure (D T E)), ContinuousAt f ⟨T, hT.le, le_rfl⟩)
    (hosc : ∀ η > 0, Tendsto (fun k => limsup (fun n => (μ n : Measure (Ω n)).real
      {ω | η < ⨆ s : {s : Set.Icc (0 : ℝ) T // a k ≤ (s : ℝ)},
        dist (Y n ω s) (Y n ω ⟨a k, ha0 k, (haT k).le⟩)}) atTop) atTop (𝓝 0)) :
    Tendsto (fun n => (μ n).map (Y n)) atTop (𝓝 ν) := by
  refine BGW.Probability.tendsto_of_tendsto_approx μ hY
    (X := fun k n => stop (a k) ∘ Y n) (Z := fun k => ν.map (stop (a k))) ?_ ?_ ?_ ?_
  · intro k n
    exact (measurable_stop_of_nonneg (ha0 k) (haT k).le).comp (hY n)
  · intro k
    have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
      (fun n => (μ n).map (restrict (haT k).le ∘ Y n)) (ν.map (restrict (haT k).le))
      (hpre k) (lipschitzWith_one_extendConst (ha0 k) (haT k).le).continuous
    have hleft (n : ℕ) :
        ((μ n).map (restrict (haT k).le ∘ Y n)).map
          (extendConst (ha0 k) (haT k).le) = (μ n).map (stop (a k) ∘ Y n) := by
      apply Subtype.ext
      change Measure.map (extendConst (ha0 k) (haT k).le)
        (Measure.map (restrict (haT k).le ∘ Y n) (μ n : Measure (Ω n))) =
        Measure.map (stop (a k) ∘ Y n) (μ n : Measure (Ω n))
      rw [Measure.map_map
        (lipschitzWith_one_extendConst (ha0 k) (haT k).le).continuous.measurable
        ((measurable_restrict_of_nonneg (ha0 k) (haT k).le).comp (hY n))]
      congr 1
      funext ω
      exact (stop_eq_extendConst_restrict (ha0 k) (haT k).le (Y n ω)).symm
    have hright := map_extendConst_restrict ν (ha0 k) (haT k).le
    simpa only [hleft, hright] using hm
  · exact tendsto_map_stop hT ha0 haT hlim hcont
  · intro ε hε
    apply squeeze_zero (g := fun k => limsup (fun n => (μ n : Measure (Ω n)).real
      {ω | ε / 2 < ⨆ s : {s : Set.Icc (0 : ℝ) T // a k ≤ (s : ℝ)},
        dist (Y n ω s) (Y n ω ⟨a k, ha0 k, (haT k).le⟩)}) atTop)
    · intro k
      exact le_limsup_of_frequently_le
        (Filter.Frequently.of_forall fun n => measureReal_nonneg)
        (isBoundedUnder_of ⟨1, fun n => measureReal_le_one⟩)
    · intro k
      apply Filter.limsup_le_limsup
      · exact Filter.Eventually.of_forall fun n => measureReal_mono (by
          intro ω hω
          change ε ≤ dist (stop (a k) (Y n ω)) (Y n ω) at hω
          change ε / 2 < ⨆ s : {s : Set.Icc (0 : ℝ) T // a k ≤ (s : ℝ)},
            dist (Y n ω s) (Y n ω ⟨a k, ha0 k, (haT k).le⟩)
          have hd := dist_stop_le (ha0 k) (haT k).le (Y n ω)
          linarith)
      · exact Filter.isCoboundedUnder_le_of_le atTop fun n => measureReal_nonneg
      · exact isBoundedUnder_of ⟨1, fun n => measureReal_le_one⟩
    · exact hosc (ε / 2) (by positivity)

/-- Two laws on `D`, both almost surely continuous at `T`, with equal restrictions to `[0, a k]`
for times `a k ↑ T`, are equal (C12(2)). -/
theorem ext_of_restrict [MetricSpace E] [TopologicalSpace.SeparableSpace E]
    {P Q : ProbabilityMeasure (D T E)} (hT : 0 < T) {a : ℕ → ℝ} (haT : ∀ k, a k < T)
    (hlim : Tendsto a atTop (𝓝 T))
    (hP : ∀ᵐ (f : D T E) ∂(P : Measure (D T E)), ContinuousAt f ⟨T, hT.le, le_rfl⟩)
    (hQ : ∀ᵐ (f : D T E) ∂(Q : Measure (D T E)), ContinuousAt f ⟨T, hT.le, le_rfl⟩)
    (h : ∀ k, P.map (restrict (haT k).le) = Q.map (restrict (haT k).le)) : P = Q := by
  have ha0 : ∀ᶠ k in atTop, 0 ≤ a k := by
    filter_upwards [hlim.eventually (Ioi_mem_nhds hT)] with k hk
    exact hk.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp ha0
  let b : ℕ → ℝ := fun k => a (k + N)
  have hb0 (k : ℕ) : 0 ≤ b k := hN (k + N) (Nat.le_add_left N k)
  have hbT (k : ℕ) : b k < T := haT (k + N)
  have hblim : Tendsto b atTop (𝓝 T) := hlim.comp (tendsto_add_atTop_nat N)
  have hstopP := tendsto_map_stop hT hb0 hbT hblim hP
  have hstopQ := tendsto_map_stop hT hb0 hbT hblim hQ
  have heq (k : ℕ) : P.map (stop (b k)) = Q.map (stop (b k)) := by
    rw [← map_extendConst_restrict P (hb0 k) (hbT k).le,
      ← map_extendConst_restrict Q (hb0 k) (hbT k).le]
    exact congrArg (fun R => R.map (extendConst (hb0 k) (hbT k).le)) (h (k + N))
  have hstopQ' : Tendsto (fun k => P.map (stop (b k))) atTop (𝓝 Q) := by
    simpa only [heq] using hstopQ
  exact tendsto_nhds_unique hstopP hstopQ'

end BGW.Skorokhod
