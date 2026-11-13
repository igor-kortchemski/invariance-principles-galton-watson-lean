/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableProcessCompactness
public import BGW.StableTrees.StableProcessLimits
import BGW.Probability.WeakConvergence
import Mathlib.Order.Filter.AtTopBot.CountablyGenerated

/-!
# The stable process law and the functional limit theorem

Tightness and finite-dimensional limits construct the stable Lévy law from the offspring-law
witness of `exists_stableDomain`. Uniqueness then identifies every subsequential limit of an
attracted real walk (Billingsley, *Convergence of Probability Measures*, 2nd ed., 1999,
Theorem 13.1; Kallenberg, *Foundations of Modern Probability*, 2nd ed., 2002, Theorem 16.14).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod BGW.Probability.RealWalk

/-- Any weak limit of step-path laws along indices tending to infinity satisfies
`IsStableLevyLaw`, including the terminal time `T` and all deterministic times. -/
theorem IsRealStableAttracted.isStableLevyLaw_of_tendsto {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) {P : ProbabilityMeasure (D T ℝ)}
    (hP : Tendsto (fun j => stepPathLaw ν T B (q j)) atTop (𝓝 P)) :
    IsStableLevyLaw θ T P := by
  refine ⟨?_, ?_⟩
  · intro hT0
    let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT0⟩
    let Q : ProbabilityMeasure ℝ := ⟨Measure.dirac 0, inferInstance⟩
    have hz : Continuous (fun f : D T ℝ => f z) := by
      apply LipschitzWith.continuous (K := 1)
      apply LipschitzWith.of_dist_le_mul
      intro f g
      simpa [z] using dist_eval_zero_le hT0 f g
    have hzero (n : ℕ) : (stepPathLaw ν T B n).map (fun f : D T ℝ => f z) = Q := by
      apply Subtype.ext
      change Measure.map (fun f : D T ℝ => f z)
        (Measure.map (realStepPath T n (B n)) (iidLaw ν : Measure (ℕ → ℝ))) = _
      rw [Measure.map_map (measurable_eval z) (measurable_realStepPath T n (B n))]
      have heq : (fun f : D T ℝ => f z) ∘ realStepPath T n (B n) = fun _ => 0 := by
        funext ω
        exact realStepPath_apply_zero hT0 n (B n) ω
      rw [heq]
      simp [Q]
    have hm := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous _ _ hP hz
    have hPQ : P.map (fun f : D T ℝ => f z) = Q :=
      tendsto_nhds_unique hm (by simpa only [hzero] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => Q) atTop (𝓝 Q)))
    have hae : ∀ᵐ x : ℝ ∂(P.map (fun f : D T ℝ => f z) : Measure ℝ), x = 0 := by
      rw [hPQ]
      simp [Q]
    exact (ae_map_iff (measurable_eval z).aemeasurable
      (measurableSet_singleton 0)).mp hae
  · intro k t ht _
    -- `hT` belongs to the frozen signature; this proof does not need it.
    have _ := hT
    exact congrArg ProbabilityMeasure.toMeasure (h.map_increments_of_tendsto hq hP t ht)

/-! ## Existence, uniqueness and the chosen law -/

/-- Existence of a stable Lévy law, from the offspring-law witness of `exists_stableDomain`. -/
theorem exists_isStableLevyLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∃ P : ProbabilityMeasure (D T ℝ), IsStableLevyLaw θ T P := by
  obtain ⟨μ, a, hμ⟩ := exists_stableDomain hθ
  have h := hμ.isRealStableAttracted
  obtain ⟨P, r, hr, hP⟩ := h.exists_subseq_stepPathLaw hT id
  exact ⟨P, h.isStableLevyLaw_of_tendsto hT hr.tendsto_atTop hP⟩

/-- Existence and uniqueness (uniqueness is the sealed `IsStableLevyLaw.unique`). -/
theorem existsUnique_isStableLevyLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∃! P : ProbabilityMeasure (D T ℝ), IsStableLevyLaw θ T P := by
  obtain ⟨P, hP⟩ := exists_isStableLevyLaw hθ hT
  exact ⟨P, hP, fun Q hQ => hQ.unique hθ hT hP⟩

/-- The law of the spectrally positive `θ`-stable Lévy process on `[0,T]`; chosen after
existence is proved. Junk value (Dirac at the zero path) unless `1 < θ ≤ 2` and `0 < T`. -/
noncomputable def stableProcessLaw (θ T : ℝ) : ProbabilityMeasure (D T ℝ) :=
  if h : (1 < θ ∧ θ ≤ 2) ∧ 0 < T then Classical.choose (exists_isStableLevyLaw h.1 h.2)
  else ⟨Measure.dirac (Skorokhod.ofContinuous (ContinuousMap.const _ 0)), inferInstance⟩

/-- The chosen law satisfies the stable Lévy characterization at valid parameters. -/
theorem isStableLevyLaw_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    IsStableLevyLaw θ T (stableProcessLaw θ T) := by
  simpa [stableProcessLaw, hθ, hT] using
    Classical.choose_spec (exists_isStableLevyLaw hθ hT)

/-- Characterization: the stable process law is the unique stable Lévy law. -/
theorem eq_stableProcessLaw_iff {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {P : ProbabilityMeasure (D T ℝ)} :
    P = stableProcessLaw θ T ↔ IsStableLevyLaw θ T P := by
  constructor
  · rintro rfl
    exact isStableLevyLaw_stableProcessLaw hθ hT
  · intro hP
    exact hP.unique hθ hT (isStableLevyLaw_stableProcessLaw hθ hT)

/-- Fixed-time marginals of the stable process law: `X_t` has law `stableLawAt θ t` for
`0 < t ≤ T`. -/
theorem map_eval_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (t : Set.Icc (0 : ℝ) T) (ht : 0 < (t : ℝ)) :
    (stableProcessLaw θ T : Measure (D T ℝ)).map (fun f : D T ℝ => f t) =
      (stableLawAt θ t : Measure ℝ) := by
  have hP := isStableLevyLaw_stableProcessLaw hθ hT
  let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT.le⟩
  let v : Fin 2 → Set.Icc (0 : ℝ) T := ![z, t]
  have hv : StrictMono v := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    change (0 : ℝ) < (t : ℝ)
    exact ht
  have hi := hP.map_increments 1 v hv
  have hmap := congrArg (Measure.map (Function.eval (0 : Fin 1))) hi
  change Measure.map (Function.eval (0 : Fin 1))
    (Measure.map (incrementsMap v) (stableProcessLaw θ T : Measure (D T ℝ))) = _ at hmap
  rw [Measure.map_map (measurable_pi_apply _) (measurable_incrementsMap v),
    Measure.pi_map_eval] at hmap
  have heq : (fun f : D T ℝ => f t) =ᵐ[(stableProcessLaw θ T : Measure (D T ℝ))]
      ((Function.eval (0 : Fin 1)) ∘ incrementsMap v) := by
    filter_upwards [hP.start hT.le] with f hf
    simp [incrementsMap, v, z, hf]
  rw [Measure.map_congr heq]
  simpa [v, z, incrementsMap] using hmap

/-- The stable process law starts at `0` almost surely. -/
theorem ae_eval_zero_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)),
      f ⟨0, le_rfl, hT.le⟩ = 0 := by
  exact (isStableLevyLaw_stableProcessLaw hθ hT).start hT.le

/-- No fixed discontinuities for the stable process law (specialization of
`IsStableLevyLaw.ae_continuousAt`). -/
theorem ae_continuousAt_stableProcessLaw {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    (t : Set.Icc (0 : ℝ) T) :
    ∀ᵐ f : D T ℝ ∂(stableProcessLaw θ T : Measure (D T ℝ)), ContinuousAt f t := by
  exact (isStableLevyLaw_stableProcessLaw hθ hT).ae_continuousAt hθ hT t

/-- Consistency of the stable process laws under restriction (specialization of
`IsStableLevyLaw.map_restrict`). -/
theorem map_restrict_stableProcessLaw {θ T a : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (ha : 0 < a)
    (haT : a ≤ T) :
    (stableProcessLaw θ T).map (Skorokhod.restrict haT) = stableProcessLaw θ a := by
  apply (eq_stableProcessLaw_iff hθ ha).mpr
  exact (isStableLevyLaw_stableProcessLaw hθ (ha.trans_le haT)).map_restrict hθ ha haT

/-! ## The functional limit theorem -/

/-- Functional limit theorem: for every real iid walk in the domain of attraction (arbitrary
eventually positive normalizers, no centering, no monotonicity, no moments) and every horizon
`T > 0`, the laws of the step paths `t ↦ S_{⌊nt⌋} / B n`, terminal value at `T` included,
converge weakly in `D T ℝ` to the stable process law. -/
theorem IsRealStableAttracted.tendsto_stepPathLaw {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => stepPathLaw ν T B n) atTop (𝓝 (stableProcessLaw θ T)) := by
  apply Filter.tendsto_of_subseq_tendsto
  intro q hq
  obtain ⟨P, r, hr, hP⟩ := h.exists_subseq_stepPathLaw hT q
  have hstable := h.isStableLevyLaw_of_tendsto hT (hq.comp hr.tendsto_atTop) hP
  have heq := (eq_stableProcessLaw_iff h.index_mem hT).mpr hstable
  exact ⟨r, heq ▸ hP⟩

/-- Subsequence form. -/
theorem IsRealStableAttracted.tendsto_stepPathLaw_subseq {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) :
    Tendsto (fun j => stepPathLaw ν T B (q j)) atTop (𝓝 (stableProcessLaw θ T)) := by
  exact (h.tendsto_stepPathLaw hT).comp hq

/-- Any measurable iid realization of the steps has the same step-path laws. -/
theorem IsRealStableAttracted.tendsto_map_realStepPath_iid {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} (hT : 0 < T)
    {Ω : Type*} [MeasurableSpace Ω] (μ : ProbabilityMeasure Ω) (ξ : ℕ → Ω → ℝ)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ (μ : Measure Ω))
    (hlaw : ∀ i, Measure.map (ξ i) (μ : Measure Ω) = (ν : Measure ℝ)) :
    Tendsto (fun n => μ.map (fun ω => realStepPath T n (B n) (fun i => ξ i ω))) atTop
      (𝓝 (stableProcessLaw θ T)) := by
  have hjoint : Measure.map (fun ω i => ξ i ω) (μ : Measure Ω) =
      (iidLaw ν : Measure (ℕ → ℝ)) := by
    rw [hind.map_fun_eq_infinitePi_map hξ]
    simp only [hlaw, coe_iidLaw]
  have heq (n : ℕ) : μ.map (fun ω => realStepPath T n (B n) (fun i => ξ i ω)) =
      stepPathLaw ν T B n := by
    apply Subtype.ext
    change Measure.map (realStepPath T n (B n) ∘ (fun ω i => ξ i ω))
      (μ : Measure Ω) = _
    rw [← Measure.map_map (measurable_realStepPath T n (B n))
      (Measurable.of_eval hξ), hjoint]
    rfl
  simpa only [heq] using h.tendsto_stepPathLaw hT

/-- Integer-step corollary through `Attraction.IsStableAttracted.isRealStableAttracted`
(centering `0`, eventual positivity of `B`). -/
theorem Attraction.IsStableAttracted.tendsto_stepPathLaw {ν : Measure ℤ}
    [IsProbabilityMeasure ν] {θ : ℝ} {B : ℕ → ℝ}
    (h : Attraction.IsStableAttracted ν θ 0 B) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => stepPathLaw (castLaw ν) T B n) atTop (𝓝 (stableProcessLaw θ T)) := by
  exact h.isRealStableAttracted.tendsto_stepPathLaw hT

/-- Offspring corollary: the step `K - 1` as a real law, normalizer `a` of `StableDomain`. -/
theorem StableDomain.tendsto_stepPathLaw {μ : PMF ℕ} {θ : ℝ} {a : ℕ → ℝ}
    (h : StableDomain μ θ a) {T : ℝ} (hT : 0 < T) :
    Tendsto (fun n => stepPathLaw (realOffspringStepLaw μ) T a n) atTop
      (𝓝 (stableProcessLaw θ T)) := by
  exact h.isRealStableAttracted.tendsto_stepPathLaw hT

end BGW.StableTrees
