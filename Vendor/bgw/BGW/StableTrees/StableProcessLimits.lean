/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.WalkPathFDD
import BGW.Probability.WeakConvergence
import BGW.Skorokhod.MeasurableJumps
import Mathlib.Topology.Algebra.Module.Cardinality
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Limits of evaluations of stable-attracted paths

Fixed-jump times are countable. Right approximation by the other times identifies every
finite-dimensional distribution of a cluster law, including terminal evaluation (Billingsley,
*Convergence of Probability Measures*, 2nd ed., 1999, Section 13).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod BGW.Probability.RealWalk

/-- Almost sure pointwise convergence of measurable maps implies convergence of their laws. -/
theorem tendsto_probabilityMeasure_map_of_ae_tendsto {Ω S : Type*} [MeasurableSpace Ω]
    [MetricSpace S] [MeasurableSpace S] [BorelSpace S] (P : ProbabilityMeasure Ω)
    {g : ℕ → Ω → S} {f : Ω → S} (hg : ∀ n, Measurable (g n)) (hf : Measurable f)
    (hlim : ∀ᵐ ω ∂(P : Measure Ω), Tendsto (fun n => g n ω) atTop (𝓝 (f ω))) :
    Tendsto (fun n => P.map (g n)) atTop (𝓝 (P.map f)) := by
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro φ
  simp only [ProbabilityMeasure.toMeasure_map,
    integral_map (hg _).aemeasurable φ.continuous.aestronglyMeasurable,
    integral_map hf.aemeasurable φ.continuous.aestronglyMeasurable]
  apply tendsto_integral_of_dominated_convergence (fun _ => ‖φ‖)
  · intro n
    exact (φ.continuous.measurable.comp (hg n)).aestronglyMeasurable
  · exact integrable_const _
  · intro n
    exact Eventually.of_forall fun ω => φ.norm_coe_le_norm (g n ω)
  · filter_upwards [hlim] with ω hω
    exact φ.continuous.continuousAt.tendsto.comp hω

private theorem ae_continuous_eval_of_no_jump {T : ℝ} (P : ProbabilityMeasure (D T ℝ))
    (t : Set.Icc (0 : ℝ) T)
    (ht : (P : Measure (D T ℝ)) {f | Function.leftLim f t ≠ f t} = 0) :
    ∀ᵐ f ∂(P : Measure (D T ℝ)), ContinuousAt (fun g : D T ℝ => g t) f := by
  have hj : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)), Function.leftLim f t = f t := by
    simpa only [ae_iff, not_not] using ht
  filter_upwards [hj] with f hf
  apply continuousAt_eval
  rw [continuousAt_iff_continuous_left'_right']
  constructor
  · change Tendsto f (𝓝[<] t) (𝓝 (f t))
    simpa [hf] using (isCadlag f).tendsto_nhdsLT_leftLim t
  · exact (isCadlag f).isRightContinuous t

private theorem ae_continuous_eval_top {T : ℝ} (P : ProbabilityMeasure (D T ℝ))
    (hT : 0 ≤ T) :
    ∀ᵐ f ∂(P : Measure (D T ℝ)),
      ContinuousAt (fun g : D T ℝ => g ⟨T, hT, le_rfl⟩) f := by
  have hLip : LipschitzWith 1 (fun g : D T ℝ => g ⟨T, hT, le_rfl⟩) :=
    LipschitzWith.of_dist_le_mul fun f g => by simpa using dist_eval_top_le hT f g
  exact Eventually.of_forall fun _ => hLip.continuous.continuousAt

private theorem exists_good_right {T : ℝ} (P : ProbabilityMeasure (D T ℝ))
    (t : Set.Icc (0 : ℝ) T) (ht : (t : ℝ) < T) {ε : ℝ} (hε : 0 < ε) :
    ∃ s : Set.Icc (0 : ℝ) T, t < s ∧ (s : ℝ) < (t : ℝ) + ε ∧
      (P : Measure (D T ℝ)) {f | Function.leftLim f s ≠ f s} = 0 := by
  let J := {s : Set.Icc (0 : ℝ) T |
    (P : Measure (D T ℝ)) {f | Function.leftLim f s ≠ f s} ≠ 0}
  have hJ : (Subtype.val '' J : Set ℝ).Countable :=
    (countable_setOf_measure_jump_ne_zero P).image Subtype.val
  have hd := hJ.dense_compl ℝ
  obtain ⟨s, hsJ, hs⟩ := hd.exists_mem_open isOpen_Ioo
    (Set.nonempty_Ioo.mpr (lt_min ht (by linarith : (t : ℝ) < (t : ℝ) + ε)))
  let u : Set.Icc (0 : ℝ) T := ⟨s, t.property.1.trans hs.1.le,
    (hs.2.trans_le (min_le_left _ _)).le⟩
  refine ⟨u, hs.1, hs.2.trans_le (min_le_right _ _), ?_⟩
  by_contra hu
  exact hsJ ⟨u, hu, rfl⟩

private theorem exists_good_approximation {T : ℝ} (P : ProbabilityMeasure (D T ℝ))
    (t : Set.Icc (0 : ℝ) T) :
    ∃ s : ℕ → Set.Icc (0 : ℝ) T,
      (∀ n, t ≤ s n) ∧ Tendsto s atTop (𝓝 t) ∧
      ∀ n, ∀ᵐ f ∂(P : Measure (D T ℝ)),
        ContinuousAt (fun g : D T ℝ => g (s n)) f := by
  by_cases ht : (t : ℝ) = T
  · refine ⟨fun _ => t, fun _ => le_rfl, tendsto_const_nhds, fun _ => ?_⟩
    have heq : t = ⟨T, t.property.1.trans t.property.2, le_rfl⟩ := Subtype.ext ht
    rw [heq]
    exact ae_continuous_eval_top P (t.property.1.trans t.property.2)
  · have htT : (t : ℝ) < T := lt_of_le_of_ne t.property.2 ht
    have hex (n : ℕ) := exists_good_right P t htT
      (show 0 < 1 / (n + 1 : ℝ) by positivity)
    choose s hts hclose hj using hex
    refine ⟨s, fun n => (hts n).le, ?_, fun n =>
      ae_continuous_eval_of_no_jump P (s n) (hj n)⟩
    apply tendsto_subtype_rng.mpr
    have hr : Tendsto (fun n : ℕ => 1 / (n + 1 : ℝ)) atTop (𝓝 0) := by
      simpa only [one_div, Function.comp_def] using tendsto_inv_atTop_zero.comp
        (tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_natCast_atTop_atTop)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using tendsto_const_nhds.add hr)
      (fun n => (hts n).le) (fun n => (hclose n).le)

private theorem tendsto_eval_of_right {T : ℝ} (f : D T ℝ)
    {s : ℕ → Set.Icc (0 : ℝ) T} {t : Set.Icc (0 : ℝ) T}
    (hs : ∀ n, t ≤ s n) (hlim : Tendsto s atTop (𝓝 t)) :
    Tendsto (fun n => f (s n)) atTop (𝓝 (f t)) := by
  exact (continuousWithinAt_Ioi_iff_Ici.mp ((isCadlag f).isRightContinuous t)).tendsto.comp
    (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hs⟩)

private theorem tendsto_stableLawAt_of_pos {θ d : ℝ} (hd : 0 < d)
    {u : ℕ → ℝ} (hu : Tendsto u atTop (𝓝 d)) :
    Tendsto (fun n => stableLawAt θ (u n)) atTop (𝓝 (stableLawAt θ d)) := by
  have hp : Tendsto (fun n => (u n) ^ (1 / θ)) atTop (𝓝 (d ^ (1 / θ))) :=
    (Real.continuousAt_rpow_const d (1 / θ) (Or.inl hd.ne')).tendsto.comp hu
  apply tendsto_probabilityMeasure_map_of_ae_tendsto (stableLaw θ)
    (fun _ => by fun_prop) (by fun_prop)
  exact Eventually.of_forall fun x => hp.mul_const x

/-- Every strictly ordered increment vector of a cluster law has the stable product law.
The times need not start at zero. -/
theorem IsRealStableAttracted.map_increments_of_tendsto {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ}
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) {P : ProbabilityMeasure (D T ℝ)}
    (hP : Tendsto (fun j => stepPathLaw ν T B (q j)) atTop (𝓝 P))
    {k : ℕ} (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) (ht : StrictMono t) :
    P.map (incrementsMap t) = incrementVectorLaw θ (fun i => (t i : ℝ)) := by
  choose s hs hlim hcont using fun i => exists_good_approximation P (t i)
  let v : ℕ → Fin (k + 1) → Set.Icc (0 : ℝ) T := fun n i => s i n
  have hv : ∀ᶠ n in atTop, StrictMono (v n) := by
    have hpair : ∀ i j, ∀ᶠ n in atTop, i < j → v n i < v n j := by
      intro i j
      by_cases hij : i < j
      · exact ((hlim i).eventually_lt (hlim j) (ht hij)).mono fun _ hn _ => hn
      · exact Eventually.of_forall fun _ hh => (hij hh).elim
    have hh := Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hpair i)
    exact hh.mono fun _ hn i j hij => hn i j hij
  have heq : ∀ᶠ n in atTop,
      P.map (incrementsMap (v n)) = incrementVectorLaw θ (fun i => (v n i : ℝ)) := by
    filter_upwards [hv] with n hn
    have hc : ∀ᵐ f ∂(P : Measure (D T ℝ)), ContinuousAt (incrementsMap (v n)) f := by
      have hh := ae_all_iff.mpr fun i => hcont i n
      filter_upwards [hh] with f hf
      apply continuousAt_pi.mpr
      intro i
      exact (hf i.succ).sub (hf i.castSucc)
    have hm := BGW.Probability.tendsto_map_of_ae_continuousAt hP
      (fun _ => (measurable_incrementsMap (v n)).aemeasurable) hc
    exact tendsto_nhds_unique hm ((h.tendsto_stepPathLaw_increments (v n) hn).comp hq)
  have hleft : Tendsto (fun n => P.map (incrementsMap (v n))) atTop
      (𝓝 (P.map (incrementsMap t))) := by
    apply tendsto_probabilityMeasure_map_of_ae_tendsto P
      (fun _ => measurable_incrementsMap _) (measurable_incrementsMap _)
    apply Eventually.of_forall
    intro f
    apply tendsto_pi_nhds.mpr
    intro i
    exact (tendsto_eval_of_right f (hs i.succ) (hlim i.succ)).sub
      (tendsto_eval_of_right f (hs i.castSucc) (hlim i.castSucc))
  have hright : Tendsto (fun n => incrementVectorLaw θ (fun i => (v n i : ℝ))) atTop
      (𝓝 (incrementVectorLaw θ (fun i => (t i : ℝ)))) := by
    apply ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp
    apply tendsto_pi_nhds.mpr
    intro i
    apply tendsto_stableLawAt_of_pos (sub_pos.mpr (ht Fin.castSucc_lt_succ))
    exact ((continuous_subtype_val.tendsto _).comp (hlim i.succ)).sub
      ((continuous_subtype_val.tendsto _).comp (hlim i.castSucc))
  exact tendsto_nhds_unique hleft (hright.congr' (heq.mono fun _ hh => hh.symm))

end BGW.StableTrees
