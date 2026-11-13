/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxTwoLimit
public import BGW.StableTrees.DiscreteHeightApproxMeshMeasure
public import BGW.StableTrees.DiscreteHeightApproxOccupationMapping
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import BGW.MetricMeasure.WeakPerturbation
import BGW.Probability.WeakConvergence
import Mathlib.Topology.Algebra.Module.Cardinality

/-!
# Identification of the joint height limit

The exact finite-path occupation map converges by continuous mapping, and its distance
from the discrete occupation vector is bounded by the final cell length. A joint vector
error is covered by finitely many coordinate errors, and upper limits preserve the
finite-sum bound. Choose positive bands tending to zero outside the exceptional countable set.
The discrete two-limit estimate and the sealed continuum approximation identify
both sides of the fixed-band joint convergence.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal Classical
open BGW.Skorokhod BGW.StableTrees.DiscreteForest
namespace BGW.StableTrees.DiscreteHeightApprox

/-- A finite-vector joint error is bounded by a sum of coordinate error probabilities. -/
theorem measure_prod_pi_error_le {Ω S : Type*} [MeasurableSpace Ω] [PseudoMetricSpace S]
    (P : Measure Ω) {r : ℕ} (X : Ω → S) (F G : Ω → Fin r → ℝ)
    {δ : ℝ} (hδ : 0 < δ) :
    P {ω | δ ≤ dist (X ω, F ω) (X ω, G ω)} ≤
      ∑ i : Fin r, P {ω | δ / 2 < |F ω i - G ω i|} := by
  refine (measure_mono ?_).trans (measure_biUnion_finset_le Finset.univ _)
  intro ω hω
  by_contra hn
  have hc (i : Fin r) : dist (F ω i) (G ω i) ≤ δ / 2 := by
    rw [Real.dist_eq]
    apply le_of_not_gt
    intro hi
    exact hn (Set.mem_iUnion.mpr ⟨i, Set.mem_iUnion.mpr ⟨Finset.mem_univ i, hi⟩⟩)
  have hd := (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ δ / 2)).mpr hc
  have hh : δ ≤ dist (F ω) (G ω) := by
    change δ ≤ dist (X ω, F ω) (X ω, G ω) at hω
    simpa only [dist_prod_same_left] using hω
  linarith

/-- Upper limits of finite sums of extended nonnegative reals are subadditive. -/
theorem limsup_finset_sum_le {α ι : Type*} (l : Filter α) (s : Finset ι)
    (f : ι → α → ℝ≥0∞) :
    limsup (fun n => ∑ i ∈ s, f i n) l ≤ ∑ i ∈ s, limsup (f i) l := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty, ← ENNReal.bot_eq_zero, limsup_const_bot]
    exact le_rfl
  | @insert i s hi ih =>
    simp_rw [Finset.sum_insert hi]
    exact (limsup_add_le_ennreal l (f i) (fun n => ∑ j ∈ s, f j n)).trans
      (add_le_add le_rfl ih)

/-- Coordinate two-limit bounds give the joint finite-vector two-limit bound. -/
theorem tendsto_limsup_prod_pi_error {α S : Type*} [PseudoMetricSpace S] {l : Filter α}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, ProbabilityMeasure (Ω n))
    {r : ℕ} (X : ∀ n, Ω n → S) (F : α → ∀ n, Ω n → Fin r → ℝ)
    (G : ∀ n, Ω n → Fin r → ℝ)
    (hc : ∀ i : Fin r, ∀ δ > 0, Tendsto (fun u => limsup (fun n =>
      (P n).toMeasure {ω | δ < |F u n ω i - G n ω i|}) atTop) l (𝓝 0))
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun u => limsup (fun n => (P n).toMeasure
      {ω | δ ≤ dist (X n ω, F u n ω) (X n ω, G n ω)}) atTop) l (𝓝 0) := by
  have ht := tendsto_finsetSum Finset.univ (fun i _ => hc i (δ / 2) (by positivity))
  simp only [Finset.sum_const_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall fun _ => bot_le
  · apply Eventually.of_forall
    intro u
    exact (limsup_le_limsup (Eventually.of_forall fun n =>
      measure_prod_pi_error_le (P n).toMeasure (X n) (F u n) (G n) hδ)).trans
        (limsup_finset_sum_le atTop Finset.univ _)

/-- Convergence of upper-limit probabilities implies convergence of their real versions. -/
theorem tendsto_limsup_measureReal_of_measure {α : Type*} {l : Filter α}
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, ProbabilityMeasure (Ω n))
    (E : α → ∀ n, Set (Ω n))
    (h : Tendsto (fun u => limsup (fun n => (P n).toMeasure (E u n)) atTop) l (𝓝 0)) :
    Tendsto (fun u => limsup (fun n => (P n).toMeasure.real (E u n)) atTop) l (𝓝 0) := by
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp h
  simp only [ENNReal.toReal_zero] at ht
  have he (u : α) : (limsup (fun n => (P n).toMeasure (E u n)) atTop).toReal =
      limsup (fun n => (P n).toMeasure.real (E u n)) atTop := by
    have hb : IsBoundedUnder (· ≤ ·) atTop (fun n => (P n).toMeasure.real (E u n)) :=
      isBoundedUnder_of_eventually_le (a := (1 : ℝ))
        (Eventually.of_forall fun n => measureReal_le_one)
    exact ENNReal.toReal_limsup (Eventually.of_forall fun n => measure_ne_top _ _) hb
  simpa only [Function.comp_def, he] using ht

/-- The entire joint occupation vector has the same deterministic mesh-error bound. -/
theorem dist_discreteJoint_finiteOccupationJoint_le (B : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    (hB : 0 < B n) (T : ℝ≥0) {r : ℕ} (t : Fin r → ℝ≥0) (ht : ∀ i, t i ≤ T)
    (ω : ℕ → ℕ) {ε : ℝ} (hε : 0 < ε) :
    dist (discreteJoint B n T ε t ω)
      (finiteOccupationJoint T ε t (forestWalkPath B n T ω)) ≤ 1 / ((n : ℝ) * ε) := by
  change dist (forestWalkPath B n T ω, fun i => discreteOccupation B n ε ω (t i))
    (forestWalkPath B n T ω, fun i => finiteHeightApprox T (t i) ε (forestWalkPath B n T ω)) ≤ _
  rw [dist_prod_same_left]
  apply (dist_pi_le_iff (by positivity : (0 : ℝ) ≤ 1 / ((n : ℝ) * ε))).mpr
  intro i
  rw [Real.dist_eq, abs_sub_comm]
  exact abs_finiteHeightApprox_sub_discreteOccupation_le B hn hB T ω (ht i) hε

/-- **Fixed-`ε` joint convergence in law** of (scaled walk, discrete `ε`-occupations) to
(`X`, `heightApprox ε`), for `ε` outside a countable exceptional set (depending on the times). -/
theorem tendsto_joint_occupation {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) {r : ℕ} (t : Fin r → ℝ≥0)
    (ht : ∀ i, t i ≤ T) :
    ∃ Exc : Set ℝ, Exc.Countable ∧ ∀ ε : ℝ, 0 < ε → ε ∉ Exc →
      Tendsto (fun n : ℕ => (offspringSeqLaw μ).map (discreteJoint B n T ε t)) atTop
        (𝓝 ((stableLocalLaw θ).map (continuumJoint T ε t))) := by
  obtain ⟨Exc, hExc, hlim⟩ := tendsto_joint_finiteOccupation h hT t ht
  refine ⟨Exc, hExc, fun ε hε hexc => ?_⟩
  have hF (n : ℕ) := measurable_discreteJoint B n T ε t
  have hG (n : ℕ) : Measurable (fun ω =>
      finiteOccupationJoint T ε t (forestWalkPath B n T ω)) :=
    (measurable_finiteOccupationJoint T ε t).comp (measurable_forestPairPath B n T).fst
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun _ => offspringSeqLaw μ) hF hG _ (hlim ε hε hexc)
  intro δ hδ
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) * ε)) atTop (𝓝 0) := by
    have hi : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    have ht' := hi.div_const ε
    simpa only [zero_div, div_div] using
      (ht' : Tendsto (fun n : ℕ => (1 / (n : ℝ)) / ε) atTop (𝓝 (0 / ε)))
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1, hzero.eventually (gt_mem_nhds hδ)] with n hn hdn
  have hn' : 0 < n := by omega
  have hset : {ω | δ < dist (discreteJoint B n T ε t ω)
      (finiteOccupationJoint T ε t (forestWalkPath B n T ω))} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ω hω
    exact (lt_of_lt_of_le hω (dist_discreteJoint_finiteOccupationJoint_le B hn'
      (h.pos n hn) T t ht ω hε)).not_ge hdn.le
  simp only [hset, measureReal_empty]

/-- A countable set can be avoided by a positive sequence tending to zero. -/
theorem exists_bandSeq_avoiding {Exc : Set ℝ} (hExc : Exc.Countable) :
    ∃ e : ℕ → ℝ, (∀ n, 0 < e n ∧ e n ∉ Exc) ∧ Tendsto e atTop (𝓝[>] 0) := by
  have he (n : ℕ) : ∃ ε : ℝ, ε ∉ Exc ∧ ε ∈ Ioo 0 (1 / ((n : ℝ) + 1)) :=
    (hExc.dense_compl ℝ).exists_between (by positivity)
  choose e he using he
  have hlim : Tendsto e atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      tendsto_one_div_add_atTop_nhds_zero_nat
    · exact Eventually.of_forall fun n => (he n).2.1.le
    · exact Eventually.of_forall fun n => (he n).2.2.le
  refine ⟨e, fun n => ⟨(he n).2.1, (he n).1⟩, ?_⟩
  exact tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall fun n => (he n).2.1⟩

private theorem continuumJoint_tendsto {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (T : ℝ≥0) {r : ℕ} (t : Fin r → ℝ≥0) {e : ℕ → ℝ}
    (he : Tendsto e atTop (𝓝[>] 0)) :
    Tendsto (fun u => (stableLocalLaw θ).map (continuumJoint T (e u) t)) atTop
      (𝓝 ((stableLocalLaw θ).map (heightLimitJoint θ T t))) := by
  have hcoord (i : Fin r) (δ : ℝ) (hδ : 0 < δ) :
      Tendsto (fun ε : ℝ => (stableLocalLaw θ).toMeasure
        {f | δ < |heightApprox ε f (t i) - height θ f (t i)|}) (𝓝[>] 0) (𝓝 0) := by
    have ht := (tendstoInMeasure_iff_dist.mp (heightApprox_tendstoInMeasure hθ (t i))) δ hδ
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    · exact Eventually.of_forall fun _ => bot_le
    · exact Eventually.of_forall fun ε => measure_mono fun f hf => by
        change δ ≤ dist (heightApprox ε f (t i)) (height θ f (t i))
        rw [Real.dist_eq]
        exact le_of_lt hf
  have hvec (δ : ℝ) (hδ : 0 < δ) : Tendsto (fun ε : ℝ => (stableLocalLaw θ).toMeasure
      {f | δ ≤ dist (continuumJoint T ε t f) (heightLimitJoint θ T t f)})
        (𝓝[>] 0) (𝓝 0) := by
    have hc (i : Fin r) (d : ℝ) (hd : 0 < d) :
        Tendsto (fun ε : ℝ => limsup (fun _ : ℕ => (stableLocalLaw θ).toMeasure
          {f | d < |heightApprox ε f (t i) - height θ f (t i)|}) atTop) (𝓝[>] 0) (𝓝 0) := by
      simpa only [limsup_const] using hcoord i d hd
    have hv := tendsto_limsup_prod_pi_error (fun _ => stableLocalLaw θ)
      (fun _ f => DLoc.restrict T f) (fun ε _ f i => heightApprox ε f (t i))
      (fun _ f i => height θ f (t i)) hc hδ
    simpa only [limsup_const, continuumJoint, heightLimitJoint] using hv
  apply BGW.MetricMeasure.tendsto_probabilityMap_of_error_probability
    (fun _ => stableLocalLaw θ) (fun u => measurable_continuumJoint T (e u) t)
    (fun _ => measurable_heightLimitJoint θ T t) _ tendsto_const_nhds
  intro δ hδ
  have ht := (ENNReal.tendsto_toReal (by simp : (0 : ℝ≥0∞) ≠ ∞)).comp ((hvec δ hδ).comp he)
  simp only [Function.comp_def, ENNReal.toReal_zero] at ht
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
  · exact Eventually.of_forall fun _ => measureReal_nonneg
  · exact Eventually.of_forall fun u => measureReal_mono (μ := (stableLocalLaw θ).toMeasure)
      (fun f hf => by
        change δ ≤ dist (continuumJoint T (e u) t f) (heightLimitJoint θ T t f)
        exact le_of_lt hf)

/-- **Joint walk/height finite-dimensional convergence** (the K09 deliverable, fixed times,
no `H03`): `(forestWalkPath, (B_n/n) H_{⌊n t_i⌋}) ⇒ (X, height θ X (t_i))`. -/
theorem tendsto_walk_height_fdd {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ≥0} (hT : 0 < T) {r : ℕ} (t : Fin r → ℝ≥0)
    (ht : ∀ i, t i ≤ T) :
    Tendsto (fun n : ℕ => (offspringSeqLaw μ).map (heightJoint B n T t)) atTop
      (𝓝 ((stableLocalLaw θ).map (heightLimitJoint θ T t))) := by
  obtain ⟨Exc, hExc, hfixed⟩ := tendsto_joint_occupation h hT t ht
  obtain ⟨e, hepos, he⟩ := exists_bandSeq_avoiding hExc
  apply BGW.Probability.tendsto_of_tendsto_approx (fun _ => offspringSeqLaw μ)
    (X := fun u n => discreteJoint B n T (e u) t)
    (Z := fun u => (stableLocalLaw θ).map (continuumJoint T (e u) t))
    (fun n => measurable_heightJoint B n T t)
    (fun u n => measurable_discreteJoint B n T (e u) t)
    (fun u => hfixed (e u) (hepos u).1 (hepos u).2)
    (continuumJoint_tendsto h.alpha_mem T t he)
  intro δ hδ
  have hc (i : Fin r) (d : ℝ) (hd : 0 < d) :
      Tendsto (fun ε : ℝ => limsup (fun n => (offspringSeqLaw μ).toMeasure
        {ω | d < |discreteOccupation B n ε ω (t i) - scaledHeight B n ω (t i)|}) atTop)
          (𝓝[>] 0) (𝓝 0) := by
    simpa only [abs_sub_comm] using occupation_error_twoLimit h (t i) hd
  have hv := tendsto_limsup_prod_pi_error (fun _ => offspringSeqLaw μ)
    (fun n ω => forestWalkPath B n T ω) (fun ε n ω i => discreteOccupation B n ε ω (t i))
    (fun n ω i => scaledHeight B n ω (t i)) hc hδ
  have hv' : Tendsto (fun ε : ℝ => limsup (fun n => (offspringSeqLaw μ).toMeasure
      {ω | δ ≤ dist (discreteJoint B n T ε t ω) (heightJoint B n T t ω)}) atTop)
        (𝓝[>] 0) (𝓝 0) := hv
  exact (tendsto_limsup_measureReal_of_measure (fun _ => offspringSeqLaw μ) _ hv').comp he

/-- **Normalization at `θ = 2`**: the limit height is `X_t - I_t`, with constant exactly `1`
(`B_n = σ√(n/2)`, library variance-2 process). -/
theorem tendsto_walk_height_fdd_two {μ : PMF ℕ} {B : ℕ → ℝ}
    (h : StableDomain μ 2 B) {T : ℝ≥0} (hT : 0 < T) {r : ℕ} (t : Fin r → ℝ≥0)
    (ht : ∀ i, t i ≤ T) :
    Tendsto (fun n : ℕ => (offspringSeqLaw μ).map (heightJoint B n T t)) atTop
      (𝓝 ((stableLocalLaw 2).map
        (fun f : DLoc => (DLoc.restrict T f, fun i => f.1 (t i) - futureInf f (t i) 0)))) := by
  have hconv := tendsto_walk_height_fdd h hT t ht
  have hmap : (stableLocalLaw 2).map (heightLimitJoint 2 T t) =
      (stableLocalLaw 2).map
        (fun f : DLoc => (DLoc.restrict T f, fun i => f.1 (t i) - futureInf f (t i) 0)) := by
    apply Subtype.ext
    change (stableLocalLaw 2).toMeasure.map _ = (stableLocalLaw 2).toMeasure.map _
    apply Measure.map_congr
    filter_upwards [ae_all_iff.mpr (fun i => ae_height_two (t i))] with f hf
    change (DLoc.restrict T f, fun i => height 2 f (t i)) = _
    congr 1
    funext i
    exact hf i
  rw [hmap] at hconv
  exact hconv

end BGW.StableTrees.DiscreteHeightApprox
