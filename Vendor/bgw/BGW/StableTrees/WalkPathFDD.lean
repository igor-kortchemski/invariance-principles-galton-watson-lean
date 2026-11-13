/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Measurable
public import BGW.StableTrees.StableLaw
public import BGW.StableTrees.StableLevyLaw
public import BGW.StableTrees.RealAttractionBounds
public import BGW.StableTrees.WalkPathTightness
public import BGW.Probability.RealWalk
public import Mathlib.MeasureTheory.Measure.FiniteMeasurePi

import BGW.Probability.WeakConvergence

/-!
# Finite-dimensional limits of real walk step paths

The increments of a floor-step path are sums over disjoint blocks of the iid walk. Their exact
product law at each index and scalar convergence of each block give the finite-dimensional limits.

This is the finite-dimensional half of the functional limit theorem for walks in a stable domain
of attraction (item C17 of `CLASSICAL_THEORY_INPUTS.md`; Skorokhod 1957, Theorem 2.7).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

namespace BGW.StableTrees

open BGW.Probability.RealWalk BGW.Skorokhod

/-! ## Increment maps and stable increment laws -/

/-- The increment vector `(f t_1 - f t_0, …, f t_k - f t_{k-1})` of a path at the times `t`. -/
def incrementsMap {T : ℝ} {k : ℕ} (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) :
    D T ℝ → (Fin k → ℝ) := fun f i => f (t i.succ) - f (t i.castSucc)

theorem measurable_incrementsMap {T : ℝ} {k : ℕ} (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) :
    Measurable (incrementsMap t) := by
  apply Measurable.of_eval
  intro i
  exact (BGW.Skorokhod.measurable_eval (t i.succ)).sub
    (BGW.Skorokhod.measurable_eval (t i.castSucc))

/-- The product of the stable increment laws at a finite family of times
(Node 10; the underlying measure is `Measure.pi (fun i => stableLawAt θ (t (i+1) - t i))`). -/
noncomputable def incrementVectorLaw (θ : ℝ) {k : ℕ} (t : Fin (k + 1) → ℝ) :
    ProbabilityMeasure (Fin k → ℝ) :=
  ProbabilityMeasure.pi (fun i : Fin k => stableLawAt θ (t i.succ - t i.castSucc))

theorem coe_incrementVectorLaw (θ : ℝ) {k : ℕ} (t : Fin (k + 1) → ℝ) :
    (incrementVectorLaw θ t : Measure (Fin k → ℝ)) =
      Measure.pi (fun i : Fin k => (stableLawAt θ (t i.succ - t i.castSucc) : Measure ℝ)) := by
  rfl

/-- Consistency with the characterization: a law with `IsStableLevyLaw.increments` has exactly the
increment law `incrementVectorLaw` along every strictly increasing family starting at `0`. -/
theorem IsStableLevyLaw.map_incrementsMap {θ T : ℝ} {P : ProbabilityMeasure (D T ℝ)}
    (hP : IsStableLevyLaw θ T P) {k : ℕ} (t : Fin (k + 1) → Set.Icc (0 : ℝ) T)
    (ht : StrictMono t) (ht0 : (t 0 : ℝ) = 0) :
    P.map (incrementsMap t) = incrementVectorLaw θ (fun i => (t i : ℝ)) := by
  apply Subtype.ext
  change Measure.map (incrementsMap t) (P : Measure (D T ℝ)) =
    Measure.pi (fun i : Fin k =>
      (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc) : Measure ℝ))
  exact hP.increments k t ht ht0

/-- The step path starts at `0` with the exact increments being block sums: for `0 ≤ s ≤ u`,
`path u - path s = blockSum ω ⌊n s⌋₊ (⌊n u⌋₊ - ⌊n s⌋₊) / b`. -/
theorem realStepPath_sub {T : ℝ} (n : ℕ) (b : ℝ) (ω : ℕ → ℝ) (s u : Set.Icc (0 : ℝ) T)
    (hsu : s ≤ u) :
    realStepPath T n b ω u - realStepPath T n b ω s =
      blockSum ω ⌊(n : ℝ) * s⌋₊ (⌊(n : ℝ) * u⌋₊ - ⌊(n : ℝ) * s⌋₊) / b := by
  rw [realStepPath_apply, realStepPath_apply]
  let a := ⌊(n : ℝ) * (s : ℝ)⌋₊
  let c := ⌊(n : ℝ) * (u : ℝ)⌋₊
  have hac : a ≤ c := by
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left hsu (Nat.cast_nonneg n)
  have hidx : a + (c - a) = c := Nat.add_sub_of_le hac
  have hsum : partialSum ω c = partialSum ω a + blockSum ω a (c - a) := by
    rw [← hidx, partialSum_add]
    rw [Nat.add_sub_cancel_left]
  change partialSum ω c / b - partialSum ω a / b = blockSum ω a (c - a) / b
  rw [hsum]
  ring

/-- Exact finite-dimensional structure for every `n` (Node 1 block independence, valid even when
blocks are empty): along a monotone family of times the increments of the step path are
independent, with the laws of the normalized block sums of lengths
`⌊n t_{i+1}⌋₊ - ⌊n t_i⌋₊`. -/
theorem map_stepPathLaw_incrementsMap (ν : ProbabilityMeasure ℝ) (T : ℝ) (B : ℕ → ℝ) (n : ℕ)
    {k : ℕ} (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) (ht : Monotone t) :
    ((stepPathLaw ν T B n).map (incrementsMap t) : Measure (Fin k → ℝ)) =
      Measure.pi (fun i : Fin k =>
        (sumLaw ν (⌊(n : ℝ) * t i.succ⌋₊ - ⌊(n : ℝ) * t i.castSucc⌋₊) : Measure ℝ).map
          (fun x => x / B n)) := by
  let a : Fin k → ℕ := fun i => ⌊(n : ℝ) * (t i.castSucc : ℝ)⌋₊
  let e : Fin k → ℕ := fun i => ⌊(n : ℝ) * (t i.succ : ℝ)⌋₊
  let m : Fin k → ℕ := fun i => e i - a i
  have hae : ∀ i, a i ≤ e i := by
    intro i
    apply Nat.floor_mono
    exact mul_le_mul_of_nonneg_left (ht (Fin.castSucc_le_succ i)) (Nat.cast_nonneg n)
  have hdisj : ∀ i j : Fin k, i < j → a i + m i ≤ a j := by
    intro i j hij
    have hij' : i.succ ≤ j.castSucc := by
      apply Fin.le_iff_val_le_val.mpr
      change i.val + 1 ≤ j.val
      omega
    have htime : t i.succ ≤ t j.castSucc := ht hij'
    have heaj : e i ≤ a j := by
      apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left htime (Nat.cast_nonneg n)
    have hsum : a i + m i = e i := Nat.add_sub_of_le (hae i)
    exact hsum ▸ heaj
  have hind : iIndepFun (fun i (ω : ℕ → ℝ) => blockSum ω (a i) (m i))
      (iidLaw ν : Measure (ℕ → ℝ)) := iIndepFun_blockSum ν a m hdisj
  have hmeas (i : Fin k) :
      AEMeasurable (fun ω : ℕ → ℝ => blockSum ω (a i) (m i) / B n)
        (iidLaw ν : Measure (ℕ → ℝ)) :=
    ((measurable_blockSum (a i) (m i)).div_const (B n)).aemeasurable
  have hscaled : Measure.map (fun ω (i : Fin k) => blockSum ω (a i) (m i) / B n)
      (iidLaw ν : Measure (ℕ → ℝ)) =
      Measure.pi (fun i : Fin k =>
        (sumLaw ν (m i) : Measure ℝ).map (fun x => x / B n)) := by
    calc
      Measure.map (fun ω (i : Fin k) => blockSum ω (a i) (m i) / B n)
          (iidLaw ν : Measure (ℕ → ℝ)) =
      Measure.pi (fun i : Fin k => Measure.map
          (fun ω : ℕ → ℝ => blockSum ω (a i) (m i) / B n)
          (iidLaw ν : Measure (ℕ → ℝ))) := by
        have hind' := hind.comp (fun _ x => x / B n) (fun _ => by fun_prop)
        exact iIndepFun.map_fun_eq_pi_map hmeas hind'
      _ = Measure.pi (fun i : Fin k =>
          (sumLaw ν (m i) : Measure ℝ).map (fun x => x / B n)) := by
        congr 1
        funext i
        calc
          Measure.map (fun ω : ℕ → ℝ => blockSum ω (a i) (m i) / B n)
              (iidLaw ν : Measure (ℕ → ℝ)) =
            Measure.map (fun x : ℝ => x / B n)
              (Measure.map (fun ω : ℕ → ℝ => blockSum ω (a i) (m i))
                (iidLaw ν : Measure (ℕ → ℝ))) := by
              exact (Measure.map_map (g := fun x : ℝ => x / B n)
                (f := fun ω : ℕ → ℝ => blockSum ω (a i) (m i))
                (measurable_id.div_const _) (measurable_blockSum (a i) (m i))).symm
          _ = (sumLaw ν (m i) : Measure ℝ).map (fun x => x / B n) := by
            rw [iidLaw_map_blockSum]
  have hfun : (incrementsMap t ∘ realStepPath T n (B n)) =
      (fun ω i => blockSum ω (a i) (m i) / B n) := by
    funext ω i
    dsimp [incrementsMap, a, e, m, Function.comp_apply]
    exact realStepPath_sub n (B n) ω (t i.castSucc) (t i.succ)
      (ht (Fin.castSucc_le_succ i))
  change Measure.map (incrementsMap t)
      (Measure.map (realStepPath T n (B n)) (iidLaw ν : Measure (ℕ → ℝ))) = _
  rw [Measure.map_map (measurable_incrementsMap t) (measurable_realStepPath T n (B n)), hfun]
  simpa [a, e, m] using hscaled

private theorem tendsto_map_mul_of_tendsto {μ : ℕ → ProbabilityMeasure ℝ}
    {P : ProbabilityMeasure ℝ} {r : ℕ → ℝ} {c : ℝ}
    (hμ : Tendsto μ atTop (𝓝 P)) (hr : Tendsto r atTop (𝓝 c)) :
    Tendsto (fun n => (μ n).map (fun x => x * r n)) atTop
      (𝓝 (P.map (fun x => x * c))) := by
  have hμid : Tendsto (fun n => (μ n).map (fun x : ℝ => x)) atTop (𝓝 P) := by
    apply hμ.congr'
    exact Filter.Eventually.of_forall fun n => by
      symm
      apply Subtype.ext
      change Measure.map (fun x : ℝ => x) (μ n : Measure ℝ) = (μ n : Measure ℝ)
      rw [Measure.map_id']
  have hpair := BGW.Probability.tendsto_map_prodMk_of_tendsto_of_error μ
    (X := fun _ x => x) (Y := fun n _ => r n)
    (fun _ => measurable_id) (fun _ => measurable_const) hμid (by
      intro ε hε
      have hevent : ∀ᶠ n in atTop, dist (r n) c < ε :=
        (Metric.tendsto_nhds.1 hr) ε hε
      have hzero : ∀ᶠ n in atTop,
          (μ n : Measure ℝ).real {x | ε < dist (r n) c} = 0 := by
        filter_upwards [hevent] with n hn
        have hset : {x : ℝ | ε < dist (r n) c} = ∅ := by
          ext x
          simp [not_lt_of_ge hn.le]
        simp [hset]
      exact tendsto_const_nhds.congr' (hzero.mono fun _ hn => hn.symm))
  have hmul : Continuous (fun p : ℝ × ℝ => p.1 * p.2) := by fun_prop
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => (μ n).map (fun x => (x, r n))) (P.map (fun x => (x, c))) hpair hmul
  have hseq (n : ℕ) :
      ((μ n).map (fun x => (x, r n))).map (fun p : ℝ × ℝ => p.1 * p.2) =
        (μ n).map (fun x => x * r n) := by
    apply Subtype.ext
    change Measure.map (fun p : ℝ × ℝ => p.1 * p.2)
        (Measure.map (fun x : ℝ => (x, r n)) (μ n : Measure ℝ)) =
      Measure.map (fun x : ℝ => x * r n) (μ n : Measure ℝ)
    rw [Measure.map_map hmul.measurable (by fun_prop)]
    rfl
  have hlim : (P.map (fun x => (x, c))).map (fun p : ℝ × ℝ => p.1 * p.2) =
      P.map (fun x => x * c) := by
    apply Subtype.ext
    change Measure.map (fun p : ℝ × ℝ => p.1 * p.2)
        (Measure.map (fun x : ℝ => (x, c)) (P : Measure ℝ)) =
      Measure.map (fun x : ℝ => x * c) (P : Measure ℝ)
    rw [Measure.map_map hmul.measurable (by fun_prop)]
    rfl
  simpa only [hseq, hlim] using hmap

/-- Scalar step (Node 4 + Slutsky): for `0 ≤ a < b` the normalized block sum of length
`⌊n b⌋₊ - ⌊n a⌋₊` (normalized by `B n`, NOT by the block's own normalizer) converges to
`stableLawAt θ (b - a)`. The length is `~ (b - a) n`, so `B (m n) / B n → (b - a)^{1/θ}`. -/
theorem IsRealStableAttracted.tendsto_scaled_block_law {ν : ProbabilityMeasure ℝ} {θ : ℝ}
    {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {a b : ℝ} (ha : 0 ≤ a) (hab : a < b) :
    Tendsto (fun n : ℕ => (sumLaw ν (⌊(n : ℝ) * b⌋₊ - ⌊(n : ℝ) * a⌋₊)).map (fun x => x / B n))
      atTop (𝓝 (stableLawAt θ (b - a))) := by
  let m : ℕ → ℕ := fun n => ⌊(n : ℝ) * b⌋₊ - ⌊(n : ℝ) * a⌋₊
  have hb : 0 ≤ b := le_trans ha hab.le
  have hratio : Tendsto (fun n : ℕ => (m n : ℝ) / n) atTop (𝓝 (b - a)) := by
    have hb' := (tendsto_nat_floor_mul_div_atTop (R := ℝ) hb).comp
      tendsto_natCast_atTop_atTop
    have ha' := (tendsto_nat_floor_mul_div_atTop (R := ℝ) ha).comp
      tendsto_natCast_atTop_atTop
    have hsub := hb'.sub ha'
    apply hsub.congr'
    filter_upwards [eventually_ne_atTop 0] with n hn
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hfloor : ⌊(n : ℝ) * a⌋₊ ≤ ⌊(n : ℝ) * b⌋₊ := by
      apply Nat.floor_mono
      exact mul_le_mul_of_nonneg_left hab.le (Nat.cast_nonneg n)
    dsimp [m]
    rw [Nat.cast_sub hfloor]
    field_simp [hn']
  have hm : Tendsto m atTop atTop := by
    have hm' : Tendsto (fun n : ℕ => (m n : ℝ)) atTop atTop := by
      have hp : Tendsto (fun n : ℕ => ((m n : ℝ) / n) * n) atTop atTop :=
        Tendsto.pos_mul_atTop (by linarith) hratio tendsto_natCast_atTop_atTop
      apply hp.congr'
      filter_upwards [eventually_ne_atTop 0] with n hn
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
      field_simp
    exact tendsto_natCast_atTop_iff.1 hm'
  have hratioB : Tendsto (fun n => B (m n) / B n) atTop
      (𝓝 ((b - a) ^ (1 / θ))) :=
    h.tendsto_norming_ratio (sub_pos.mpr hab) tendsto_natCast_atTop_atTop hratio
  have hscaled : Tendsto (fun n => scaledSumLaw ν B (m n)) atTop (𝓝 (stableLaw θ)) :=
    h.converges.comp hm
  have hmul := tendsto_map_mul_of_tendsto hscaled hratioB
  have hpos : ∀ᶠ n in atTop, 0 < B (m n) := hm.eventually h.pos
  have hEq : ∀ᶠ n in atTop,
      (scaledSumLaw ν B (m n)).map (fun x => x * (B (m n) / B n)) =
        (sumLaw ν (m n)).map (fun x => x / B n) := by
    filter_upwards [hpos] with n hBn
    apply Subtype.ext
    change Measure.map (fun x : ℝ => x * (B (m n) / B n))
        (Measure.map (fun x => x / B (m n)) (sumLaw ν (m n) : Measure ℝ)) = _
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    change Measure.map (fun x : ℝ => (x / (B (m n)) * (B (m n) / B n)))
      (sumLaw ν (m n) : Measure ℝ) =
      Measure.map (fun x : ℝ => x / B n) (sumLaw ν (m n) : Measure ℝ)
    congr 1
    funext x
    by_cases hB : B n = 0
    · simp [hB]
    · field_simp [hBn.ne', hB]
  have hfinal := hmul.congr' hEq
  have hscale :
      (stableLaw θ).map (fun x => x * (b - a) ^ (1 / θ)) = stableLawAt θ (b - a) := by
    apply Subtype.ext
    change Measure.map (fun x : ℝ => x * (b - a) ^ (1 / θ))
        (stableLaw θ : Measure ℝ) = _
    simp only [stableLawAt]
    congr 1
    funext x
    ring
  exact hscale ▸ hfinal

/-- Node 10: the finite-dimensional increments of the step paths converge to the product of the
stable increments at any finite strictly increasing family of times in `[0,T]` (not necessarily
starting at `0`; the terminal time `T` is allowed). -/
theorem IsRealStableAttracted.tendsto_stepPathLaw_increments {ν : ProbabilityMeasure ℝ}
    {θ : ℝ} {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} {k : ℕ}
    (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) (ht : StrictMono t) :
    Tendsto (fun n => (stepPathLaw ν T B n).map (incrementsMap t)) atTop
      (𝓝 (incrementVectorLaw θ (fun i => (t i : ℝ)))) := by
  let μ : ℕ → Fin k → ProbabilityMeasure ℝ := fun n i =>
    (sumLaw ν (⌊(n : ℝ) * t i.succ⌋₊ - ⌊(n : ℝ) * t i.castSucc⌋₊)).map
      (fun x => x / B n)
  have hμ : ∀ i : Fin k,
      Tendsto (fun n => μ n i) atTop
        (𝓝 (stableLawAt θ ((t i.succ : ℝ) - t i.castSucc))) := by
    intro i
    apply h.tendsto_scaled_block_law (t i.castSucc).property.1
    have hi : i.castSucc < i.succ := Fin.castSucc_lt_succ
    exact ht hi
  have hμ' : Tendsto μ atTop (𝓝 fun i : Fin k =>
      stableLawAt θ ((t i.succ : ℝ) - t i.castSucc)) := by
    apply tendsto_pi_nhds.2
    intro i
    exact hμ i
  have hprod := ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp hμ'
  have heq (n : ℕ) : (stepPathLaw ν T B n).map (incrementsMap t) =
      ProbabilityMeasure.pi (fun i : Fin k => μ n i) := by
    apply Subtype.ext
    change Measure.map (incrementsMap t)
        (stepPathLaw ν T B n : Measure (D T ℝ)) =
      Measure.pi (fun i : Fin k =>
        ((sumLaw ν (⌊(n : ℝ) * t i.succ⌋₊ - ⌊(n : ℝ) * t i.castSucc⌋₊) :
          Measure ℝ).map (fun x => x / B n)))
    exact map_stepPathLaw_incrementsMap ν T B n t ht.monotone
  have hprod' : Tendsto (fun n => (stepPathLaw ν T B n).map (incrementsMap t)) atTop
      (𝓝 (ProbabilityMeasure.pi (fun i : Fin k =>
        stableLawAt θ ((t i.succ : ℝ) - t i.castSucc)))) := by
    exact hprod.congr' (Filter.Eventually.of_forall fun n => (heq n).symm)
  simpa only [incrementVectorLaw] using hprod'

/-- Partial sums of an increment vector (positions from increments, starting value `0`). -/
def cumulativeSum {k : ℕ} (x : Fin k → ℝ) : Fin k → ℝ :=
  fun j => ∑ i ∈ Finset.univ.filter (fun i : Fin k => i ≤ j), x i

private theorem cumulativeSum_sub_eval {k : ℕ} (y : Fin (k + 1) → ℝ) (j : Fin k) :
    cumulativeSum (fun i : Fin k => y i.succ - y i.castSucc) j = y j.succ - y 0 := by
  classical
  let g : ℕ → ℝ := fun n => if hn : n ≤ k then y ⟨n, by omega⟩ else 0
  have hfilter : (∑ i ∈ Finset.univ.filter (fun i : Fin k => i ≤ j),
      (y i.succ - y i.castSucc)) =
      ∑ n ∈ Finset.range (j.val + 1), (g (n + 1) - g n) := by
    apply Finset.sum_bij' (fun i hi => i.val)
      (fun n hn => (⟨n, by
        have hn' := Finset.mem_range.mp hn
        exact Nat.lt_of_lt_of_le hn' (Nat.succ_le_iff.mpr j.isLt)⟩ : Fin k))
      ?_ ?_ ?_ ?_ ?_
    · intro i hi
      simp only [Finset.mem_range]
      exact Nat.lt_succ_of_le
        (Fin.le_iff_val_le_val.mp (Finset.mem_filter.mp hi).2)
    · intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      apply Fin.le_iff_val_le_val.mpr
      exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    · intro i hi
      apply Fin.ext
      rfl
    · intro n hn
      rfl
    · intro i hi
      have hbound : i.val + 1 ≤ k := by omega
      have hbound0 : i.val ≤ k := by omega
      have hg1 : g (i.val + 1) = y i.succ := by
        dsimp [g]
        rw [dite_eq_left hbound]
        have heq : (⟨i.val + 1, by omega⟩ : Fin (k + 1)) = i.succ := by
          apply Fin.ext
          rfl
        rw [heq]
      have hg0 : g i.val = y i.castSucc := by
        dsimp [g]
        rw [dite_eq_left hbound0]
        have heq : (⟨i.val, by omega⟩ : Fin (k + 1)) = i.castSucc := by
          apply Fin.ext
          rfl
        rw [heq]
      rw [hg1, hg0]
  unfold cumulativeSum
  rw [hfilter, Finset.sum_range_sub]
  have hjk : j.val + 1 ≤ k := Nat.succ_le_of_lt j.isLt
  have heq : (⟨j.val + 1, by omega⟩ : Fin (k + 1)) = j.succ := by
    apply Fin.ext
    rfl
  simp [g, hjk, heq]

private theorem continuous_cumulativeSum {k : ℕ} :
    Continuous (cumulativeSum (k := k)) := by
  fun_prop [cumulativeSum]

/-- Position form, starting at `0` (the family `t` has `t 0 = 0`): the vector
`(f t_1, …, f t_k)` converges to the cumulative sum of the independent stable increments
(`f t_0 = f 0 = 0` for every step path). -/
theorem IsRealStableAttracted.tendsto_stepPathLaw_positions {ν : ProbabilityMeasure ℝ}
    {θ : ℝ} {B : ℕ → ℝ} (h : IsRealStableAttracted ν θ B) {T : ℝ} {k : ℕ}
    (t : Fin (k + 1) → Set.Icc (0 : ℝ) T) (ht : StrictMono t) (ht0 : (t 0 : ℝ) = 0) :
    Tendsto (fun n => (stepPathLaw ν T B n).map (fun f : D T ℝ => fun i : Fin k => f (t i.succ)))
      atTop
      (𝓝 ((incrementVectorLaw θ (fun i => (t i : ℝ))).map cumulativeSum)) := by
  have hinc := h.tendsto_stepPathLaw_increments t ht
  have hmap := ProbabilityMeasure.tendsto_map_of_tendsto_of_continuous
    (fun n => (stepPathLaw ν T B n).map (incrementsMap t))
    (incrementVectorLaw θ (fun i => (t i : ℝ))) hinc continuous_cumulativeSum
  have hT : 0 ≤ T := by
    have h := (t 0).property.2
    rw [ht0] at h
    exact h
  have htZero : t 0 = ⟨0, le_rfl, hT⟩ := Subtype.ext ht0
  have hposmeas : Measurable (fun f : D T ℝ => fun i : Fin k => f (t i.succ)) := by
    apply Measurable.of_eval
    intro i
    exact BGW.Skorokhod.measurable_eval (t i.succ)
  have hpositions (n : ℕ) :
      (stepPathLaw ν T B n).map (fun f : D T ℝ => fun i : Fin k => f (t i.succ)) =
        ((stepPathLaw ν T B n).map (incrementsMap t)).map cumulativeSum := by
    apply Subtype.ext
    change Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ))
        (Measure.map (realStepPath T n (B n)) (iidLaw ν : Measure (ℕ → ℝ))) =
      Measure.map cumulativeSum
        (Measure.map (incrementsMap t)
          (Measure.map (realStepPath T n (B n)) (iidLaw ν : Measure (ℕ → ℝ))))
    have hfun :
        (fun ω : ℕ → ℝ => (fun f : D T ℝ => fun i : Fin k => f (t i.succ))
          (realStepPath T n (B n) ω)) =
        (fun ω => cumulativeSum (incrementsMap t (realStepPath T n (B n) ω))) := by
      funext ω
      funext j
      change realStepPath T n (B n) ω (t j.succ) =
        cumulativeSum (fun i : Fin k =>
          realStepPath T n (B n) ω (t i.succ) - realStepPath T n (B n) ω (t i.castSucc)) j
      rw [cumulativeSum_sub_eval (fun q => realStepPath T n (B n) ω (t q)) j,
        htZero, realStepPath_apply_zero hT n (B n) ω]
      simp
    calc
      Measure.map (fun f : D T ℝ => fun i : Fin k => f (t i.succ))
          (Measure.map (realStepPath T n (B n)) (iidLaw ν : Measure (ℕ → ℝ))) =
        Measure.map ((fun f : D T ℝ => fun i : Fin k => f (t i.succ)) ∘
          realStepPath T n (B n)) (iidLaw ν : Measure (ℕ → ℝ)) :=
          Measure.map_map hposmeas (measurable_realStepPath T n (B n))
      _ = Measure.map (fun ω => cumulativeSum
          (incrementsMap t (realStepPath T n (B n) ω)))
          (iidLaw ν : Measure (ℕ → ℝ)) := by
          have hcomp :
              ((fun f : D T ℝ => fun i : Fin k => f (t i.succ)) ∘
                realStepPath T n (B n)) =
              (fun ω => cumulativeSum (incrementsMap t (realStepPath T n (B n) ω))) := by
            funext ω
            exact congrFun hfun ω
          rw [hcomp]
      _ = Measure.map cumulativeSum
          (Measure.map (incrementsMap t)
            (Measure.map (realStepPath T n (B n)) (iidLaw ν : Measure (ℕ → ℝ)))) := by
          have hcomp : (fun ω : ℕ → ℝ => cumulativeSum
              (incrementsMap t (realStepPath T n (B n) ω))) =
              ((cumulativeSum ∘ incrementsMap t) ∘ realStepPath T n (B n)) := by
            funext ω
            rfl
          rw [hcomp,
            ← Measure.map_map (continuous_cumulativeSum.measurable.comp
              (measurable_incrementsMap t)) (measurable_realStepPath T n (B n)),
            ← Measure.map_map continuous_cumulativeSum.measurable
              (measurable_incrementsMap t)]
  exact hmap.congr' (Filter.Eventually.of_forall fun n => (hpositions n).symm)

end BGW.StableTrees
