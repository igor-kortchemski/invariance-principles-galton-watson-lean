/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridgePrefix
public import BGW.StableTrees.DiscreteBridgeDensity
import BGW.Probability.Rounding
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.Floor

/-!
# Path prefix Radon–Nikodym identities for the discrete bridge

The conditional prefix-word masses are transported through the prefix path map.
Nonzero norming recovers the integer walk endpoint by rounding.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.Skorokhod BGW.Probability.RealWalk BGW.StableTrees.DiscreteForest

/-- Discrete measurable structure for the prefix-word carrier in this module. -/
local instance rnWordMeasurable : MeasurableSpace (List ℕ) := ⊤
/-- Every prefix-word singleton is measurable in the local structure. -/
local instance rnWordSingleton : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

private theorem map_cond_preimage {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (f : α → β) (hf : Measurable f) (A : Set β) (hA : MeasurableSet A) :
    (μ[|f ⁻¹' A]).map f = (μ.map f)[|A] := by
  ext S hS
  rw [Measure.map_apply hf hS, cond_apply' (hf hS), cond_apply' hS,
    Measure.map_apply hf hA, Measure.map_apply hf (hA.inter hS), preimage_inter]

private theorem map_withDensity_comp {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) {f : α → β} (hf : Measurable f) {w : β → ℝ≥0∞}
    (hw : Measurable w) :
    (μ.withDensity (w ∘ f)).map f = (μ.map f).withDensity w := by
  ext A hA
  rw [Measure.map_apply hf hA, withDensity_apply _ (hf hA), withDensity_apply _ hA,
    ← lintegral_indicator (hf hA), ← lintegral_indicator hA,
    lintegral_map (hw.indicator hA) hf]
  apply lintegral_congr
  intro x
  by_cases hx : f x ∈ A <;> simp [hx, Function.comp_def]

private theorem initial_bridge_preimage (n : ℕ) :
    (fun (ω : ℕ → ℕ) (i : Fin n) => ω i) ⁻¹' countBridges n = {ω | walk ω n = -1} := by
  ext ω
  have hs : (stepWord (fun i : Fin n => ω i)).sum = walk ω n := by
    rw [stepWord, List.sum_ofFn]
    exact Fin.sum_univ_eq_sum_range (fun j => (ω j : ℤ) - 1) n
  change (fun i : Fin n => ω i) ∈ countBridges n ↔ walk ω n = -1
  rw [← stepWord_mem_bridgeWords_iff]
  exact ⟨fun hx => hs ▸ hx.2.2, fun hw =>
    ⟨by simp [stepWord], fun j hj => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hj
      omega, hs.trans hw⟩⟩

private theorem bridge_endpoint_pos {μ : PMF ℕ} {n : ℕ} (hn : Admissible μ n) :
    0 < walkProb μ n (-1) := by
  have hm := offspringVec_countBridges_ne_zero hn
  have heq : offspringVec μ n (countBridges n) =
      (offspringSeqLaw μ).toMeasure {ω | walk ω n = -1} := by
    rw [offspringVec, ← map_offspringSeqLaw_initial μ n,
      Measure.map_apply (by fun_prop) (Set.to_countable _).measurableSet,
      initial_bridge_preimage]
  rw [heq] at hm
  rw [← walk_event_real]
  exact ENNReal.toReal_pos hm (measure_ne_top _ _)

private theorem seqPrefix_bridge_withDensity (μ : PMF ℕ) {n m : ℕ}
    (hmn : m ≤ n) (hp : 0 < walkProb μ n (-1)) :
    (((offspringSeqLaw μ).toMeasure)[|{ω | walk ω n = -1}]).map (seqPrefix m) =
      ((offspringSeqLaw μ).toMeasure.map (seqPrefix m)).withDensity
        (fun a => ENNReal.ofReal (bridgePrefixDensity μ n m (prefixWalk a))) := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.map_apply (measurable_seqPrefix m) (measurableSet_singleton a),
    withDensity_apply _ (measurableSet_singleton a), lintegral_singleton,
    Measure.map_apply (measurable_seqPrefix m) (measurableSet_singleton a)]
  change (((offspringSeqLaw μ).toMeasure)[|{ω | walk ω n = -1}])
    {ω | seqPrefix m ω = a} =
      ENNReal.ofReal (bridgePrefixDensity μ n m (prefixWalk a)) *
        (offspringSeqLaw μ).toMeasure {ω | seqPrefix m ω = a}
  by_cases ham : a.length = m
  · have h := congrArg ENNReal.ofReal (bridgePrefix_cond_mass μ ham hmn hp)
    simp only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
    rw [h, ENNReal.ofReal_mul (by exact ENNReal.toReal_nonneg), mul_comm]
    congr 1
    rw [← ham, seqPrefix_mass]
    exact ENNReal.ofReal_toReal (by
      have := measure_ne_top (offspringSeqLaw μ).toMeasure {ω | seqPrefix a.length ω = a}
      rwa [seqPrefix_mass] at this)
  · have he : {ω | seqPrefix m ω = a} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      intro h
      apply ham
      rw [← h, seqPrefix]
      simp
    rw [he, measure_empty, measure_empty, mul_zero]

private theorem forestWalkPath_prefix (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) (ω : ℕ → ℕ) :
    forestWalkPath B n a (fun i => (seqPrefix ⌊(a : ℝ) * n⌋₊ ω).getD i 0) =
      forestWalkPath B n a ω := by
  apply BGW.Skorokhod.ext
  intro t
  let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hk : k ≤ ⌊(a : ℝ) * n⌋₊ := by
    apply Nat.floor_mono
    nlinarith [t.2.2, show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
  change partialSum
    (fun i => (((seqPrefix ⌊(a : ℝ) * n⌋₊ ω).getD i 0 : ℤ) - 1 : ℝ)) k / B n =
    partialSum (fun i => ((ω i : ℤ) - 1 : ℝ)) k / B n
  congr 1
  unfold partialSum
  apply Finset.sum_congr rfl
  intro i hi
  have him : i < ⌊(a : ℝ) * n⌋₊ := (Finset.mem_range.mp hi).trans_le hk
  simp [seqPrefix, him]

private theorem initial_stepPath (B : ℕ → ℝ) (n : ℕ) (ω : ℕ → ℕ)
    (t : Set.Icc (0 : ℝ) 1) :
    vecPath B n (fun i : Fin n => ω i) t = forestWalkPath B n 1 ω t := by
  let k := ⌊(n : ℝ) * (t : ℝ)⌋₊
  have hk : k ≤ n := Nat.floor_le_of_le
    (mul_le_of_le_one_right (Nat.cast_nonneg n) t.2.2)
  have hstep : stepWord (fun i : Fin n => ω i) =
      (seqPrefix n ω).map (fun d : ℕ => (d : ℤ) - 1) := by
    simp only [stepWord, seqPrefix_eq_ofFn, List.map_ofFn, Function.comp_def]
  have hlist : (stepWord (fun i : Fin n => ω i)).take k =
      (seqPrefix k ω).map (fun d : ℕ => (d : ℤ) - 1) := by
    rw [hstep, ← List.map_take, take_seqPrefix n k ω hk]
  change (((stepWord (fun i : Fin n => ω i)).take
    ⌊((stepWord (fun i : Fin n => ω i)).length : ℝ) * (t : ℝ)⌋₊).sum : ℝ) / B n = _
  simp only [stepWord, List.length_ofFn] at *
  change (((List.ofFn (fun i : Fin n => (ω i : ℤ) - 1)).take k).sum : ℝ) / B n = _
  rw [hlist, sum_seqPrefix]
  change (walk ω k : ℝ) / B n = partialSum (fun i => ((ω i : ℤ) - 1 : ℝ)) k / B n
  simp [walk, partialSum]

/-- The path prefix density is measurable through its terminal coordinate. -/
theorem measurable_bridgePathDensity (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    Measurable (bridgePathDensity μ B n a) := by
  have he : Measurable (endValue a) := measurable_eval _
  have hr : Measurable (round : ℝ → ℤ) := BGW.Probability.measurable_round
  exact ((measurable_of_countable (fun z : ℤ =>
    walkProb μ ((n - ⌊(a : ℝ) * n⌋₊ : ℕ) : ℤ) (-1 - z))).comp
    (hr.comp (he.mul_const _))).div_const _

/-- The terminal value of a forest walk prefix is its integer partial sum divided by the norming. -/
theorem endValue_forestWalkPath (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) (ω : ℕ → ℕ) :
    endValue a (forestWalkPath B n a ω) = (walk ω ⌊(a : ℝ) * n⌋₊ : ℝ) / B n := by
  change partialSum (fun i => ((ω i : ℤ) - 1 : ℝ)) ⌊(n : ℝ) * a⌋₊ / B n = _
  rw [mul_comm (n : ℝ)]
  simp [walk, partialSum]

/-- The iid offspring sequence pushed through its prefix path has the canonical step-path law. -/
theorem map_forestWalkPath (μ : PMF ℕ) (B : ℕ → ℝ) (n : ℕ) (a : ℝ≥0) :
    (offspringSeqLaw μ).toMeasure.map (forestWalkPath B n a) =
      (stepPathLaw (realOffspringStepLaw μ) (a : ℝ) B n : Measure (D (a : ℝ) ℝ)) := by
  change (offspringSeqLaw μ).toMeasure.map
    (realStepPath (a : ℝ) n (B n) ∘ (fun ω i => ((ω i : ℤ) - 1 : ℝ))) = _
  rw [← Measure.map_map (measurable_realStepPath _ _ _) (by fun_prop),
    map_offspringSeqLaw_realIncrements]
  rfl

private theorem restrictLaw_bridge_eq_seq {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ}
    (hn : Admissible μ n) (a : ℝ≥0) (ha : a ≤ 1) :
    (restrictLaw a ha (walkBridgeLaw μ B n hn) : Measure (D (a : ℝ) ℝ)) =
      (((offspringSeqLaw μ).toMeasure)[|{ω | walk ω n = -1}]).map
        (forestWalkPath B n a) := by
  let r : (ℕ → ℕ) → Fin n → ℕ := fun ω i => ω i
  have hr : Measurable r := by fun_prop
  have haR : (a : ℝ) ≤ 1 := by exact_mod_cast ha
  let f := BGW.Skorokhod.restrict (E := ℝ) haR ∘ vecPath B n
  have hf : Measurable f := (measurable_restrict _).comp (measurable_vecPath B n)
  have hmcond : (((offspringSeqLaw μ).toMeasure)[|{ω | walk ω n = -1}]).map r =
      (offspringVec μ n)[|countBridges n] := by
    rw [← initial_bridge_preimage n, map_cond_preimage _ _ hr _
      (Set.to_countable _).measurableSet, map_offspringSeqLaw_initial]
    rfl
  have hpath : f ∘ r = forestWalkPath B n a := by
    funext ω
    apply BGW.Skorokhod.ext
    intro t
    exact initial_stepPath B n ω ⟨t, t.2.1, t.2.2.trans haR⟩
  change ((conditionedVecOrJunk μ n (countBridges n) : Measure (Fin n → ℕ)).map
    (vecPath B n)).map (BGW.Skorokhod.restrict haR) = _
  rw [Measure.map_map (measurable_restrict _) (measurable_vecPath B n),
    coe_conditionedVecOrJunk μ n _ (offspringVec_countBridges_ne_zero hn)]
  change ((offspringVec μ n)[|countBridges n]).map f = _
  rw [← hmcond, Measure.map_map hf hr, hpath]

/-- **Prefix Radon-Nikodym identity**: for `a < 1`, admissible `n` and nonzero norming `B n`
(without it the rounded endpoint loses the walk value: audit finding 1), the bridge path on
`[0,a]` has density `bridgePathDensity` with respect to the unconditioned step-path law. -/
theorem restrictLaw_walkBridgeLaw_eq_withDensity {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ}
    (hn : Admissible μ n) (hB : B n ≠ 0) (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    ((restrictLaw a ha.2.le (walkBridgeLaw μ B n hn) : ProbabilityMeasure (D (a : ℝ) ℝ)) :
        Measure (D (a : ℝ) ℝ)) =
      ((stepPathLaw (realOffspringStepLaw μ) (a : ℝ) B n :
          ProbabilityMeasure (D (a : ℝ) ℝ)) :
          Measure (D (a : ℝ) ℝ)).withDensity
        (fun x => ENNReal.ofReal (bridgePathDensity μ B n a x)) := by
  let m := ⌊(a : ℝ) * n⌋₊
  let p := seqPrefix m
  let g : List ℕ → D (a : ℝ) ℝ := fun l => forestWalkPath B n a (fun i => l.getD i 0)
  let d := fun x => ENNReal.ofReal (bridgePathDensity μ B n a x)
  have hp : Measurable p := measurable_seqPrefix m
  have hg : Measurable g := measurable_of_countable _
  have hd : Measurable d := ENNReal.measurable_ofReal.comp
    (measurable_bridgePathDensity μ B n a)
  have hfactor : g ∘ p = forestWalkPath B n a := by
    funext ω
    exact forestWalkPath_prefix B n a ω
  have hmn : m ≤ n := by
    apply Nat.floor_le_of_le
    have haR : (a : ℝ) ≤ 1 := by exact_mod_cast ha.2.le
    exact mul_le_of_le_one_left (Nat.cast_nonneg n) haR
  have heq : (fun l => ENNReal.ofReal (bridgePrefixDensity μ n m (prefixWalk l))) =ᵐ[
      (offspringSeqLaw μ).toMeasure.map p] d ∘ g := by
    apply (ae_map_iff hp.aemeasurable (measurableSet_eq_fun
      (measurable_of_countable _) (hd.comp hg))).mpr
    apply ae_of_all
    intro ω
    change ENNReal.ofReal (bridgePrefixDensity μ n m (prefixWalk (seqPrefix m ω))) =
      ENNReal.ofReal (bridgePathDensity μ B n a (g (p ω)))
    have hgp : g (p ω) = forestWalkPath B n a ω := congrFun hfactor ω
    rw [hgp, bridgePathDensity, endValue_forestWalkPath, div_mul_cancel₀ _ hB,
      round_intCast, prefixWalk_seqPrefix, bridgePrefixDensity]
  rw [restrictLaw_bridge_eq_seq hn a ha.2.le, ← hfactor,
    ← Measure.map_map hg hp, seqPrefix_bridge_withDensity μ hmn (bridge_endpoint_pos hn),
    withDensity_congr_ae heq, map_withDensity_comp _ hg hd,
    Measure.map_map hg hp, hfactor, map_forestWalkPath]


end BGW.StableTrees.DiscreteBridge
