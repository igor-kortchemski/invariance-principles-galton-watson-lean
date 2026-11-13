/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StablePassageSubordinator
public import BGW.StableTrees.Scalar.ForestWalkBridge
public import BGW.StableTrees.Scalar.ForestBounds
public import BGW.Tree.ForestCycle
public import BGW.Skorokhod.ExitPartition
import BGW.LocallyFinite.ForestWalkLaw
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Fin.Tuple.Take

/-!
# First passage of the canonical offspring walk

The weak downward hitting time of the canonical real walk is identified with the
Łukasiewicz code of a finite forest.  Criticality makes the hitting time almost
surely finite.  The step-path formulation is deterministic and is the input to
the functional stable limit theorem
(J. H. B. Kemperman, *The Passage Problem for a Stationary Markov Chain*, University of
Chicago Press, 1961; J. Pitman, *Combinatorial Stochastic Processes*, Springer, 2006,
Section 6.1).
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal BigOperators
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- The first (weak) hit of `(-∞, -ℓ]` by the walk `k ↦ partialSum w k`; `⊤` if never. -/
noncomputable def walkHitTime (ℓ : ℕ) (w : ℕ → ℝ) : ℕ∞ :=
  ⨅ k ∈ {k : ℕ | partialSum w k ≤ -(ℓ : ℝ)}, (k : ℕ∞)

/-- The law of `walkHitTime ℓ / n` for the canonical offspring walk (finite reading). -/
noncomputable def walkPassageLaw (μ : PMF ℕ) (ℓ n : ℕ) : Measure ℝ :=
  Measure.map (fun w : ℕ → ℝ => (((walkHitTime ℓ w).toNat : ℝ)) / n)
    (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ))

private def offspringSteps (K : ℕ → ℕ) (i : ℕ) : ℝ := (K i : ℝ) - 1

private noncomputable def offspringLaw (μ : PMF ℕ) : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun _ : ℕ => μ.toMeasure)

private instance (μ : PMF ℕ) : IsProbabilityMeasure (offspringLaw μ) := by
  unfold offspringLaw
  infer_instance

private def countPrefix (q : ℕ) (K : ℕ → ℕ) : Fin q → ℕ := fun i => K i

private theorem measurable_countPrefix (q : ℕ) : Measurable (countPrefix q) := by
  exact Measurable.of_eval fun i => (measurable_pi_apply (i : ℕ))

private theorem measurable_offspringSteps : Measurable offspringSteps := by
  unfold offspringSteps
  fun_prop

private theorem map_offspringLaw (μ : PMF ℕ) :
    (offspringLaw μ).map offspringSteps =
      (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) := by
  change (offspringLaw μ).map offspringSteps = Measure.infinitePi (fun _ : ℕ =>
    ((μ.toMeasure.map (fun k : ℕ => (k : ℤ) - 1)).map (fun z : ℤ => (z : ℝ))))
  rw [offspringLaw]
  unfold offspringSteps
  calc
    _ = Measure.infinitePi (fun _ : ℕ => μ.toMeasure.map (fun k : ℕ => (k : ℝ) - 1)) :=
      Measure.infinitePi_map_pi (μ := fun _ : ℕ => μ.toMeasure)
        (f := fun _ (k : ℕ) => (k : ℝ) - 1) (fun _ => by fun_prop)
    _ = _ := by
      congr 1
      funext i
      rw [Measure.map_map (by fun_prop) (measurable_of_countable _)]
      apply Measure.map_congr
      exact Eventually.of_forall fun k => by simp

private theorem partialSum_offspringSteps (K : ℕ → ℕ) (k : ℕ) :
    partialSum (offspringSteps K) k = ((stepWord (countPrefix k K)).sum : ℝ) := by
  simp only [partialSum, offspringSteps, stepWord, List.sum_ofFn, countPrefix,
    Finset.sum_sub_distrib, Int.cast_sum, Int.cast_sub, Int.cast_natCast, Int.cast_one,
    Fin.sum_univ_eq_sum_range (fun x => (K x : ℝ)) k,
    Fin.sum_univ_eq_sum_range (fun _ => (1 : ℝ)) k]

private theorem partialSum_offspringSteps_take (K : ℕ → ℕ) {q k : ℕ} (hkq : k ≤ q) :
    partialSum (offspringSteps K) k =
      (((stepWord (countPrefix q K)).take k).sum : ℝ) := by
  rw [partialSum_offspringSteps]
  congr 1
  simp only [stepWord, countPrefix]
  rw [← Fin.ofFn_take_eq_take_ofFn hkq]
  rfl

private theorem walkHitTime_le_nat_iff {ℓ q : ℕ} (w : ℕ → ℝ) :
    walkHitTime ℓ w ≤ (q : ℕ∞) ↔
      ∃ k ≤ q, partialSum w k ≤ -(ℓ : ℝ) := by
  constructor
  · intro h
    by_contra hn
    push Not at hn
    have hsucc : ((q + 1 : ℕ) : ℕ∞) ≤ walkHitTime ℓ w := by
      unfold walkHitTime
      apply le_iInf
      intro k
      apply le_iInf
      intro hk
      by_cases hkq : k ≤ q
      · exact ((not_lt_of_ge hk) (hn k hkq)).elim
      · exact_mod_cast Nat.succ_le_of_lt (Nat.lt_of_not_ge hkq)
    have hq : (q : ℕ∞) < ((q + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self q
    exact (not_lt_of_ge h) (hq.trans_le hsucc)
  · rintro ⟨k, hkq, hk⟩
    exact (iInf_le_of_le k (iInf_le _ hk)).trans (by exact_mod_cast hkq)

private theorem walkHitTime_eq_nat_iff {ℓ q : ℕ} (w : ℕ → ℝ) :
    walkHitTime ℓ w = (q : ℕ∞) ↔
      partialSum w q ≤ -(ℓ : ℝ) ∧ ∀ k < q, -(ℓ : ℝ) < partialSum w k := by
  rw [walkHitTime, ← iInf_subtype'']
  constructor
  · intro h
    obtain ⟨⟨⟨k, hk⟩, hkeq⟩, hlower⟩ := ENat.iInf_eq_natCast_iff.mp h
    have hkq : k = q := by exact_mod_cast hkeq
    subst k
    refine ⟨hk, fun j hj => ?_⟩
    by_contra hn
    have hjmem : j ∈ {j : ℕ | partialSum w j ≤ -(ℓ : ℝ)} := le_of_not_gt hn
    have hjq := hlower ⟨j, hjmem⟩
    exact (not_le_of_gt (by exact_mod_cast hj)) hjq
  · rintro ⟨hq, hbefore⟩
    apply ENat.iInf_eq_natCast_iff.mpr
    refine ⟨⟨⟨q, hq⟩, rfl⟩, ?_⟩
    rintro ⟨k, hk⟩
    by_contra hn
    have hkq : k < q := by exact_mod_cast (lt_of_not_ge hn)
    exact (not_lt_of_ge hk) (hbefore k hkq)

theorem measurable_walkHitTime (ℓ : ℕ) : Measurable (walkHitTime ℓ) := by
  apply ENat.measurable_iff.mpr
  intro q
  have hset : walkHitTime ℓ ⁻¹' {(q : ℕ∞)} =
      {w | partialSum w q ≤ -(ℓ : ℝ) ∧ ∀ k < q, -(ℓ : ℝ) < partialSum w k} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_ofPred_eq]
    exact walkHitTime_eq_nat_iff w
  rw [hset]
  apply MeasurableSet.inter
  · exact measurableSet_le (measurable_partialSum q) measurable_const
  · have heq : {w : ℕ → ℝ | ∀ k < q, -(ℓ : ℝ) < partialSum w k} =
        ⋂ k : Fin q, {w : ℕ → ℝ | -(ℓ : ℝ) < partialSum w k} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_iInter]
      exact ⟨fun h k => h k k.isLt, fun h k hk => h ⟨k, hk⟩⟩
    change MeasurableSet {w : ℕ → ℝ | ∀ k < q, -(ℓ : ℝ) < partialSum w k}
    rw [heq]
    exact MeasurableSet.iInter fun k => measurableSet_lt measurable_const (measurable_partialSum k)

private theorem partialSum_offspringSteps_eq_of_walkHitTime_eq_nat (K : ℕ → ℕ) {ℓ q : ℕ}
    (hhit : walkHitTime ℓ (offspringSteps K) = (q : ℕ∞)) :
    partialSum (offspringSteps K) q = -(ℓ : ℝ) := by
  have hchar := (walkHitTime_eq_nat_iff (offspringSteps K)).mp hhit
  apply le_antisymm hchar.1
  by_contra hlt
  have hlt' : partialSum (offspringSteps K) q < -(ℓ : ℝ) := lt_of_not_ge hlt
  cases q with
  | zero =>
    have hnonneg : (0 : ℝ) ≤ ℓ := Nat.cast_nonneg ℓ
    simp only [partialSum, Finset.sum_range_zero] at hlt'
    linarith
  | succ q =>
    have hprev : -(ℓ : ℝ) < partialSum (offspringSteps K) q :=
      hchar.2 q (Nat.lt_succ_self q)
    have hsucc : partialSum (offspringSteps K) (q + 1) =
        partialSum (offspringSteps K) q + offspringSteps K q := by
      simp [partialSum, Finset.sum_range_succ]
    let a : ℤ := (stepWord (countPrefix q K)).sum
    let b : ℤ := (stepWord (countPrefix (q + 1) K)).sum
    have ha : partialSum (offspringSteps K) q = (a : ℝ) := partialSum_offspringSteps K q
    have hb : partialSum (offspringSteps K) (q + 1) = (b : ℝ) :=
      partialSum_offspringSteps K (q + 1)
    rw [ha] at hprev
    rw [hb] at hlt'
    have hai : -(ℓ : ℤ) < a := by exact_mod_cast hprev
    have hbi : b < -(ℓ : ℤ) := by exact_mod_cast hlt'
    have hnextR : (b : ℝ) = (a : ℝ) + (K q : ℝ) - 1 := by
      rw [← hb, hsucc, ha]
      simp only [offspringSteps]
      ring
    have hnext : b = a + (K q : ℤ) - 1 := by exact_mod_cast hnextR
    omega

/-- Almost surely the canonical walk is downward skip-free: every step is an integer `≥ -1`. -/
theorem ae_step_ge_neg_one (μ : PMF ℕ) :
    ∀ᵐ w ∂(iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)),
      ∀ i : ℕ, ∃ k : ℕ, w i = (k : ℝ) - 1 := by
  have hp : MeasurableSet {w : ℕ → ℝ | ∀ i : ℕ, ∃ k : ℕ, w i = (k : ℝ) - 1} := by
    rw [show {w : ℕ → ℝ | ∀ i : ℕ, ∃ k : ℕ, w i = (k : ℝ) - 1} =
      ⋂ i : ℕ, {w : ℕ → ℝ | ∃ k : ℕ, w i = (k : ℝ) - 1} by ext w; simp]
    apply MeasurableSet.iInter
    intro i
    have heq : {w : ℕ → ℝ | ∃ k : ℕ, w i = (k : ℝ) - 1} =
        ⋃ k : ℕ, {w : ℕ → ℝ | w i = (k : ℝ) - 1} := by
      ext w
      simp
    rw [heq]
    exact MeasurableSet.iUnion fun k =>
      measurableSet_eq_fun (measurable_pi_apply i) measurable_const
  rw [← map_offspringLaw μ, ae_map_iff measurable_offspringSteps.aemeasurable hp]
  exact Eventually.of_forall fun K i => ⟨K i, rfl⟩

/-- Weak hit is exact hit: a.s., if the walk ever reaches `(-∞, -ℓ]` it equals `-ℓ` there. -/
theorem ae_partialSum_walkHitTime {μ : PMF ℕ} (ℓ : ℕ) :
    ∀ᵐ w ∂(iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)), ∀ k : ℕ,
      walkHitTime ℓ w = (k : ℕ∞) → partialSum w k = -(ℓ : ℝ) := by
  have hp : MeasurableSet {w : ℕ → ℝ | ∀ k : ℕ,
      walkHitTime ℓ w = (k : ℕ∞) → partialSum w k = -(ℓ : ℝ)} := by
    rw [show {w : ℕ → ℝ | ∀ k : ℕ,
      walkHitTime ℓ w = (k : ℕ∞) → partialSum w k = -(ℓ : ℝ)} =
      ⋂ k : ℕ, {w : ℕ → ℝ |
        walkHitTime ℓ w = (k : ℕ∞) → partialSum w k = -(ℓ : ℝ)} by ext w; simp]
    apply MeasurableSet.iInter
    intro k
    have heq : {w : ℕ → ℝ | walkHitTime ℓ w = (k : ℕ∞) → partialSum w k = -(ℓ : ℝ)} =
        {w | walkHitTime ℓ w ≠ (k : ℕ∞)} ∪ {w | partialSum w k = -(ℓ : ℝ)} := by
      ext w
      simp only [Set.mem_ofPred_eq, Set.mem_union, ne_eq, or_iff_not_imp_left, not_not]
    rw [heq]
    exact ((measurable_walkHitTime ℓ) (measurableSet_singleton _)).compl.union
      (measurableSet_eq_fun (measurable_partialSum k) measurable_const)
  rw [← map_offspringLaw μ, ae_map_iff measurable_offspringSteps.aemeasurable hp]
  exact Eventually.of_forall fun K k hk => partialSum_offspringSteps_eq_of_walkHitTime_eq_nat K hk

/-- `walkPassageLaw` is a probability measure when the hit is a.s. finite. -/
theorem walkPassageLaw_isProbabilityMeasure {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (ℓ n : ℕ) : IsProbabilityMeasure (walkPassageLaw μ ℓ n) := by
  -- `h` is part of the stated interface; this proof does not use it.
  have _h := h
  rw [walkPassageLaw]
  infer_instance

private theorem forestWeight_eq_pi_codes (μ : PMF ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (q : ℕ) :
    Measure.pi (fun _ : Fin q => μ.toMeasure) {w | BGW.IsForestCode ℓ (stepWord w)} =
      BGW.forestWeight μ ℓ q := by
  rw [BGW.forestWeight_eq_tsum_codes μ hℓ, BGW.pi_eq_tsum_indicator]
  let A : Set (List ℤ) := {x | BGW.IsForestCode ℓ x ∧ x.length = q}
  have hrange : Function.support (Set.indicator A (BGW.walkWeight μ)) ⊆
      Set.range (stepWord (n := q)) := by
    intro x hx
    by_contra hn
    apply hx
    apply Set.indicator_of_notMem
    intro hmem
    exact hn (BGW.exists_stepWord_eq_of_entries hmem.2 hmem.1.1)
  change (∑' w : Fin q → ℕ, Set.indicator {w | BGW.IsForestCode ℓ (stepWord w)}
    (fun w => ∏ i, μ.toMeasure {w i}) w) = ∑' x : List ℤ, Set.indicator A (BGW.walkWeight μ) x
  rw [← BGW.stepWord_injective.tsum_eq hrange]
  apply tsum_congr
  intro w
  by_cases hw : BGW.IsForestCode ℓ (stepWord w)
  · have hmem : stepWord w ∈ A := ⟨hw, by simp [stepWord]⟩
    have hw' : w ∈ {w | BGW.IsForestCode ℓ (stepWord w)} := hw
    simp only [Set.indicator, hw', hmem, ite_true, BGW.walkWeight_stepWord]
    simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
  · have hmem : stepWord w ∉ A := fun h => hw h.1
    simp [Set.indicator, hw, hmem]

/-- **First-hit mass is the forest weight.** For `ℓ ≥ 1`, the probability of a first hit of `-ℓ` at
time `q` equals `forestWeight μ ℓ q` (via `IsForestCode`, `firstPassageWords`; the support
condition `K ≥ 0`, i.e. steps `≥ -1`, is used, since `walkWeight` of an arbitrary integer word
does not encode `μ`). -/
theorem walkHitTime_mass_eq_forestWeight (μ : PMF ℕ) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (q : ℕ) :
    (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) {w | walkHitTime ℓ w = (q : ℕ∞)} =
      BGW.forestWeight μ ℓ q := by
  have hevent : offspringLaw μ (offspringSteps ⁻¹' {w | walkHitTime ℓ w = (q : ℕ∞)}) =
      (offspringLaw μ).map (countPrefix q) {v | BGW.IsForestCode ℓ (stepWord v)} := by
    rw [Measure.map_apply (measurable_countPrefix q) (MeasurableSet.of_discrete)]
    congr 1
    ext K
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    rw [walkHitTime_eq_nat_iff]
    constructor
    · rintro ⟨hq, hbefore⟩
      have hval := partialSum_offspringSteps_eq_of_walkHitTime_eq_nat K
        ((walkHitTime_eq_nat_iff _).mpr ⟨hq, hbefore⟩)
      refine ⟨?_, ?_, ?_⟩
      · intro a ha
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
        omega
      · rw [partialSum_offspringSteps K q] at hval
        exact_mod_cast hval
      · intro i hi
        have hiq : i < q := by simpa [stepWord] using hi
        have hs := hbefore i hiq
        rw [partialSum_offspringSteps_take K hiq.le] at hs
        exact_mod_cast hs
    · intro hcode
      have hsum := hcode.2.1
      have hnear : ∀ k < q, -(ℓ : ℝ) < partialSum (offspringSteps K) k := by
        intro k hk
        rw [partialSum_offspringSteps_take K hk.le]
        have hs := hcode.2.2 k (by simpa [stepWord] using hk)
        exact_mod_cast hs
      refine ⟨?_, hnear⟩
      have hsumR : ((stepWord (countPrefix q K)).sum : ℝ) = -(ℓ : ℝ) := by
        exact_mod_cast hsum
      have hpartial := partialSum_offspringSteps K q
      linarith
  have hprefix : (offspringLaw μ).map (countPrefix q) =
      Measure.pi (fun _ : Fin q => μ.toMeasure) := by
    unfold offspringLaw
    change Measure.map (fun K (i : Fin q) => K (i : ℕ))
      (Measure.infinitePi (fun _ : ℕ => μ.toMeasure)) = _
    rw [Measure.map_infinitePi_infinitePi_of_inj (f := fun i : Fin q => (i : ℕ))
      Fin.val_injective, Measure.infinitePi_eq_pi]
  rw [← map_offspringLaw μ]
  calc
    (Measure.map offspringSteps (offspringLaw μ)) {w | walkHitTime ℓ w = (q : ℕ∞)} =
        offspringLaw μ (offspringSteps ⁻¹' {w | walkHitTime ℓ w = (q : ℕ∞)}) := by
      exact Measure.map_apply measurable_offspringSteps
        ((measurable_walkHitTime ℓ) (measurableSet_singleton _))
    _ = _ := by rw [hevent, hprefix, forestWeight_eq_pi_codes μ hℓ q]

/-- **Kemperman for the first-hit mass.** For `ℓ ≥ 1`, `q ≥ 1`: `P(hit = q) = (ℓ / q) P(S_q = -ℓ)`,
with the integer walk point probability `walkProb`. -/
theorem walkHitTime_mass_toReal {μ : PMF ℕ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) {q : ℕ} (hq : 1 ≤ q) :
    ((iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)).real {w | walkHitTime ℓ w = (q : ℕ∞)}) =
      ℓ / q * walkProb μ q (-(ℓ : ℤ)) := by
  rw [measureReal_def, walkHitTime_mass_eq_forestWeight μ hℓ q]
  exact Scalar.forestWeight_toReal_eq μ hℓ hq

/-- The masses of the hitting times add up to `1` (a.s. finite hit), as `tsum` over `q`. -/
theorem tsum_walkHitTime_mass {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B) {ℓ : ℕ}
    (hℓ : 1 ≤ ℓ) : ∑' q : ℕ, BGW.forestWeight μ ℓ q = 1 := by
  -- `hℓ` is part of the stated interface; this proof does not use it.
  have _hℓ := hℓ
  exact Scalar.tsum_forestWeight_eq_one h.critical h.nondegenerate ℓ

/-- The critical, nondegenerate offspring walk hits every level `-ℓ` a.s. -/
theorem ae_walkHitTime_ne_top {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B) (ℓ : ℕ) :
    ∀ᵐ w ∂(iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)), walkHitTime ℓ w ≠ ⊤ := by
  by_cases hℓzero : ℓ = 0
  · subst ℓ
    filter_upwards [] with w
    have hzero : walkHitTime 0 w = 0 := by
      apply le_antisymm _ bot_le
      exact (walkHitTime_le_nat_iff w).mpr ⟨0, le_rfl, by simp [partialSum]⟩
    simp [hzero]
  · have hℓpos : 1 ≤ ℓ := Nat.one_le_iff_ne_zero.mpr hℓzero
    let E : ℕ → Set (ℕ → ℝ) := fun q => {w | walkHitTime ℓ w = (q : ℕ∞)}
    have hEdisj : Pairwise (Function.onFun Disjoint E) := by
      intro i j hij
      simp only [Function.onFun, Set.disjoint_left, E]
      rintro w hi hj
      change walkHitTime ℓ w = (i : ℕ∞) at hi
      change walkHitTime ℓ w = (j : ℕ∞) at hj
      rw [hi] at hj
      exact hij (by exact_mod_cast hj)
    have hEmeas : ∀ q, MeasurableSet (E q) := fun q =>
      measurableSet_eq_fun (measurable_walkHitTime ℓ) measurable_const
    have hmeasure : (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) (⋃ q, E q) = 1 := by
      rw [measure_iUnion hEdisj hEmeas]
      simp_rw [E, walkHitTime_mass_eq_forestWeight μ hℓpos]
      exact tsum_walkHitTime_mass h hℓpos
    have hmem : ∀ᵐ w ∂(iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)), w ∈ ⋃ q, E q := by
      apply (ae_iff_measure_eq (MeasurableSet.iUnion hEmeas).nullMeasurableSet).mpr
      change (iidLaw (realOffspringStepLaw μ) : Measure (ℕ → ℝ)) (⋃ q, E q) = _
      rw [hmeasure, measure_univ]
    filter_upwards [hmem] with w hw
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hw
    change walkHitTime ℓ w = (q : ℕ∞) at hq
    rw [hq]
    exact ENat.natCast_ne_top q

/-- **Weak hit versus running minimum of the step path** (deterministic, no limit): for `b > 0`,
`walkHitTime ℓ ≤ ⌊n t⌋ ↔ inf_{s ≤ t} realStepPath ≤ -ℓ/b`. The infimum over `[0, t]` of the
step path is a minimum over `j ≤ ⌊n t⌋`, so the WEAK inequality `≤ -ℓ/b` is exact. -/
theorem walkHitTime_le_iff_iInf_stepPath_le {ℓ n : ℕ} {t b : ℝ} (ht : 0 ≤ t) (hb : 0 < b)
    (w : ℕ → ℝ) :
    walkHitTime ℓ w ≤ ((⌊(n : ℝ) * t⌋₊ : ℕ) : ℕ∞) ↔
      (⨅ s : Set.Icc (0 : ℝ) t, realStepPath t n b w s) ≤ -(ℓ : ℝ) / b := by
  let _ : Nonempty (Set.Icc (0 : ℝ) t) := ⟨⟨0, le_rfl, ht⟩⟩
  by_cases hn : n = 0
  · subst n
    have hzero : walkHitTime ℓ w = 0 ↔ 0 ≤ -(ℓ : ℝ) := by
      change walkHitTime ℓ w = ((0 : ℕ) : ℕ∞) ↔ _
      rw [walkHitTime_eq_nat_iff]
      simp [partialSum]
    simp only [Nat.cast_zero, zero_mul, Nat.floor_zero]
    change walkHitTime ℓ w ≤ (0 : ℕ∞) ↔ _
    rw [nonpos_iff_eq_zero, hzero]
    simp only [realStepPath_apply, Nat.cast_zero, zero_mul, Nat.floor_zero,
      partialSum, Finset.sum_range_zero, zero_div, ciInf_const]
    by_cases hℓ : ℓ = 0
    · simp [hℓ]
    · have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast Nat.pos_of_ne_zero hℓ
      have hneg : -(ℓ : ℝ) / b < 0 := div_neg_of_neg_of_pos (neg_neg_of_pos hℓpos) hb
      constructor
      · intro heq
        exact div_nonneg heq hb.le
      · intro hnonneg
        exact ((not_le_of_gt hneg) hnonneg).elim
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
    let N : ℕ := ⌊(n : ℝ) * t⌋₊
    let grid : Fin (N + 1) → ℝ := fun k => partialSum w k / b
    obtain ⟨kmin, hkmin⟩ := Finite.exists_min grid
    have hNt : 0 ≤ (n : ℝ) * t := mul_nonneg (Nat.cast_nonneg n) ht
    have hpath (s : Set.Icc (0 : ℝ) t) :
        ∃ k : Fin (N + 1), realStepPath t n b w s = grid k := by
      have hfloor : ⌊(n : ℝ) * (s : ℝ)⌋₊ ≤ N := by
        apply Nat.floor_le_floor
        exact mul_le_mul_of_nonneg_left s.2.2 (Nat.cast_nonneg n)
      exact ⟨⟨⌊(n : ℝ) * (s : ℝ)⌋₊, Nat.lt_succ_of_le hfloor⟩, rfl⟩
    have htime (k : Fin (N + 1)) : (k : ℝ) / n ∈ Set.Icc (0 : ℝ) t := by
      have hkN : (k : ℕ) ≤ N := Nat.le_of_lt_succ k.isLt
      have hkNt : (k : ℝ) ≤ (n : ℝ) * t := by
        have hcast : (k : ℝ) ≤ (N : ℝ) := by exact_mod_cast hkN
        exact hcast.trans (Nat.floor_le hNt)
      refine⟨div_nonneg (Nat.cast_nonneg k) hnreal.le, ?_⟩
      exact (div_le_iff₀ hnreal).mpr (by simpa [mul_comm] using hkNt)
    let time (k : Fin (N + 1)) : Set.Icc (0 : ℝ) t := ⟨(k : ℝ) / n, htime k⟩
    have htime_value (k : Fin (N + 1)) : realStepPath t n b w (time k) = grid k := by
      have hmul : (n : ℝ) * ((k : ℝ) / n) = k := by field_simp
      simp [realStepPath_apply, time, hmul, grid]
    have hI : (⨅ s : Set.Icc (0 : ℝ) t, realStepPath t n b w s) = grid kmin := by
      apply le_antisymm
      · let s := time kmin
        have hbdd : BddBelow (Set.range fun s : Set.Icc (0 : ℝ) t => realStepPath t n b w s) := by
          refine ⟨grid kmin, ?_⟩
          rintro _ ⟨u, rfl⟩
          obtain ⟨j, hj⟩ := hpath u
          change grid kmin ≤ realStepPath t n b w u
          rw [hj]
          exact hkmin j
        exact (ciInf_le hbdd s).trans_eq (htime_value kmin)
      · apply le_ciInf
        intro s
        obtain ⟨j, hj⟩ := hpath s
        rw [hj]
        exact hkmin j
    constructor
    · intro hhit
      obtain ⟨k, hkN, hk⟩ := (walkHitTime_le_nat_iff w).mp hhit
      let k' : Fin (N + 1) := ⟨k, Nat.lt_succ_of_le hkN⟩
      have hkval : grid k' ≤ -(ℓ : ℝ) / b := by
        dsimp [grid, k']
        gcongr
      rw [hI]
      exact (hkmin k').trans hkval
    · intro hIle
      apply (walkHitTime_le_nat_iff w).mpr
      refine ⟨kmin, Nat.le_of_lt_succ kmin.isLt, ?_⟩
      have hg : grid kmin ≤ -(ℓ : ℝ) / b := by
        rw [← hI]
        exact hIle
      dsimp [grid] at hg
      exact (div_le_div_iff_of_pos_right hb).mp hg

end BGW.StableTrees
