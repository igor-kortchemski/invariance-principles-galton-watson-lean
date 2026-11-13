/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteHeightApproxRenewalGreen

/-!
# The weak ascending ladder-height law

A last-step decomposition combines exact pre-return occupations with an independent
offspring coordinate. The resulting height law is the offspring tail, including
its atom at zero.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest

namespace BGW.StableTrees.DiscreteHeightApprox

private def ladderExit (j y n : ℕ) : Set (ℕ → ℕ) :=
  negativeLevelEvent y n ∩ {ω | ω n = y + j + 1}

private theorem measurableSet_ladderExit (j y n : ℕ) : MeasurableSet (ladderExit j y n) :=
  (measurableSet_negativeLevelEvent y n).inter
    (measurableSet_eq_fun (measurable_pi_apply n) measurable_const)

private theorem ladderExit_walk {ω : ℕ → ℕ} {j y n : ℕ} (he : ω ∈ ladderExit j y n) :
    walk ω (n + 1) = (j : ℤ) := by
  have hs := walk_succ_eq ω n
  have hn := he.1.1
  have hd := he.2
  rw [hd] at hs
  push_cast at hs
  omega

private theorem ladderExit_epoch {ω : ℕ → ℕ} (hω : EpochsFinite ω) {j y n : ℕ}
    (he : ω ∈ ladderExit j y n) : weakEpoch ω 1 = n + 1 := by
  have hret := ladderExit_walk he
  have hle : weakEpoch ω 1 ≤ n + 1 := by
    rw [weakEpoch_succ, weakEpoch_zero]
    have hz : walk ω 0 = 0 := by simp [walk]
    exact Nat.sInf_le ⟨by omega, by rw [hz, hret]; exact Int.natCast_nonneg j⟩
  have hp : 0 < weakEpoch ω 1 := by
    simpa only [weakEpoch_zero] using weakEpoch_lt_succ hω 0
  have hw := walk_weakEpoch_nonneg hω 1
  have hgt : n < weakEpoch ω 1 := by
    by_contra hn
    have hneg := he.1.2 (weakEpoch ω 1) hp (by omega)
    omega
  omega

private theorem ladderExit_disjoint (j : ℕ) :
    Pairwise (fun p q : ℕ × ℕ => Disjoint (ladderExit j p.2 p.1) (ladderExit j q.2 q.1)) := by
  intro ⟨n, y⟩ ⟨m, z⟩ hne
  apply Set.disjoint_left.mpr
  intro ω hn hm
  change (walk ω n = -(y : ℤ) ∧ NegativePrefix ω n) ∧ ω n = y + j + 1 at hn
  change (walk ω m = -(z : ℤ) ∧ NegativePrefix ω m) ∧ ω m = z + j + 1 at hm
  rcases lt_trichotomy n m with hlt | heq | hgt
  · have hneg := hm.1.2 (n + 1) (by omega) (by omega)
    have hpos : walk ω (n + 1) = (j : ℤ) := ladderExit_walk hn
    omega
  · have hy := hn.1.1
    have hz := hm.1.1
    have hyz : y = z := by rw [heq] at hy; omega
    exact hne (Prod.ext heq hyz)
  · have hneg := hn.1.2 (m + 1) (by omega) (by omega)
    have hpos : walk ω (m + 1) = (j : ℤ) := ladderExit_walk hm
    omega

private theorem ladderExit_union_ae (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (j : ℕ) :
    (⋃ p : ℕ × ℕ, ladderExit j p.2 p.1) =ᵐ[(offspringSeqLaw μ).toMeasure]
      {ω | weakEpochHeight ω 1 = j} := by
  filter_upwards [ae_epochsFinite μ hc hne] with ω hω
  apply propext
  constructor
  · intro he
    obtain ⟨⟨n, y⟩, hn⟩ := Set.mem_iUnion.mp he
    have hτ := ladderExit_epoch hω hn
    have hs := ladderExit_walk hn
    have hh := weakEpochHeight_cast hω 1
    rw [hτ, hs] at hh
    exact_mod_cast hh
  · intro hj
    have hτp : 0 < weakEpoch ω 1 := by
      simpa only [weakEpoch_zero] using weakEpoch_lt_succ hω 0
    let n := weakEpoch ω 1 - 1
    have hnτ : n + 1 = weakEpoch ω 1 := by omega
    have hprefix : NegativePrefix ω n := by
      intro u hu hun
      by_contra hneg
      have hle : weakEpoch ω 1 ≤ u := by
        rw [weakEpoch_succ, weakEpoch_zero]
        apply Nat.sInf_le
        exact ⟨hu, by simpa [walk] using (not_lt.mp hneg)⟩
      omega
    have hwn : walk ω n ≤ 0 := by
      by_cases hn : n = 0
      · simp [hn, walk]
      · exact (hprefix n (by omega) le_rfl).le
    let y := (-walk ω n).toNat
    have hy : (y : ℤ) = -walk ω n := Int.toNat_of_nonneg (by omega)
    have hτw : walk ω (weakEpoch ω 1) = (j : ℤ) := by
      rw [← weakEpochHeight_cast hω 1, hj]
    have hstep := walk_succ_eq ω n
    rw [hnτ, hτw] at hstep
    apply Set.mem_iUnion.mpr
    refine ⟨(n, y), ?_⟩
    change (walk ω n = -(y : ℤ) ∧ NegativePrefix ω n) ∧ ω n = y + j + 1
    exact ⟨⟨by omega, hprefix⟩, by omega⟩

private theorem ladderExit_mass (μ : PMF ℕ) (j y n : ℕ) :
    (offspringSeqLaw μ).toMeasure (ladderExit j y n) =
      (offspringSeqLaw μ).toMeasure (negativeLevelEvent y n) * μ (y + j + 1) := by
  let A : Set (ℕ → ℕ) := {ω | ω 0 = y + j + 1}
  have hN : IsSeqStoppingTime (fun _ : ℕ → ℕ => (n : ℕ∞)) :=
    fun _ _ _ hm _ => ⟨hm, Iff.rfl⟩
  have hfin : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, (n : ℕ∞) ≠ ⊤ := by simp
  have hA : MeasurableSet A := measurableSet_eq_fun (measurable_pi_apply 0) measurable_const
  have hr := stoppedRestart μ (fun _ => (n : ℕ∞)) hN hfin
    (preStopped_negativeLevelEvent y n) hA
  have he : {ω : ℕ → ℕ | ∃ m : ℕ, (n : ℕ∞) = m ∧ shiftSeq m ω ∈ A} =
      {ω | ω n = y + j + 1} := by
    ext ω
    constructor
    · rintro ⟨m, hm, hmem⟩
      have hnm : n = m := ENat.natCast_inj.mp hm
      subst m
      exact hmem
    · intro hmem
      exact ⟨n, rfl, hmem⟩
  have hm : (offspringSeqLaw μ).toMeasure A = μ (y + j + 1) := by
    change (Measure.infinitePi (fun _ : ℕ => μ.toMeasure))
      ((fun ω : ℕ → ℕ => ω 0) ⁻¹' {y + j + 1}) = _
    rw [← Measure.map_apply (measurable_pi_apply 0) (measurableSet_singleton _),
      Measure.infinitePi_map_eval,
      PMF.toMeasure_apply_singleton μ (y + j + 1) (measurableSet_singleton _)]
  rw [he, hm] at hr
  exact hr

private theorem tsum_shift_pmf (μ : PMF ℕ) (j : ℕ) :
    ∑' y : ℕ, μ (y + j + 1) = μ.toMeasure (Set.Ici (j + 1)) := by
  let e : ℕ ≃ Set.Ici (j + 1) :=
    { toFun := fun n => ⟨n + j + 1, by change j + 1 ≤ n + j + 1; omega⟩
      invFun := fun u => u.val - (j + 1)
      left_inv := fun n => by change n + j + 1 - (j + 1) = n; omega
      right_inv := fun u => by
        apply Subtype.ext
        change u.val - (j + 1) + j + 1 = u.val
        have hu : j + 1 ≤ u.val := u.property
        omega }
  rw [PMF.toMeasure_apply_eq_tsum, ← tsum_subtype]
  exact e.tsum_eq (fun u : Set.Ici (j + 1) => μ u)

/-- The first weak ascending ladder height has the offspring-tail law, with its zero atom. -/
theorem weakEpochHeight_one_law (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (j : ℕ) :
    (offspringSeqLaw μ).toMeasure {ω | weakEpochHeight ω 1 = j} =
      μ.toMeasure (Set.Ici (j + 1)) := by
  rw [← measure_congr (ladderExit_union_ae μ hc hne j),
    measure_iUnion (ladderExit_disjoint j) (fun p => measurableSet_ladderExit j p.2 p.1),
    ENNReal.tsum_prod']
  simp_rw [ladderExit_mass]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_right, tsum_negativeLevelEvent_mass μ hc hne, one_mul]
  exact tsum_shift_pmf μ j

end BGW.StableTrees.DiscreteHeightApprox
