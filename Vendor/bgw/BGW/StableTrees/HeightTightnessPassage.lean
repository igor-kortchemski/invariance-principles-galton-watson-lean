/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessRegeneration
public import BGW.StableTrees.WalkPassageBasic
import BGW.StableTrees.StableKendall
import BGW.StableTrees.Survival

/-!
# Small-time estimates for the first height upcrossing

Forest ladder times have the canonical walk passage law. Passage convergence
keeps positive tree levels away from time zero. Combining this with the survival
union bound and then choosing a small tree level gives the eventual small-time
bound for the first height upcrossing.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest BGW.Probability.RealWalk
namespace BGW.StableTrees.HeightTightness

private theorem walkHitTime_eq_ladderTime {ω : ℕ → ℕ} (hω : LadderFinite ω) (l : ℕ) :
    walkHitTime l (fun i => ((ω i : ℤ) - 1 : ℝ)) = (ladderTime ω l : ℕ∞) := by
  have hw (k : ℕ) : partialSum (fun i => ((ω i : ℤ) - 1 : ℝ)) k = (walk ω k : ℝ) := by
    simp only [walk, partialSum, Int.cast_sum, Int.cast_sub, Int.cast_one]
  apply le_antisymm
  · unfold walkHitTime
    apply iInf_le_of_le (ladderTime ω l)
    apply iInf_le_of_le
      (by simp only [mem_ofPred_eq]; rw [hw, walk_ladderTime hω, Int.cast_neg,
        Int.cast_natCast])
    exact le_rfl
  · unfold walkHitTime
    apply le_iInf
    intro k
    apply le_iInf
    intro hk
    apply ENat.natCast_le_natCast.mpr
    by_contra hn
    have hgt := walk_gt_of_lt_ladderTime hω (r := l) (k := k) (by omega)
    simp only [mem_ofPred_eq] at hk
    rw [hw] at hk
    exact not_le_of_gt (by exact_mod_cast hgt) hk

/-- The rescaled ladder time of the offspring forest has the canonical walk passage law. -/
theorem map_scaled_ladderTime (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (l n : ℕ) :
    (offspringSeqLaw μ).toMeasure.map (fun ω => (ladderTime ω l : ℝ) / n) =
      walkPassageLaw μ l n := by
  have hi : Measurable (fun (ω : ℕ → ℕ) i => ((ω i : ℤ) - 1 : ℝ)) := by
    fun_prop
  have ht : Measurable (fun w : ℕ → ℝ => ((walkHitTime l w).toNat : ℝ) / n) :=
    (((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      ((measurable_of_countable ENat.toNat).comp (measurable_walkHitTime l))).div_const n)
  rw [walkPassageLaw, ← map_offspringSeqLaw_realIncrements,
    Measure.map_map ht hi]
  apply Measure.map_congr
  filter_upwards [ae_ladderFinite μ hc hne] with ω hω
  simp only [Function.comp_def, walkHitTime_eq_ladderTime hω, ENat.toNat_natCast]

/-- At a positive limiting tree level, the scaled ladder times stay away from zero
in probability, eventually in the scaling index. -/
theorem exists_pos_eventually_ladderTime_probability_small {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B) {a ε : ℝ} (ha : 0 < a) (hε : 0 < ε) :
    ∃ x : ℝ, 0 < x ∧ ∀ᶠ n : ℕ in atTop,
      (offspringSeqLaw μ).toMeasure.real
        {ω | ladderTime ω ⌊a * B n⌋₊ ≤ ⌊(n : ℝ) * x⌋₊} ≤ ε := by
  have hfloor : Tendsto (fun n : ℕ => (⌊a * B n⌋₊ : ℝ) / B n) atTop (𝓝 a) := by
    simpa only [Function.comp_def] using
      (tendsto_nat_floor_mul_div_atTop (R := ℝ) ha.le).comp (Scalar.tendsto_atTop h)
  have hl : ∀ᶠ n : ℕ in atTop, 1 ≤ ⌊a * B n⌋₊ := by
    filter_upwards [((Scalar.tendsto_atTop h).const_mul_atTop ha).eventually_ge_atTop 1] with n hn
    exact Nat.le_floor (by simpa only [Nat.cast_one] using hn)
  obtain ⟨δ, hδ, R, _, htail⟩ := walkPassageLaw_tight h
    (x := ⟨a, ha.le⟩) ha hl hfloor hε
  refine ⟨δ / 2, by positivity, ?_⟩
  filter_upwards [htail, eventually_ge_atTop 1] with n hn hn1
  have hmap := map_scaled_ladderTime μ h.critical h.nondegenerate ⌊a * B n⌋₊ n
  have hm : Measurable (fun ω => (ladderTime ω ⌊a * B n⌋₊ : ℝ) / n) :=
    ((measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      (measurable_ladderTime _)).div_const n
  have hs : {ω | ladderTime ω ⌊a * B n⌋₊ ≤ ⌊(n : ℝ) * (δ / 2)⌋₊} ⊆
      (fun ω => (ladderTime ω ⌊a * B n⌋₊ : ℝ) / n) ⁻¹' Iio δ := by
    intro ω hω
    change (ladderTime ω ⌊a * B n⌋₊ : ℝ) / n < δ
    apply (div_lt_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn1)).mpr
    have hb : (ladderTime ω ⌊a * B n⌋₊ : ℝ) ≤ (n : ℝ) * (δ / 2) :=
      (Nat.cast_le.mpr hω).trans (Nat.floor_le (by positivity))
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    nlinarith
  have hle := measure_mono hs (μ := (offspringSeqLaw μ).toMeasure)
  rw [← Measure.map_apply hm measurableSet_Iio, hmap] at hle
  have hr := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (hle.trans ((le_add_right le_rfl).trans hn))
  change ((offspringSeqLaw μ).toMeasure _).toReal ≤ ε
  simpa only [ENNReal.toReal_ofReal hε.le] using hr

/-- The scaled first height upcrossing has uniformly vanishing mass near time zero,
in the eventual form needed for the renewal argument. -/
theorem exists_pos_eventually_height_hit_probability_small {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) :
    ∃ x : ℝ, 0 < x ∧ ∀ᶠ n : ℕ in atTop,
      (offspringSeqLaw μ).toMeasure.real
        {ω | ∃ k ≤ ⌊(n : ℝ) * x⌋₊, ⌊η * (n : ℝ) / B n⌋₊ ≤ forestHeight ω k} ≤ ε := by
  let v := Survival.csbpSurvival θ η
  have hv : 0 < v := Survival.csbpSurvival_pos h.alpha_mem.1 hη
  let a := ε / (4 * v)
  have ha : 0 < a := by dsimp [a]; positivity
  have hav : a * v < ε / 2 := by
    dsimp [a]
    field_simp
    nlinarith
  obtain ⟨x, hx, hpass⟩ := exists_pos_eventually_ladderTime_probability_small h ha
    (show 0 < ε / 2 by positivity)
  have hsurv := (Survival.tendsto_floor_mul_survivalProb_floor h hη ha.le).eventually
    (gt_mem_nhds hav)
  refine ⟨x, hx, ?_⟩
  filter_upwards [hpass, hsurv] with n hnP hnS
  exact (height_hit_probability_le μ h.critical h.nondegenerate
    ⌊η * (n : ℝ) / B n⌋₊ ⌊(n : ℝ) * x⌋₊ ⌊a * B n⌋₊).trans (by linarith)

end BGW.StableTrees.HeightTightness
