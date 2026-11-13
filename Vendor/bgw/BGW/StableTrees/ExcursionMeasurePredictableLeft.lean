/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasurePredictable

/-! Predictability of left-continuous adapted nonnegative processes.

See Bertoin, *Lévy Processes*, Chapter IV, and Kallenberg,
*Foundations of Modern Probability*, Chapters 12 and 22.
-/

@[expose] public section

open MeasureTheory MeasurableSpace Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

private noncomputable def windowStep (a b : ℝ≥0) (Y : DLoc → ℝ≥0∞) (p : ℝ≥0 × DLoc) : ℝ≥0∞ :=
  if p.1 ∈ Ioc a b then Y p.2 else 0

private theorem measurable_windowStep {a b : ℝ≥0} (hab : a ≤ b) {Y : DLoc → ℝ≥0∞}
    (hY : Measurable[(isStoppingTime_firstPassageBelow a).measurableSpace] Y) :
    Measurable[predictableSigma] (windowStep a b Y) := by
  apply measurable_of_Ioi
  intro c
  have hs : MeasurableSet[predictableSigma] (Ioc a b ×ˢ (Y ⁻¹' Ioi c)) := by
    rw [predictableSigma_eq_generate]
    exact measurableSet_generateFrom (mem_insert_of_mem _ (Or.inl ⟨a, b, _, hab,
      hY measurableSet_Ioi, rfl⟩))
  convert hs using 1
  ext p
  by_cases hp : p.1 ∈ Ioc a b <;> simp [windowStep, hp]

private theorem measurable_zeroStep {Y : DLoc → ℝ≥0∞}
    (hY : Measurable[(isStoppingTime_firstPassageBelow 0).measurableSpace] Y) :
    Measurable[predictableSigma] (fun p : ℝ≥0 × DLoc => if p.1 = 0 then Y p.2 else 0) := by
  apply measurable_of_Ioi
  intro c
  have hs : MeasurableSet[predictableSigma] (({0} : Set ℝ≥0) ×ˢ (Y ⁻¹' Ioi c)) := by
    rw [predictableSigma_eq_generate]
    exact measurableSet_generateFrom (mem_insert_of_mem _ (Or.inr ⟨_, hY measurableSet_Ioi, rfl⟩))
  convert hs using 1
  ext p
  by_cases hp : p.1 = 0 <;> simp [hp]

private noncomputable def leftIndex (n : ℕ) (x : ℝ≥0) : ℕ := ⌈x * (n + 1 : ℝ≥0)⌉₊ - 1

private noncomputable def leftGrid (n : ℕ) (x : ℝ≥0) : ℝ≥0 :=
  (leftIndex n x : ℝ≥0) / (n + 1 : ℝ≥0)

private theorem leftIndex_bounds (n : ℕ) {x : ℝ≥0} (hx : 0 < x) :
    (leftIndex n x : ℝ≥0) < x * (n + 1 : ℝ≥0) ∧
      x * (n + 1 : ℝ≥0) ≤ (leftIndex n x + 1 : ℝ≥0) := by
  have hpos : 0 < ⌈x * (n + 1 : ℝ≥0)⌉₊ := by
    apply Nat.lt_ceil.mpr
    simpa only [Nat.cast_zero] using mul_pos hx (show 0 < (n + 1 : ℝ≥0) by positivity)
  have hk : leftIndex n x + 1 = ⌈x * (n + 1 : ℝ≥0)⌉₊ := Nat.sub_add_cancel hpos
  have hk' : (⌈x * (n + 1 : ℝ≥0)⌉₊ : ℝ≥0) = (leftIndex n x : ℝ≥0) + 1 := by
    exact_mod_cast hk.symm
  constructor
  · have hc := Nat.ceil_lt_add_one (show 0 ≤ x * (n + 1 : ℝ≥0) from bot_le)
    rw [hk'] at hc
    exact (add_lt_add_iff_right 1).mp hc
  · simpa only [hk'] using Nat.le_ceil (x * (n + 1 : ℝ≥0))

private theorem mem_leftGrid (n : ℕ) {x : ℝ≥0} (hx : 0 < x) :
    x ∈ Ioc (leftGrid n x) ((leftIndex n x + 1 : ℝ≥0) / (n + 1 : ℝ≥0)) := by
  exact ⟨(div_lt_iff₀ (by positivity)).mpr (leftIndex_bounds n hx).1,
    (le_div_iff₀ (by positivity)).mpr (leftIndex_bounds n hx).2⟩

private theorem grid_index_unique {n j k : ℕ} {x : ℝ≥0}
    (hj : x ∈ Ioc ((j : ℝ≥0) / (n + 1)) ((j + 1 : ℝ≥0) / (n + 1)))
    (hk : x ∈ Ioc ((k : ℝ≥0) / (n + 1)) ((k + 1 : ℝ≥0) / (n + 1))) : j = k := by
  have hjk : (j : ℝ≥0) < k + 1 := by
    exact ((div_lt_div_iff_of_pos_right (by positivity)).mp (hj.1.trans_le hk.2))
  have hkj : (k : ℝ≥0) < j + 1 := by
    exact ((div_lt_div_iff_of_pos_right (by positivity)).mp (hk.1.trans_le hj.2))
  have hjk' : j < k + 1 := by exact_mod_cast hjk
  have hkj' : k < j + 1 := by exact_mod_cast hkj
  omega

private theorem tendsto_leftGrid {x : ℝ≥0} (hx : 0 < x) :
    Tendsto (fun n => leftGrid n x) atTop (𝓝[<] x) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨NNReal.tendsto_coe.mp ?_,
    Eventually.of_forall fun n => (mem_leftGrid n hx).1⟩
  have hlow : Tendsto (fun n : ℕ => (x : ℝ) - 1 / (n + 1 : ℝ)) atTop (𝓝 (x : ℝ)) := by
    simpa only [sub_zero] using
      (tendsto_const_nhds (x := (x : ℝ))).sub tendsto_one_div_add_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
  · intro n
    have hu := (mem_leftGrid n hx).2
    have hur : (x : ℝ) ≤ ((leftIndex n x : ℝ) + 1) / (n + 1 : ℝ) := by
      exact_mod_cast hu
    change (x : ℝ) - 1 / (n + 1 : ℝ) ≤ (leftIndex n x : ℝ) / (n + 1 : ℝ)
    rw [add_div] at hur
    linarith
  · intro n
    exact_mod_cast (mem_leftGrid n hx).1.le

/-- A left-continuous process adapted to the stopped filtration is predictable. -/
theorem measurable_predictable_of_leftContinuous
    {H : ℝ≥0 → DLoc → ℝ≥0∞}
    (hadapted : ∀ x, Measurable[(isStoppingTime_firstPassageBelow x).measurableSpace] (H x))
    (hleft : ∀ f x, 0 < x → ContinuousWithinAt (fun y => H y f) (Iio x) x) :
    Measurable[predictableSigma] (fun p : ℝ≥0 × DLoc => H p.1 p.2) := by
  let : MeasurableSpace (ℝ≥0 × DLoc) := predictableSigma
  let F : ℕ → (ℝ≥0 × DLoc) → ℝ≥0∞ := fun n p =>
    (if p.1 = 0 then H 0 p.2 else 0) ⊔
      ⨆ k : ℕ, windowStep ((k : ℝ≥0) / (n + 1))
        ((k + 1 : ℝ≥0) / (n + 1)) (H ((k : ℝ≥0) / (n + 1))) p
  have hFm (n : ℕ) : Measurable (F n) := by
    apply (measurable_zeroStep (hadapted 0)).sup
    apply Measurable.iSup
    intro k
    apply measurable_windowStep _ (hadapted _)
    exact div_le_div_of_nonneg_right (by exact_mod_cast Nat.le_succ k) (by positivity)
  have hFeq {p : ℝ≥0 × DLoc} (hp : 0 < p.1) (n : ℕ) : F n p = H (leftGrid n p.1) p.2 := by
    have hmem := mem_leftGrid n hp
    dsimp only [leftGrid] at hmem
    have hs : (⨆ k : ℕ, windowStep ((k : ℝ≥0) / (n + 1))
        ((k + 1 : ℝ≥0) / (n + 1)) (H ((k : ℝ≥0) / (n + 1))) p) =
        H (leftGrid n p.1) p.2 := by
      apply le_antisymm
      · apply iSup_le
        intro k
        by_cases hk : p.1 ∈ Ioc ((k : ℝ≥0) / (n + 1)) ((k + 1 : ℝ≥0) / (n + 1))
        · have heq := grid_index_unique hk hmem
          subst k
          rw [windowStep, ite_eq_left hk]
          exact le_rfl
        · simp [windowStep, hk]
      · apply le_iSup_of_le (leftIndex n p.1)
        rw [windowStep, ite_eq_left hmem]
        exact le_rfl
    change (if p.1 = 0 then H 0 p.2 else 0) ⊔ _ = _
    rw [ite_eq_right (ne_of_gt hp), hs]
    exact sup_eq_right.mpr bot_le
  apply measurable_of_tendsto_metrizable hFm
  apply tendsto_pi_nhds.mpr
  intro p
  by_cases hp : p.1 = 0
  · have heq : (fun n => F n p) = fun _ => H 0 p.2 := by
      funext n
      simp [F, hp, windowStep]
    simpa only [hp, heq] using (tendsto_const_nhds (x := H 0 p.2))
  · have hp' : 0 < p.1 := pos_iff_ne_zero.mpr hp
    simpa only [hFeq hp', Function.comp_def] using
      (hleft p.2 p.1 hp').tendsto.comp (tendsto_leftGrid hp')

end BGW.StableTrees
