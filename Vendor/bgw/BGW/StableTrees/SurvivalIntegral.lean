/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SurvivalDynamics
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Integral time change for survival

The integral of the reciprocal defect increases asymptotically by one along the survival
recursion. Its value at the survival probability is therefore asymptotic to the generation.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace BGW.StableTrees.Survival

/-- The reciprocal-defect time change, used for arguments in `(0,1]`. -/
noncomputable def survivalTime (μ : PMF ℕ) (x : ℝ) : ℝ :=
  ∫ u in x..1, (offspringDefect μ u)⁻¹

/-- The reciprocal defect is integrable on every compact interval in `(0,1]`. -/
theorem intervalIntegrable_inv_offspringDefect {μ : PMF ℕ} (hc : IsCritical μ)
    (hne : μ 1 ≠ 1) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) (hb : b ≤ 1) :
    IntervalIntegrable (fun u => (offspringDefect μ u)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  apply ((continuousOn_offspringDefect μ).mono
    (show Set.Icc a b ⊆ Set.Icc 0 1 from fun u hu => ⟨ha.le.trans hu.1, hu.2.trans hb⟩)).inv₀
  intro u hu
  exact (offspringDefect_pos hc hne (ha.trans_le hu.1) (hu.2.trans hb)).ne'

/-- The time change is antitone on its positive domain. -/
theorem survivalTime_antitoneOn {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    AntitoneOn (survivalTime μ) (Set.Ioc 0 1) := by
  intro a ha b hb hab
  have hiab := intervalIntegrable_inv_offspringDefect hc hne ha.1 hab hb.2
  have hib := intervalIntegrable_inv_offspringDefect hc hne hb.1 hb.2 le_rfl
  have he := intervalIntegral.integral_add_adjacent_intervals hiab hib
  have hnonneg : 0 ≤ ∫ u in a..b, (offspringDefect μ u)⁻¹ := by
    apply intervalIntegral.integral_nonneg hab
    intro u hu
    exact inv_nonneg.mpr (offspringDefect_nonneg hc (ha.1.le.trans hu.1) (hu.2.trans hb.2))
  dsimp [survivalTime]
  linarith

/-- One survival step increases the time change by an amount between one and the defect ratio. -/
theorem survivalTime_succ_bounds {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (k : ℕ) :
    1 ≤ survivalTime μ (survivalProb μ (k + 1)) - survivalTime μ (survivalProb μ k) ∧
      survivalTime μ (survivalProb μ (k + 1)) - survivalTime μ (survivalProb μ k) ≤
        offspringDefect μ (survivalProb μ k) / offspringDefect μ (survivalProb μ (k + 1)) := by
  let a := survivalProb μ (k + 1)
  let b := survivalProb μ k
  have ha : 0 < a := survivalProb_pos hc hne _
  have hb : 0 < b := survivalProb_pos hc hne _
  have hab : a ≤ b := antitone_survivalProb μ (by omega)
  have hb1 : b ≤ 1 := (survivalProb_mem_Icc μ k).2
  have hpa : 0 < offspringDefect μ a := offspringDefect_pos hc hne ha (hab.trans hb1)
  have hpb : 0 < offspringDefect μ b := offspringDefect_pos hc hne hb hb1
  have hiab := intervalIntegrable_inv_offspringDefect hc hne ha hab hb1
  have hib := intervalIntegrable_inv_offspringDefect hc hne hb hb1 le_rfl
  have htime : survivalTime μ a - survivalTime μ b =
      ∫ u in a..b, (offspringDefect μ u)⁻¹ := by
    have he := intervalIntegral.integral_add_adjacent_intervals hiab hib
    dsimp [survivalTime]
    linarith
  have hstep : b - a = offspringDefect μ b := survivalProb_sub_succ μ k
  change 1 ≤ survivalTime μ a - survivalTime μ b ∧ _
  rw [htime]
  constructor
  · have hl := intervalIntegral.integral_mono_on hab (intervalIntegrable_const) hiab
      (show ∀ u ∈ Set.Icc a b, (offspringDefect μ b)⁻¹ ≤ (offspringDefect μ u)⁻¹ from by
        intro u hu
        apply inv_anti₀ (offspringDefect_pos hc hne (ha.trans_le hu.1) (hu.2.trans hb1))
        exact offspringDefect_monotoneOn hc ⟨ha.le.trans hu.1, hu.2.trans hb1⟩ ⟨hb.le, hb1⟩ hu.2)
    simpa [intervalIntegral.integral_const, smul_eq_mul, hstep, hpb.ne'] using hl
  · have hh := intervalIntegral.integral_mono_on hab hiab (intervalIntegrable_const)
      (show ∀ u ∈ Set.Icc a b, (offspringDefect μ u)⁻¹ ≤ (offspringDefect μ a)⁻¹ from by
        intro u hu
        apply inv_anti₀ hpa
        exact offspringDefect_monotoneOn hc ⟨ha.le, hab.trans hb1⟩
          ⟨ha.le.trans hu.1, hu.2.trans hb1⟩ hu.1)
    simpa [intervalIntegral.integral_const, smul_eq_mul, hstep, div_eq_mul_inv] using hh

/-- The time-change increment tends to one along successive generations. -/
theorem tendsto_survivalTime_increment {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) :
    Tendsto (fun k => survivalTime μ (survivalProb μ (k + 1)) -
      survivalTime μ (survivalProb μ k)) atTop (𝓝 1) := by
  have hr := (tendsto_offspringDefect_survivalProb_succ_div h).inv₀ one_ne_zero
  simp only [inv_one, inv_div] at hr
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hr
    (fun k => (survivalTime_succ_bounds h.critical h.nondegenerate k).1)
    (fun k => (survivalTime_succ_bounds h.critical h.nondegenerate k).2)

/-- The integral time change at generation `k` is asymptotic to `k`. -/
theorem tendsto_survivalTime_div_natCast {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) :
    Tendsto (fun k => survivalTime μ (survivalProb μ k) / k) atTop (𝓝 1) := by
  have ht := (tendsto_survivalTime_increment h).cesaro
  apply ht.congr
  intro k
  rw [Finset.sum_range_sub (fun k => survivalTime μ (survivalProb μ k))]
  simp [survivalProb_zero, survivalTime, div_eq_mul_inv, mul_comm]

end BGW.StableTrees.Survival
