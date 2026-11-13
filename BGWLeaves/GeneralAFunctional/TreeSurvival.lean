module

public import BGWLeaves.GeneralAFunctional.TreeConcentration

/-! Vanishing missing mass for deterministic surviving-prefix restrictions. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeSurvival

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralAFunctional.TreeEvents BGWLeaves.GeneralAFunctional.TreeConcentration
open scoped ENNReal Topology Classical

theorem ae_conditioning_event {μ : PMF ℕ} {A : Set ℕ} {n : ℕ}
    (hn : ZetaAAdmissible μ A n) :
    ∀ᵐ T ∂(zetaATreeLaw μ A n).toMeasure, FiniteVertices T ∧ zetaA A T = (n : ℕ∞) := by
  rw [coe_zetaATreeLaw hn]
  exact ae_cond_mem (measurableSet_zetaAEvent A n)

/-- Every prefix whose asymptotic length is strictly below the conditioned
total size survives with probability tending to one. -/
theorem small_size_probability_tendsto {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {l : ℕ → ℕ} {s : ℝ}
    (hl : Tendsto (fun k => (l k : ℝ) / q k) atTop (𝓝 s))
    (hs : s < 1 / (μ.toMeasure A).toReal) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).toMeasure.real
      {T | treeSize T ≤ l k}) atTop (𝓝 0) := by
  let δ := (1 / (μ.toMeasure A).toReal - s) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hupper : s < 1 / (μ.toMeasure A).toReal - 2 * δ := by dsimp [δ]; linarith
  apply squeeze_zero' (Eventually.of_forall fun _ => measureReal_nonneg) ?_
    (conditional_size_concentration hc hne hDA hA hqtop hq hδ)
  filter_upwards [hl.eventually (eventually_lt_nhds hupper), hqtop.eventually_ge_atTop 1]
    with k hk hkn
  apply measureReal_mono ?_ (measure_ne_top _ _)
  intro T hT
  have hqpos : (0 : ℝ) < q k := by exact_mod_cast hkn
  have hTl : (treeSize T : ℝ) / q k ≤ (l k : ℝ) / q k :=
    div_le_div_of_nonneg_right (by exact_mod_cast hT) hqpos.le
  change δ < |(treeSize T : ℝ) / q k - 1 / (μ.toMeasure A).toReal|
  have hlow := neg_le_abs ((treeSize T : ℝ) / q k - 1 / (μ.toMeasure A).toReal)
  linarith

/-- The floor clock `r_n = floor(n/μ(A))` is the appropriate deterministic scale. -/
theorem exploration_index_ratio {m : ℝ} (hm : 0 < m) :
    Tendsto (fun n : ℕ => (⌊(n : ℝ) / m⌋₊ : ℝ) / n) atTop (𝓝 (1 / m)) := by
  have hu : Tendsto (fun n : ℕ => ((n : ℝ) / m) / n) atTop (𝓝 (1 / m)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    field_simp
  have hlo : Tendsto (fun n : ℕ => ((n : ℝ) / m) / n - 1 / (n : ℝ))
      atTop (𝓝 (1 / m)) := by simpa only [sub_zero] using hu.sub tendsto_one_div_atTop_nhds_zero_nat
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hu
  · filter_upwards with n
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith [Nat.lt_floor_add_one ((n : ℝ) / m)]) (Nat.cast_nonneg n)
  · filter_upwards with n
    exact div_le_div_of_nonneg_right (Nat.floor_le (by positivity)) (Nat.cast_nonneg n)

/-- The explicit floor-prefix consequence requested in step A. -/
theorem floor_prefix_missing_mass {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {b : ℝ} (hb0 : 0 < b) (hb1 : b < 1) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).toMeasure.real
      {T | (treeSize T : ℝ) ≤ b * ⌊(q k : ℝ) / (μ.toMeasure A).toReal⌋₊}) atTop (𝓝 0) := by
  have hm : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have hgap : b / (μ.toMeasure A).toReal < 1 / (μ.toMeasure A).toReal :=
    div_lt_div_of_pos_right hb1 hm
  have hl : Tendsto (fun k =>
      (⌊b * ⌊(q k : ℝ) / (μ.toMeasure A).toReal⌋₊⌋₊ : ℝ) / q k) atTop
      (𝓝 (b / (μ.toMeasure A).toReal)) := by
    have hu := ((exploration_index_ratio hm).const_mul b).comp hqtop
    have hlo := hu.sub (tendsto_one_div_atTop_nhds_zero_nat.comp hqtop)
    simp only [sub_zero, mul_one_div] at hu hlo
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hu
    · filter_upwards with k
      dsimp only [Function.comp_def]
      rw [← mul_div_assoc, ← sub_div]
      exact div_le_div_of_nonneg_right
        (by linarith [Nat.lt_floor_add_one (b * (⌊(q k : ℝ) / (μ.toMeasure A).toReal⌋₊ : ℝ))])
        (Nat.cast_nonneg _)
    · filter_upwards with k
      dsimp only [Function.comp_def]
      rw [← mul_div_assoc]
      exact div_le_div_of_nonneg_right (Nat.floor_le (by positivity)) (Nat.cast_nonneg _)
  have ht := small_size_probability_tendsto hc hne hDA hA hqtop hq hl hgap
  apply ht.congr
  intro k
  congr 1
  ext T
  exact Nat.le_floor_iff (by positivity)

end BGWLeaves.GeneralAFunctional.TreeSurvival
