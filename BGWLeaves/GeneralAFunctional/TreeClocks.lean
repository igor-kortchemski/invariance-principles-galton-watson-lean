module

public import BGWLeaves.GeneralAFunctional.TreeKernel
public import BGWLeaves.GeneralAFunctional.TreeSurvival

/-! Deterministic total-size clocks and room between two prefix horizons. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreeClocks

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.GeneralAFunctional.TreeSurvival
open BGWLeaves.GeneralAFunctional.TreeLocal
open scoped ENNReal NNReal Topology

noncomputable def explorationIndex (μ : PMF ℕ) (A : Set ℕ) (n : ℕ) : ℕ :=
  ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊

noncomputable def prefixLength (b : ℝ≥0) (r : ℕ) : ℕ := ⌊(b : ℝ) * r⌋₊

theorem explorationIndex_atTop {μ : PMF ℕ} {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    Tendsto (explorationIndex μ A) atTop atTop := by
  have hp : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  exact tendsto_nat_floor_atTop.comp (tendsto_natCast_atTop_atTop.atTop_div_const hp)

theorem explorationIndex_ratio {μ : PMF ℕ} {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    Tendsto (fun n => (explorationIndex μ A n : ℝ) / n) atTop
      (𝓝 (1 / (μ.toMeasure A).toReal)) :=
  exploration_index_ratio (ENNReal.toReal_pos hA (measure_ne_top _ _))

theorem prefixLength_ratio (b : ℝ≥0) :
    Tendsto (fun r : ℕ => (prefixLength b r : ℝ) / r) atTop (𝓝 (b : ℝ)) :=
  (tendsto_nat_floor_mul_div_atTop b.coe_nonneg).comp tendsto_natCast_atTop_atTop

theorem prefixLength_lt {b : ℝ≥0} (hb : b < 1) {r : ℕ} (hr : 0 < r) :
    prefixLength b r < r := by
  apply (Nat.floor_lt (mul_nonneg b.coe_nonneg (Nat.cast_nonneg r))).mpr
  exact mul_lt_of_lt_one_left (by exact_mod_cast hr) hb

theorem prefixLength_room {a b : ℝ≥0} (hab : a < b) :
    ∀ᶠ r : ℕ in atTop, ⌊(a : ℝ) * r⌋₊ + 1 ≤ prefixLength b r := by
  have hgap : 0 < (b : ℝ) - a := sub_pos.mpr (NNReal.coe_lt_coe.mpr hab)
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_ge_atTop (1 / ((b : ℝ) - a)))] with r hr
  apply Nat.le_floor
  have hf := Nat.floor_le (mul_nonneg a.coe_nonneg (Nat.cast_nonneg r))
  have hh := (div_le_iff₀ hgap).mp hr
  push_cast
  nlinarith

theorem prefixLength_exploration_ratio {μ : PMF ℕ} {A : Set ℕ}
    (hA : μ.toMeasure A ≠ 0) (b : ℝ≥0) :
    Tendsto (fun n => (prefixLength b (explorationIndex μ A n) : ℝ) / n) atTop
      (𝓝 ((b : ℝ) / (μ.toMeasure A).toReal)) := by
  have hr := explorationIndex_atTop hA
  have ht := ((prefixLength_ratio b).comp hr).mul (explorationIndex_ratio hA)
  simp only [mul_one_div] at ht
  apply ht.congr'
  filter_upwards [hr.eventually_ne_atTop 0] with n hn
  have hnR : (explorationIndex μ A n : ℝ) ≠ 0 := by exact_mod_cast hn
  dsimp only [Function.comp_def]
  field_simp

theorem markScale_ratio_exploration {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    Tendsto (fun n => markScale μ A θ n / B (explorationIndex μ A n)) atTop (𝓝 1) := by
  have hattr : IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) B := by
    rw [mean_stepLaw h.critical]
    exact stableDomain_isStableAttracted h
  exact (norming_isEquivalent (stepLaw μ) (stepLaw_lt_neg_one μ)
    (integrable_stepLaw h.critical) hattr).comp (explorationIndex_atTop hA)

end BGWLeaves.GeneralAFunctional.TreeClocks
