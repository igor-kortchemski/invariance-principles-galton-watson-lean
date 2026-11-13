/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.ExcursionMeasureBasic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Window intensities of the excursion process, including mark sets of infinite intensity.

See Bertoin, *Lévy Processes*, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod
open BGW.Probability

namespace BGW.StableTrees

/-- Lebesgue measure on `ℝ≥0` (flagged: Mathlib has no `MeasureSpace ℝ≥0`; this is the pullback of
`volume` on `ℝ` under the coercion, so `lebNN (Ioc a b) = b - a`). -/
noncomputable def lebNN : Measure ℝ≥0 := Measure.comap ((↑) : ℝ≥0 → ℝ) volume

/-- Lebesgue measure of an interval. -/
theorem lebNN_Ioc (a b : ℝ≥0) : lebNN (Ioc a b) = ((b - a : ℝ≥0) : ℝ≥0∞) := by
  have he : MeasurableEmbedding ((↑) : ℝ≥0 → ℝ) :=
    (MeasurableEmbedding.subtype_coe measurableSet_Ici)
  rw [lebNN, he.comap_apply]
  have hi : ((↑) : ℝ≥0 → ℝ) '' Ioc a b = Ioc (a : ℝ) (b : ℝ) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, le_trans a.2 hx.1.le⟩, hx, rfl⟩
  rw [hi, Real.volume_Ioc]
  calc
    ENNReal.ofReal ((b : ℝ) - (a : ℝ)) =
        ENNReal.ofReal (b : ℝ) - ENNReal.ofReal (a : ℝ) :=
      ENNReal.ofReal_sub (b : ℝ) (NNReal.coe_nonneg a)
    _ = _ := by simp only [ENNReal.ofReal_coe_nnreal, ENNReal.coe_sub]

/-- The increasing lifetime exhaustion used to extend finite-rate formulas. -/
def excursionLifetimeSlab (n : ℕ) : Set Excursion :=
  {e | 1 / (n + 1 : ℝ≥0) < e.lifetime}

/-- Lifetime slabs are measurable. -/
theorem measurableSet_excursionLifetimeSlab (n : ℕ) :
    MeasurableSet (excursionLifetimeSlab n) :=
  measurableSet_lt measurable_const measurable_excursion_lifetime

/-- Lifetime slabs increase with their index. -/
theorem monotone_excursionLifetimeSlab : Monotone excursionLifetimeSlab := by
  intro n m hnm e he
  apply lt_of_le_of_lt ?_ he
  apply NNReal.coe_le_coe.mp
  push_cast
  apply one_div_le_one_div_of_le (by positivity)
  exact_mod_cast Nat.add_le_add_right hnm 1

/-- Every excursion belongs to a lifetime slab. -/
theorem iUnion_excursionLifetimeSlab : (⋃ n, excursionLifetimeSlab n) = univ := by
  apply eq_univ_of_forall
  intro e
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt e.lifetime_pos
  exact mem_iUnion.mpr ⟨n, hn⟩

/-- **Mean measure of windows**: for a measurable modification `ξ`, `a ≤ b` and measurable `A`
(finite or infinite rate), `E ξ((a,b] × A) = (b - a) N(A)`. -/
theorem lintegral_windowMark_eq {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {ξ : DLoc → Measure (ℝ≥0 × Excursion)} (hξ : Measurable ξ)
    (hae : ξ =ᵐ[(stableLocalLaw θ : Measure DLoc)] excursionPointMeasure)
    {a b : ℝ≥0} (hab : a ≤ b) {A : Set Excursion} (hA : MeasurableSet A) :
    ∫⁻ f, ξ f (Ioc a b ×ˢ A) ∂(stableLocalLaw θ : Measure DLoc) =
      ((b - a : ℝ≥0) : ℝ≥0∞) * excursionMeasure θ A := by
  obtain ⟨hlevy, hslab⟩ := isTimeSimpleLevy_of_ae_eq_excursionPointMeasure hθ hξ hae
  let C : ℕ → Set Excursion := fun n => A ∩ excursionLifetimeSlab n
  have hCm (n : ℕ) : MeasurableSet (C n) :=
    hA.inter (measurableSet_excursionLifetimeSlab n)
  have hCmono : Monotone C := fun n m h => inter_subset_inter_right A
    (monotone_excursionLifetimeSlab h)
  have hCu : (⋃ n, C n) = A := by simp [C, ← inter_iUnion, iUnion_excursionLifetimeSlab]
  have hrate (n : ℕ) : IsFiniteRate (stableLocalLaw θ : Measure DLoc) ξ (C n) := by
    refine ⟨hCm n, fun t => ?_⟩
    filter_upwards [(hslab (1 / (n + 1)) (by positivity)).2.2 t] with f hf
    exact lt_of_le_of_lt (measure_mono (Set.prod_mono Subset.rfl inter_subset_right)) hf
  have hformula (n : ℕ) :
      (∫⁻ f, ξ f (Ioc a b ×ˢ C n) ∂(stableLocalLaw θ : Measure DLoc)) =
        ((b - a : ℝ≥0) : ℝ≥0∞) * excursionMeasure θ (C n) := by
    rw [(excursionMeasure_apply_of_ae_eq hθ hξ hae (hCm n)).2]
    exact lintegral_count_window hlevy (hrate n) hab
  have hboxes : (⋃ n, Ioc a b ×ˢ C n) = Ioc a b ×ˢ A := by
    rw [← prod_iUnion, hCu]
  calc
    _ = ∫⁻ f, ⨆ n, ξ f (Ioc a b ×ˢ C n) ∂(stableLocalLaw θ : Measure DLoc) := by
      congr 1
      funext f
      rw [← hboxes]
      exact Monotone.measure_iUnion (fun n m h => Set.prod_mono Subset.rfl (hCmono h))
    _ = ⨆ n, ∫⁻ f, ξ f (Ioc a b ×ˢ C n) ∂(stableLocalLaw θ : Measure DLoc) := by
      rw [lintegral_iSup]
      · intro n
        exact measurable_count hξ (measurable_box (hCm n))
      · intro n m h f
        exact measure_mono (Set.prod_mono Subset.rfl (hCmono h))
    _ = ⨆ n, ((b - a : ℝ≥0) : ℝ≥0∞) * excursionMeasure θ (C n) := by
      simp_rw [hformula]
    _ = _ := by
      rw [← ENNReal.mul_iSup, ← hCmono.measure_iUnion, hCu]

end BGW.StableTrees
