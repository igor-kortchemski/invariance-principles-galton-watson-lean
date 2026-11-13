/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForest
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Semicontinuity.Basic

/-!
# Oscillation observables for the discrete forest height

The height is interpolated before rescaling. Its modulus is measurable as a
lower semicontinuous functional of the continuous height path. The final adjacent
height jump is bounded by the modulus on the longer horizon `T + 1`, and the modulus
is monotone in its time scale. A generic dominated convergence lemma for events that
eventually fail almost surely is also recorded here.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal Classical

namespace BGW.StableTrees.HeightTightness

open BGW.StableTrees.DiscreteForest

/-- The modulus of continuity at scale `δ` of the normalized interpolated height on `[0,T]`. -/
noncomputable def heightOscillation (B : ℕ → ℝ) (n : ℕ) (T δ : ℝ) (ω : ℕ → ℕ) : ℝ :=
  ⨆ s : Set.Icc (0 : ℝ) T, ⨆ t : Set.Icc (0 : ℝ) T,
    if |(s : ℝ) - t| ≤ δ then
      |B n / n * forestHeightLin ω (n * s) - B n / n * forestHeightLin ω (n * t)|
    else 0

/-- The normalized largest adjacent height jump before index `⌊n T⌋ + 1`. -/
noncomputable def maxHeightJump (B : ℕ → ℝ) (n : ℕ) (T : ℝ) (ω : ℕ → ℕ) : ℝ :=
  B n / n * (((Finset.range (⌊(n : ℝ) * T⌋₊ + 1)).sup
    (fun k => ((forestHeight ω (k + 1) : ℤ) - forestHeight ω k).natAbs) : ℕ) : ℝ)

/-- Events that almost surely hold only finitely often have probabilities tending to zero. -/
theorem tendsto_measureReal_zero_of_eventually_notMem {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E : ℕ → Set Ω}
    (hm : ∀ N, MeasurableSet (E N)) (hev : ∀ᵐ f ∂P, ∀ᶠ N : ℕ in atTop, f ∉ E N) :
    Tendsto (fun N : ℕ => P.real (E N)) atTop (𝓝 0) := by
  have he (N : ℕ) : (∫ f, (E N).indicator (fun _ => (1 : ℝ)) f ∂P) = P.real (E N) :=
    integral_indicator_one (hm N)
  have hconv : Tendsto (fun N : ℕ => ∫ f, (E N).indicator (fun _ => (1 : ℝ)) f ∂P)
      atTop (𝓝 (∫ _ : Ω, (0 : ℝ) ∂P)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => (1 : ℝ))
    · intro N
      exact (measurable_const.indicator (hm N)).aestronglyMeasurable
    · exact integrable_const _
    · intro N
      exact Eventually.of_forall fun f => by
        by_cases hf : f ∈ E N <;> simp [hf]
    · filter_upwards [hev] with f hf
      exact tendsto_const_nhds.congr' (hf.mono fun N hN => by
        change (0 : ℝ) = (E N).indicator (fun _ => (1 : ℝ)) f
        rw [Set.indicator_of_notMem hN])
  simpa only [he, integral_zero] using hconv

private theorem bounded_heightDifference {T : ℝ≥0}
    (f : C(Set.Icc (0 : ℝ) (T : ℝ), ℝ)) (δ : ℝ)
    (s t : Set.Icc (0 : ℝ) (T : ℝ)) :
    (if |(s : ℝ) - t| ≤ δ then |f s - f t| else 0) ≤ 2 * ‖f‖ := by
  split_ifs
  · exact (abs_sub (f s) (f t)).trans (by
      have hs := f.norm_coe_le_norm s
      have ht := f.norm_coe_le_norm t
      rw [Real.norm_eq_abs] at hs ht
      linarith)
  · positivity

private theorem measurable_pathOscillation (T : ℝ≥0) (δ : ℝ) :
    Measurable (fun f : C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) =>
      ⨆ s : Set.Icc (0 : ℝ) (T : ℝ), ⨆ t : Set.Icc (0 : ℝ) (T : ℝ),
        if |(s : ℝ) - t| ≤ δ then |f s - f t| else 0) := by
  let : Nonempty (Set.Icc (0 : ℝ) (T : ℝ)) := ⟨⟨0, le_rfl, T.coe_nonneg⟩⟩
  apply LowerSemicontinuous.measurable
  apply lowerSemicontinuous_ciSup
  · intro f
    refine ⟨2 * ‖f‖, ?_⟩
    rintro _ ⟨s, rfl⟩
    exact ciSup_le (fun t => bounded_heightDifference f δ s t)
  · intro s
    apply lowerSemicontinuous_ciSup
    · intro f
      refine ⟨2 * ‖f‖, ?_⟩
      rintro _ ⟨t, rfl⟩
      exact bounded_heightDifference f δ s t
    · intro t
      by_cases hst : |(s : ℝ) - t| ≤ δ
      · simp only [ite_eq_left hst]
        exact (by fun_prop : Continuous (fun f : C(Set.Icc (0 : ℝ) (T : ℝ), ℝ) =>
          |f s - f t|)).lowerSemicontinuous
      · simp only [ite_eq_right hst]
        exact continuous_const.lowerSemicontinuous

/-- The interpolated-height modulus is a measurable observable of the offspring sequence. -/
theorem measurable_heightOscillation (B : ℕ → ℝ) (n : ℕ) (T δ : ℝ) :
    Measurable (heightOscillation B n T δ) := by
  unfold heightOscillation
  by_cases hT : 0 ≤ T
  · have hm := (measurable_pathOscillation ⟨T, hT⟩ δ).comp
      (measurable_forestPairPath B n ⟨T, hT⟩).snd
    convert hm using 1
    rfl
  · have : IsEmpty (Set.Icc (0 : ℝ) T) :=
      ⟨fun t => hT (t.property.1.trans t.property.2)⟩
    simpa only [iSup_of_empty', Real.sSup_empty] using
      (measurable_const : Measurable (fun _ : ℕ → ℕ => (0 : ℝ)))

private theorem forestHeightLin_natCast (ω : ℕ → ℕ) (k : ℕ) :
    forestHeightLin ω (k : ℝ) = (forestHeight ω k : ℝ) := by
  simp [forestHeightLin]

private theorem osc_bdd (B : ℕ → ℝ) (n : ℕ) {T : ℝ} (hT : 0 ≤ T)
    (δ : ℝ) (ω : ℕ → ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t : Set.Icc (0 : ℝ) T,
      (if |(s : ℝ) - t| ≤ δ then
        |B n / n * forestHeightLin ω (n * s) - B n / n * forestHeightLin ω (n * t)|
      else 0) ≤ C := by
  let f := forestHeightPath B n ⟨T, hT⟩ ω
  refine ⟨2 * ‖f‖, by positivity, ?_⟩
  intro s t
  split_ifs
  · have hs := f.norm_coe_le_norm s
    have ht := f.norm_coe_le_norm t
    rw [Real.norm_eq_abs] at hs ht
    exact (abs_sub _ _).trans (by change |f s| + |f t| ≤ _; linarith)
  · positivity

/-- A pair of height evaluations within distance `δ` is bounded by the modulus. -/
theorem heightDifference_le_heightOscillation (B : ℕ → ℝ) (n : ℕ)
    {T δ : ℝ} (hT : 0 ≤ T) (ω : ℕ → ℕ)
    (s t : Set.Icc (0 : ℝ) T) (hst : |(s : ℝ) - t| ≤ δ) :
    |B n / n * forestHeightLin ω (n * s) - B n / n * forestHeightLin ω (n * t)| ≤
      heightOscillation B n T δ ω := by
  let : Nonempty (Set.Icc (0 : ℝ) T) := ⟨s⟩
  obtain ⟨C, _, hC⟩ := osc_bdd B n hT δ ω
  have hb (u : Set.Icc (0 : ℝ) T) : BddAbove (Set.range fun v : Set.Icc (0 : ℝ) T =>
      if |(u : ℝ) - v| ≤ δ then
        |B n / n * forestHeightLin ω (n * u) - B n / n * forestHeightLin ω (n * v)|
      else 0) := ⟨C, by rintro _ ⟨v, rfl⟩; exact hC u v⟩
  have ho : BddAbove (Set.range fun u : Set.Icc (0 : ℝ) T =>
      ⨆ v : Set.Icc (0 : ℝ) T, if |(u : ℝ) - v| ≤ δ then
        |B n / n * forestHeightLin ω (n * u) - B n / n * forestHeightLin ω (n * v)|
      else 0) := ⟨C, by rintro _ ⟨u, rfl⟩; exact ciSup_le (hC u)⟩
  have hi := le_ciSup (hb s) t
  rw [ite_eq_left hst] at hi
  exact hi.trans (le_ciSup ho s)

/-- The final adjacent jump is controlled by the modulus on the longer horizon `T + 1`. -/
theorem maxHeightJump_le_heightOscillation (B : ℕ → ℝ) {n : ℕ} (hn : 1 ≤ n)
    {T : ℝ} (hT : 0 ≤ T) (hB : 0 ≤ B n) (ω : ℕ → ℕ) :
    maxHeightJump B n T ω ≤ heightOscillation B n (T + 1) (1 / n) ω := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  obtain ⟨k, hk, he⟩ := (Finset.range (⌊(n : ℝ) * T⌋₊ + 1)).exists_mem_eq_sup
    ⟨0, by simp⟩ (fun k => ((forestHeight ω (k + 1) : ℤ) - forestHeight ω k).natAbs)
  have hkN : k ≤ ⌊(n : ℝ) * T⌋₊ := by simpa using hk
  have hkR : (k : ℝ) ≤ (n : ℝ) * T :=
    (Nat.cast_le.mpr hkN).trans (Nat.floor_le (by positivity))
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  let s : Set.Icc (0 : ℝ) (T + 1) := ⟨k / (n : ℝ), by
    constructor
    · positivity
    · apply (div_le_iff₀ hnR).mpr
      nlinarith⟩
  let t : Set.Icc (0 : ℝ) (T + 1) := ⟨(k + 1 : ℕ) / (n : ℝ), by
    constructor
    · positivity
    · apply (div_le_iff₀ hnR).mpr
      push_cast
      nlinarith⟩
  have hst : |(s : ℝ) - t| ≤ 1 / n := by
    change |(k : ℝ) / n - ((k + 1 : ℕ) : ℝ) / n| ≤ 1 / n
    rw [Nat.cast_add_one, ← sub_div, show (k : ℝ) - (k + 1) = -1 by ring,
      neg_div, abs_neg, abs_of_pos (one_div_pos.mpr hnR)]
  have hb := heightDifference_le_heightOscillation B n (by positivity : 0 ≤ T + 1) ω s t hst
  have hs : (n : ℝ) * (s : ℝ) = k := by dsimp [s]; field_simp
  have ht : (n : ℝ) * (t : ℝ) = (k + 1 : ℕ) := by dsimp [t]; field_simp
  rw [hs, ht, forestHeightLin_natCast, forestHeightLin_natCast] at hb
  unfold maxHeightJump
  rw [he]
  have habs : (((forestHeight ω (k + 1) : ℤ) - forestHeight ω k).natAbs : ℝ) =
      |(forestHeight ω (k + 1) : ℝ) - forestHeight ω k| := by
    rw [Nat.cast_natAbs, Int.cast_abs, Int.cast_sub, Int.cast_natCast, Int.cast_natCast]
  rw [habs]
  calc
    _ = |B n / n * (forestHeight ω k : ℝ) -
        B n / n * (forestHeight ω (k + 1) : ℝ)| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (div_nonneg hB hnR.le), abs_sub_comm]
    _ ≤ _ := hb
/-- Pairwise bounds on the admissible time pairs bound the entire height modulus. -/
theorem heightOscillation_le (B : ℕ → ℝ) (n : ℕ) {T δ M : ℝ}
    (hT : 0 ≤ T) (hM : 0 ≤ M) (ω : ℕ → ℕ)
    (hb : ∀ s t : Set.Icc (0 : ℝ) T, |(s : ℝ) - t| ≤ δ →
      |B n / n * forestHeightLin ω (n * s) - B n / n * forestHeightLin ω (n * t)| ≤ M) :
    heightOscillation B n T δ ω ≤ M := by
  let : Nonempty (Set.Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  unfold heightOscillation
  apply ciSup_le
  intro s
  apply ciSup_le
  intro t
  split_ifs with hst
  · exact hb s t hst
  · exact hM

/-- The height modulus increases with its time scale, for a nonnegative upper scale. -/
theorem heightOscillation_mono (B : ℕ → ℝ) (n : ℕ) {T δ δ' : ℝ}
    (hT : 0 ≤ T) (hδ' : 0 ≤ δ') (hδ : δ ≤ δ') (ω : ℕ → ℕ) :
    heightOscillation B n T δ ω ≤ heightOscillation B n T δ' ω := by
  let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT⟩
  have hnonneg : 0 ≤ heightOscillation B n T δ' ω := by
    simpa only [sub_self, abs_zero] using
      heightDifference_le_heightOscillation B n hT ω z z (by simpa using hδ')
  exact heightOscillation_le B n hT hnonneg ω fun s t hst =>
    heightDifference_le_heightOscillation B n hT ω s t (hst.trans hδ)

end BGW.StableTrees.HeightTightness
