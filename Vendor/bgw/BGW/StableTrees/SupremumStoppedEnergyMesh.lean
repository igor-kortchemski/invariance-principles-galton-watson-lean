/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumStoppedEnergyGrid
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.UniformSpace.HeineCantor

/-!
# Vanishing continuous-variation remainder for the stopped energy estimate

The equally spaced mesh controls the squared-increment remainder by uniform continuity
of the difference and the total increments of its two monotone components.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology
open scoped NNReal
namespace BGW.StableTrees

/-- Equally spaced grid on a fixed nonnegative time interval. -/
noncomputable def stoppedEnergyGrid (T : ℝ≥0) (N k : ℕ) : ℝ≥0 := k / (N + 1) * T

private lemma stoppedEnergyGrid_zero (T : ℝ≥0) (N : ℕ) :
    stoppedEnergyGrid T N 0 = 0 := by simp [stoppedEnergyGrid]

private lemma stoppedEnergyGrid_last (T : ℝ≥0) (N : ℕ) : stoppedEnergyGrid T N (N + 1) = T := by
  simp [stoppedEnergyGrid, Nat.cast_add, Nat.cast_one]

private lemma stoppedEnergyGrid_mono (T : ℝ≥0) (N : ℕ) : Monotone (stoppedEnergyGrid T N) := by
  intro k l hkl
  dsimp [stoppedEnergyGrid]
  gcongr

private lemma stoppedEnergyGrid_dist (T : ℝ≥0) (N k : ℕ) :
    dist (stoppedEnergyGrid T N (k + 1)) (stoppedEnergyGrid T N k) = (T : ℝ) / (N + 1) := by
  rw [NNReal.dist_eq, abs_of_nonneg (NNReal.coe_le_coe.mpr
    (stoppedEnergyGrid_mono T N (Nat.le_succ k)) |> sub_nonneg.mpr)]
  simp only [stoppedEnergyGrid, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_natCast,
    NNReal.coe_add, NNReal.coe_one, Nat.cast_succ]
  field_simp
  ring

private lemma mesh_sum_le (O M : ℝ≥0 → ℝ) (hO : Monotone O) (hM : Monotone M)
    (T : ℝ≥0) (N : ℕ) {η : ℝ} (hη : 0 ≤ η)
    (hb : ∀ k < N + 1, |(O (stoppedEnergyGrid T N (k + 1)) - M (stoppedEnergyGrid T N (k + 1))) -
      (O (stoppedEnergyGrid T N k) - M (stoppedEnergyGrid T N k))| ≤ η) :
    (∑ k ∈ Finset.range (N + 1),
      ((O (stoppedEnergyGrid T N (k + 1)) - M (stoppedEnergyGrid T N (k + 1))) -
        (O (stoppedEnergyGrid T N k) - M (stoppedEnergyGrid T N k))) ^ 2) ≤
      η * (O T - O 0 + (M T - M 0)) := by
  calc
    _ ≤ ∑ k ∈ Finset.range (N + 1), η *
        ((O (stoppedEnergyGrid T N (k + 1)) - O (stoppedEnergyGrid T N k)) +
          (M (stoppedEnergyGrid T N (k + 1)) - M (stoppedEnergyGrid T N k))) := by
      apply Finset.sum_le_sum
      intro k hk
      have ho := sub_nonneg.mpr (hO (stoppedEnergyGrid_mono T N (Nat.le_succ k)))
      have hm := sub_nonneg.mpr (hM (stoppedEnergyGrid_mono T N (Nat.le_succ k)))
      have h1 := hb k (Finset.mem_range.mp hk)
      have h2 := abs_sub (O (stoppedEnergyGrid T N (k + 1)) - O (stoppedEnergyGrid T N k))
        (M (stoppedEnergyGrid T N (k + 1)) - M (stoppedEnergyGrid T N k))
      rw [abs_of_nonneg ho, abs_of_nonneg hm] at h2
      have he : (O (stoppedEnergyGrid T N (k + 1)) - M (stoppedEnergyGrid T N (k + 1))) -
          (O (stoppedEnergyGrid T N k) - M (stoppedEnergyGrid T N k)) =
          (O (stoppedEnergyGrid T N (k + 1)) - O (stoppedEnergyGrid T N k)) -
          (M (stoppedEnergyGrid T N (k + 1)) - M (stoppedEnergyGrid T N k)) := by ring
      rw [he] at h1 ⊢
      nlinarith [abs_nonneg ((O (stoppedEnergyGrid T N (k + 1)) - O (stoppedEnergyGrid T N k)) -
        (M (stoppedEnergyGrid T N (k + 1)) - M (stoppedEnergyGrid T N k))),
        sq_abs ((O (stoppedEnergyGrid T N (k + 1)) - O (stoppedEnergyGrid T N k)) -
          (M (stoppedEnergyGrid T N (k + 1)) - M (stoppedEnergyGrid T N k)))]
    _ = _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib,
        Finset.sum_range_sub (f := fun k => O (stoppedEnergyGrid T N k)),
        Finset.sum_range_sub (f := fun k => M (stoppedEnergyGrid T N k)),
        stoppedEnergyGrid_zero, stoppedEnergyGrid_last]

/-- Squared increments of a continuous difference of two monotone paths vanish
on equally spaced grids. -/
theorem tendsto_stoppedEnergyGrid_sq_increments (O M : ℝ≥0 → ℝ) (hO : Monotone O) (hM : Monotone M)
    (hC : Continuous (fun s => O s - M s)) (T : ℝ≥0) :
    Tendsto (fun N => ∑ k ∈ Finset.range (N + 1),
      ((O (stoppedEnergyGrid T N (k + 1)) - M (stoppedEnergyGrid T N (k + 1))) -
        (O (stoppedEnergyGrid T N k) - M (stoppedEnergyGrid T N k))) ^ 2) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let L := O T - O 0 + (M T - M 0)
  have hL : 0 ≤ L := add_nonneg (sub_nonneg.mpr (hO (zero_le : 0 ≤ T)))
    (sub_nonneg.mpr (hM (zero_le : 0 ≤ T)))
  have hη : 0 < ε / (L + 1) := div_pos hε (by positivity)
  have hu := (isCompact_Icc : IsCompact (Icc (0 : ℝ≥0) T)).uniformContinuousOn_of_continuous
    hC.continuousOn
  obtain ⟨δ, hδ, hdist⟩ := Metric.uniformContinuousOn_iff.mp hu _ hη
  have hstep : Tendsto (fun N : ℕ => (T : ℝ) / ((N : ℝ) + 1)) atTop (𝓝 0) := by
    simpa only [mul_zero, mul_one_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (T : ℝ)
  filter_upwards [hstep.eventually (Iio_mem_nhds hδ)] with N hN
  have hb (k : ℕ) (hk : k < N + 1) :
      |(O (stoppedEnergyGrid T N (k + 1)) - M (stoppedEnergyGrid T N (k + 1))) -
        (O (stoppedEnergyGrid T N k) - M (stoppedEnergyGrid T N k))| ≤ ε / (L + 1) := by
    have hle {j : ℕ} (hj : j ≤ N + 1) : stoppedEnergyGrid T N j ≤ T := by
      exact (stoppedEnergyGrid_mono T N hj).trans_eq (stoppedEnergyGrid_last T N)
    have hh := hdist (stoppedEnergyGrid T N (k + 1)) ⟨zero_le, hle (by omega)⟩
      (stoppedEnergyGrid T N k) ⟨zero_le, hle (by omega)⟩
      (by simpa only [stoppedEnergyGrid_dist] using hN)
    exact (Real.dist_eq _ _ ▸ hh).le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
  apply (mesh_sum_le O M hO hM T N hη.le hb).trans_lt
  change ε / (L + 1) * L < ε
  have he := div_mul_cancel₀ ε (show L + 1 ≠ 0 by positivity)
  have hb := mul_lt_mul_of_pos_left (show L < L + 1 by linarith) hη
  linarith only [he, hb]

/-- Finite-grid energy bound for a nonnegative bounded correction, retaining
the continuous-variation remainder and the predictable martingale sum. -/
theorem stopped_energy_grid_le (D O M : ℕ → ℝ) (hD : D 0 = 0) (hO0 : O 0 = 0) (hM0 : M 0 = 0)
    (hO : Monotone O) (hM : Monotone M) {B : ℝ} (N : ℕ)
    (hw : ∀ k ≤ N, 0 ≤ D k - (O k - M k) ∧ D k - (O k - M k) ≤ B) :
    D N ^ 2 ≤ 2 * B * O N + B ^ 2 +
      (∑ k ∈ Finset.range N, ((O (k + 1) - M (k + 1)) - (O k - M k)) ^ 2) +
      2 * (∑ k ∈ Finset.range N, (O k - M k) * (D (k + 1) - D k)) := by
  have he := stopped_energy_grid_identity D (fun k => O k - M k) hD (by simp [hO0, hM0]) N
  have hs : (∑ k ∈ Finset.range N, (D (k + 1) - (O (k + 1) - M (k + 1))) *
      ((O (k + 1) - M (k + 1)) - (O k - M k))) ≤ B * O N := by
    calc
      _ ≤ ∑ k ∈ Finset.range N, B * (O (k + 1) - O k) := by
        apply Finset.sum_le_sum
        intro k hk
        have hwk := hw (k + 1) (by have := Finset.mem_range.mp hk; omega)
        have ho := sub_nonneg.mpr (hO (Nat.le_succ k))
        have hm := sub_nonneg.mpr (hM (Nat.le_succ k))
        nlinarith [mul_nonneg hwk.1 hm,
          mul_nonneg (sub_nonneg.mpr hwk.2) ho]
      _ = _ := by
        rw [← Finset.mul_sum, Finset.sum_range_sub, hO0, sub_zero]
  have hwN := hw N le_rfl
  have hsq : (D N - (O N - M N)) ^ 2 ≤ B ^ 2 := by nlinarith
  linarith only [he, hs, hsq]

/-- A bounded nonnegative correction to the difference of two continuous increasing
processes controls the terminal martingale energy. The proof takes expectations on finite
meshes and then removes the squared-increment remainder by dominated convergence. -/
theorem integral_sq_le_of_martingale_nonneg_correction {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    {D O M : ℝ≥0 → Ω → ℝ} (hD : Martingale D ℱ μ)
    (hO : StronglyAdapted ℱ O) (hM : StronglyAdapted ℱ M) (T : ℝ≥0)
    {K L B : ℝ} (hK : 0 ≤ K) (hL : 0 ≤ L)
    (hDi : Integrable (fun ω => D T ω ^ 2) μ)
    (hpaths : ∀ᵐ ω ∂μ, O 0 ω = 0 ∧ M 0 ω = 0 ∧ D 0 ω = 0 ∧
      Monotone (fun s => O s ω) ∧ Monotone (fun s => M s ω) ∧
      Continuous (fun s => O s ω - M s ω) ∧ O T ω ≤ K ∧ M T ω ≤ L ∧
      ∀ s ≤ T, 0 ≤ D s ω - (O s ω - M s ω) ∧ D s ω - (O s ω - M s ω) ≤ B) :
    ∫ ω, D T ω ^ 2 ∂μ ≤ 2 * B * (∫ ω, O T ω ∂μ) + B ^ 2 := by
  let C : ℝ≥0 → Ω → ℝ := fun s ω => O s ω - M s ω
  let Q : ℕ → Ω → ℝ := fun N ω => ∑ k ∈ Finset.range (N + 1),
    (C (stoppedEnergyGrid T N (k + 1)) ω - C (stoppedEnergyGrid T N k) ω) ^ 2
  let R : ℕ → Ω → ℝ := fun N ω => ∑ k ∈ Finset.range (N + 1),
    C (stoppedEnergyGrid T N k) ω *
      (D (stoppedEnergyGrid T N (k + 1)) ω - D (stoppedEnergyGrid T N k) ω)
  have hC : StronglyAdapted ℱ C := hO.sub hM
  have hCm (s : ℝ≥0) : StronglyMeasurable (C s) := (hC s).mono (ℱ.le s)
  have hgle (N k : ℕ) (hk : k ≤ N + 1) : stoppedEnergyGrid T N k ≤ T :=
    (stoppedEnergyGrid_mono T N hk).trans_eq (stoppedEnergyGrid_last T N)
  have hb : ∀ᵐ ω ∂μ, ∀ s ≤ T, |C s ω| ≤ K + L := by
    filter_upwards [hpaths] with ω hω
    rcases hω with ⟨hO0, hM0, _, ho, hm, _, hOK, hML, _⟩
    intro s hs
    have ho0 : 0 ≤ O s ω := hO0 ▸ ho (zero_le : 0 ≤ s)
    have hm0 : 0 ≤ M s ω := hM0 ▸ hm (zero_le : 0 ≤ s)
    have hos := (ho hs).trans hOK
    have hms := (hm hs).trans hML
    exact (abs_sub _ _).trans (by
      rw [abs_of_nonneg ho0, abs_of_nonneg hm0]
      linarith only [hos, hms])
  have hOi : Integrable (O T) μ := by
    apply Integrable.of_bound ((hO T).mono (ℱ.le T)).aestronglyMeasurable K
    filter_upwards [hpaths] with ω hω
    rcases hω with ⟨hO0, _, _, ho, _, _, hOK, _⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (hO0 ▸ ho (zero_le : 0 ≤ T))]
    exact hOK
  have hQm (N : ℕ) : AEStronglyMeasurable (Q N) μ := by
    simpa only [Q, Finset.sum_apply, Pi.pow_apply, Pi.sub_apply] using
      (Finset.stronglyMeasurable_fun_sum (Finset.range (N + 1)) (fun k _ =>
        ((hCm (stoppedEnergyGrid T N (k + 1))).sub
          (hCm (stoppedEnergyGrid T N k))).pow 2)).aestronglyMeasurable (μ := μ)
  have hQb (N : ℕ) : ∀ᵐ ω ∂μ, ‖Q N ω‖ ≤ (K + L) ^ 2 := by
    filter_upwards [hpaths] with ω hω
    rcases hω with ⟨hO0, hM0, _, ho, hm, _, hOK, hML, _⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun _ _ => sq_nonneg _))]
    have hh := mesh_sum_le (fun s => O s ω) (fun s => M s ω) ho hm T N
      (add_nonneg hK hL) (fun k hk => ?_)
    · simp only [hO0, hM0, sub_zero] at hh
      apply hh.trans
      calc
        (K + L) * (O T ω + M T ω) ≤ (K + L) * (K + L) :=
          mul_le_mul_of_nonneg_left (by linarith only [hOK, hML]) (add_nonneg hK hL)
        _ = _ := (pow_two _).symm
    · have ht := hgle N (k + 1) (by omega)
      have hst := stoppedEnergyGrid_mono T N (Nat.le_succ k)
      have ho0 := ho (show 0 ≤ stoppedEnergyGrid T N k from zero_le)
      have hm0 := hm (show 0 ≤ stoppedEnergyGrid T N k from zero_le)
      have hod := ho hst
      have hmd := hm hst
      have hot := ho ht
      have hmt := hm ht
      dsimp only at ho0 hm0 hod hmd hot hmt
      rw [hO0] at ho0
      rw [hM0] at hm0
      apply abs_le.mpr
      constructor <;> linarith
  have hQi (N : ℕ) : Integrable (Q N) μ := Integrable.of_bound (hQm N) _ (hQb N)
  have hQlim : Tendsto (fun N => ∫ ω, Q N ω ∂μ) atTop (𝓝 0) := by
    have hh := tendsto_integral_of_dominated_convergence (μ := μ)
      (F := Q) (f := fun _ => (0 : ℝ)) (fun _ => (K + L) ^ 2) hQm
      (integrable_const _) hQb ?_
    · simpa only [integral_zero] using hh
    · filter_upwards [hpaths] with ω hω
      exact tendsto_stoppedEnergyGrid_sq_increments _ _ hω.2.2.2.1 hω.2.2.2.2.1
        hω.2.2.2.2.2.1 T
  have hRi (N k : ℕ) (hk : k < N + 1) : Integrable (fun ω =>
      C (stoppedEnergyGrid T N k) ω *
        (D (stoppedEnergyGrid T N (k + 1)) ω - D (stoppedEnergyGrid T N k) ω)) μ := by
    apply ((hD.integrable _).sub (hD.integrable _)).bdd_mul (hCm _).aestronglyMeasurable
    exact hb.mono fun ω hω => by
      rw [Real.norm_eq_abs]
      exact hω _ (hgle N k (by omega))
  have hRint (N : ℕ) : Integrable (R N) μ :=
    integrable_finsetSum _ (fun k hk => hRi N k (Finset.mem_range.mp hk))
  have hRzero (N : ℕ) : ∫ ω, R N ω ∂μ = 0 := by
    rw [show R N = fun ω => ∑ k ∈ Finset.range (N + 1),
      C (stoppedEnergyGrid T N k) ω *
        (D (stoppedEnergyGrid T N (k + 1)) ω - D (stoppedEnergyGrid T N k) ω) from rfl,
      integral_finsetSum _ (fun k hk => hRi N k (Finset.mem_range.mp hk))]
    apply Finset.sum_eq_zero
    intro k hk
    exact integral_mul_martingale_increment_eq_zero hD
      (stoppedEnergyGrid_mono T N (Nat.le_succ k)) (hC _) (hRi N k (Finset.mem_range.mp hk))
  have hineq (N : ℕ) : ∫ ω, D T ω ^ 2 ∂μ ≤
      2 * B * (∫ ω, O T ω ∂μ) + B ^ 2 + ∫ ω, Q N ω ∂μ := by
    have hi := integral_mono_ae hDi
      ((((hOi.const_mul (2 * B)).add (integrable_const (B ^ 2))).add (hQi N)).add
        ((hRint N).const_mul 2)) ?_
    · rw [integral_add' (((hOi.const_mul (2 * B)).add (integrable_const (B ^ 2))).add
          (hQi N)) ((hRint N).const_mul 2),
        integral_add' ((hOi.const_mul (2 * B)).add (integrable_const (B ^ 2))) (hQi N),
        integral_add' (hOi.const_mul (2 * B)) (integrable_const (B ^ 2)),
        integral_const_mul, integral_const_mul, hRzero, integral_const] at hi
      simpa only [probReal_univ, one_smul, mul_zero, add_zero] using hi
    · filter_upwards [hpaths] with ω hω
      rcases hω with ⟨hO0, hM0, hD0, ho, hm, _, _, _, hw⟩
      have hh := stopped_energy_grid_le
        (fun k => D (stoppedEnergyGrid T N k) ω)
        (fun k => O (stoppedEnergyGrid T N k) ω)
        (fun k => M (stoppedEnergyGrid T N k) ω)
        (by simpa only [stoppedEnergyGrid_zero] using hD0)
        (by simpa only [stoppedEnergyGrid_zero] using hO0)
        (by simpa only [stoppedEnergyGrid_zero] using hM0)
        (ho.comp (stoppedEnergyGrid_mono T N)) (hm.comp (stoppedEnergyGrid_mono T N))
        (N + 1) (fun k hk => hw _ (hgle N k hk))
      simpa only [Pi.add_apply, stoppedEnergyGrid_last, Q, R, C] using hh
  have hh := le_of_tendsto_of_tendsto tendsto_const_nhds
    (hQlim.const_add (2 * B * (∫ ω, O T ω ∂μ) + B ^ 2))
    (Eventually.of_forall hineq)
  simpa only [add_zero] using hh

end BGW.StableTrees
