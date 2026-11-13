/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.HeightTightnessBasic
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import BGW.StableTrees.HeightTightnessGridLaw
import BGW.StableTrees.HeightTightnessGridEnclosure

/-!
# Height modulus and vanishing adjacent jumps

The regenerated count and short-gap bounds control every short upward variation.
K09 on a deterministic grid and H03 continuity control the grid endpoint values.
An enclosing-grid argument bounds the full interpolated modulus. Monotonicity
in the time scale gives the two-limit statement. Adjacent jumps use the modulus
on the longer horizon `T + 1`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical
open BGW.StableTrees.DiscreteForest BGW.StableTrees.DiscreteHeightApprox
namespace BGW.StableTrees.HeightTightness

/-- The forest-height modulus is eventually small on a sufficiently fine fixed time scale. -/
theorem exists_pos_eventually_forestHeight_modulus_small {μ : PMF ℕ} {θ : ℝ}
    {B : ℕ → ℝ} (h : StableDomain μ θ B) {T η ε : ℝ}
    (hT : 0 < T) (hη : 0 < η) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n : ℕ in atTop, (offspringSeqLaw μ).toMeasure.real
      {ω | η < heightOscillation B n T δ ω} ≤ ε := by
  let R : ℝ≥0 := ⟨T + 1, by positivity⟩
  have hR : 0 < R := by change 0 < T + 1; positivity
  let η₀ := η / 16
  have hη₀ : 0 < η₀ := by dsimp [η₀]; positivity
  obtain ⟨x, hx, hshort⟩ := exists_pos_eventually_short_rise_probability_small h hη₀
    (T := (R : ℝ)) R.coe_nonneg (show 0 < ε / 2 by positivity)
  let N₀ := ⌈4 * (R : ℝ) / x⌉₊ + ⌈4 * (R : ℝ)⌉₊ + 1
  obtain ⟨N, hN₀, hN, hgrid⟩ := exists_eventually_height_grid_probability_small h hR hη₀
    (show 0 < ε / 2 by positivity) N₀
  have hnR : (0 : ℝ) < N := by exact_mod_cast hN
  let δ := (R : ℝ) / N
  have hδ : 0 < δ := div_pos (by exact_mod_cast hR) hnR
  have hN₁ : ⌈4 * (R : ℝ) / x⌉₊ ≤ N := by dsimp [N₀] at hN₀; omega
  have hN₂ : ⌈4 * (R : ℝ)⌉₊ ≤ N := by dsimp [N₀] at hN₀; omega
  have hδx : 4 * δ ≤ x := by
    have hh := (div_le_iff₀ hx).mp
      ((Nat.le_ceil (4 * (R : ℝ) / x)).trans (Nat.cast_le.mpr hN₁))
    dsimp [δ]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hnR).mpr
    nlinarith
  have hδ1 : δ ≤ 1 / 4 := by
    have hh := (Nat.le_ceil (4 * (R : ℝ))).trans (Nat.cast_le.mpr hN₂)
    dsimp [δ]
    apply (div_le_iff₀ hnR).mpr
    linarith
  have hcover : T + 1 ≤ (N : ℝ) * δ := by
    have he : (N : ℝ) * δ = (R : ℝ) := by dsimp [δ]; field_simp
    rw [he]
    exact le_rfl
  refine ⟨δ, hδ, ?_⟩
  filter_upwards [hshort, hgrid, eventually_ge_atTop 1,
    eventually_ge_atTop ⌈1 / δ⌉₊] with n hnS hnG hn hnδ
  have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnPos : (0 : ℝ) < n := by exact_mod_cast hn
  have hnδ1 : 1 ≤ (n : ℝ) * δ := (div_le_iff₀ hδ).mp
    ((Nat.le_ceil (1 / δ)).trans (Nat.cast_le.mpr hnδ))
  let c := B n / (n : ℝ)
  let q := ⌊η₀ * (n : ℝ) / B n⌋₊
  have hB : 0 < B n := h.pos n hn
  have hc : 0 ≤ c := div_nonneg hB.le hn0
  have hcq : c * (q : ℝ) ≤ η₀ := by
    have hf := Nat.floor_le (by positivity : 0 ≤ η₀ * (n : ℝ) / B n)
    have hh := mul_le_mul_of_nonneg_left hf hc
    have he : c * (η₀ * (n : ℝ) / B n) = η₀ := by
      dsimp [c]
      field_simp [hB.ne', hnPos.ne']
    rw [he] at hh
    exact hh
  let S : Set (ℕ → ℕ) := {ω | ∃ i j : ℕ,
    i ≤ j ∧ j ≤ ⌊(n : ℝ) * (R : ℝ)⌋₊ ∧ j - i ≤ ⌊(n : ℝ) * x⌋₊ ∧
      forestHeight ω i + 2 * q < forestHeight ω j}
  let G : Set (ℕ → ℕ) := {ω | ∃ i : Fin N, η₀ ≤
    |scaledHeight B n ω (heightGridTime R N i.castSucc) -
      scaledHeight B n ω (heightGridTime R N i.succ)|}
  have hsub : {ω | η < heightOscillation B n T δ ω} ⊆ S ∪ G := by
    intro ω hω
    by_cases hS : ω ∈ S
    · exact Or.inl hS
    by_cases hG : ω ∈ G
    · exact Or.inr hG
    have hgoodGrid (j : ℕ) (hj : j < N) :
        |c * forestHeight ω ⌊(n : ℝ) * ((j : ℝ) * δ)⌋₊ -
          c * forestHeight ω ⌊(n : ℝ) * (((j + 1 : ℕ) : ℝ) * δ)⌋₊| ≤ η₀ := by
      let i : Fin N := ⟨j, hj⟩
      have hh : ¬ η₀ ≤ |scaledHeight B n ω (heightGridTime R N i.castSucc) -
          scaledHeight B n ω (heightGridTime R N i.succ)| := fun hh => hG ⟨i, hh⟩
      have he₀ : (heightGridTime R N i.castSucc : ℝ) = (j : ℝ) * δ := by
        change (R : ℝ) * j / N = j * ((R : ℝ) / N)
        ring
      have he₁ : (heightGridTime R N i.succ : ℝ) = ((j + 1 : ℕ) : ℝ) * δ := by
        change (R : ℝ) * (j + 1 : ℕ) / N = ((j + 1 : ℕ) : ℝ) * ((R : ℝ) / N)
        ring
      change ¬ η₀ ≤ |c * forestHeight ω ⌊(n : ℝ) * (heightGridTime R N i.castSucc : ℝ)⌋₊ -
        c * forestHeight ω ⌊(n : ℝ) * (heightGridTime R N i.succ : ℝ)⌋₊| at hh
      rw [he₀, he₁] at hh
      exact (lt_of_not_ge hh).le
    have hgoodRise (i j : ℕ) (hij : i ≤ j)
        (hj : j ≤ ⌊(n : ℝ) * ((N : ℝ) * δ)⌋₊)
        (hd : j - i ≤ ⌊(n : ℝ) * (4 * δ)⌋₊) :
        forestHeight ω j ≤ forestHeight ω i + 2 * q := by
      have he : (N : ℝ) * δ = (R : ℝ) := by dsimp [δ]; field_simp
      rw [he] at hj
      have hd' := hd.trans (Nat.floor_mono (mul_le_mul_of_nonneg_left hδx hn0))
      by_contra hh
      exact hS ⟨i, j, hij, hj, hd', by omega⟩
    have hpoint (s t : Set.Icc (0 : ℝ) T) (hd : |(s : ℝ) - t| ≤ δ) :
        |c * forestHeightLin ω ((n : ℝ) * s) -
          c * forestHeightLin ω ((n : ℝ) * t)| ≤ η := by
      have hbound : |c * forestHeightLin ω ((n : ℝ) * s) -
          c * forestHeightLin ω ((n : ℝ) * t)| ≤ 3 * η₀ + 4 * c * q := by
        rcases le_total (s : ℝ) (t : ℝ) with hst | hts
        · apply forestHeightLin_short_oscillation_of_grid hc hδ hδ1 hnδ1 hcover
            hgoodGrid hgoodRise s.property t.property hst
          rw [abs_of_nonpos (sub_nonpos.mpr hst)] at hd
          linarith
        · rw [abs_sub_comm]
          apply forestHeightLin_short_oscillation_of_grid hc hδ hδ1 hnδ1 hcover
            hgoodGrid hgoodRise t.property s.property hts
          rw [abs_of_nonneg (sub_nonneg.mpr hts)] at hd
          exact hd
      dsimp [η₀] at hbound hcq
      linarith
    have hb := heightOscillation_le B n hT.le hη.le ω hpoint
    exact False.elim ((not_lt_of_ge hb) hω)
  exact (measureReal_mono hsub).trans ((measureReal_union_le S G).trans (by linarith))

/-- **Height modulus** (DLG Theorem 2.3.1 route). -/
theorem forestHeight_modulus {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    {T η : ℝ} (hT : 0 < T) (hη : 0 < η) :
    Tendsto (fun δ : ℝ => limsup (fun n : ℕ =>
        ((offspringSeqLaw μ : Measure (ℕ → ℕ))).real {ω | η < heightOscillation B n T δ ω})
        atTop) (𝓝[>] 0) (𝓝 0) := by
  let F (δ : ℝ) (n : ℕ) := (offspringSeqLaw μ).toMeasure.real
    {ω | η < heightOscillation B n T δ ω}
  have hbounded (δ : ℝ) : IsBoundedUnder (· ≤ ·) atTop (F δ) := by
    refine ⟨1, ?_⟩
    change ∀ᶠ n : ℕ in atTop, F δ n ≤ (1 : ℝ)
    exact Eventually.of_forall fun _ => measureReal_le_one
  have hnonneg (δ : ℝ) : 0 ≤ limsup (F δ) atTop :=
    le_limsup_of_frequently_le
      (Eventually.of_forall fun _ => measureReal_nonneg).frequently (hbounded δ)
  change Tendsto (fun δ => limsup (F δ) atTop) (𝓝[>] 0) (𝓝 0)
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun δ => ha.trans_le (hnonneg δ)
  · intro b hb
    obtain ⟨δ₀, hδ₀, hsmall⟩ := exists_pos_eventually_forestHeight_modulus_small h hT hη
      (show 0 < b / 2 by positivity)
    have hm : Iio δ₀ ∈ 𝓝[>] (0 : ℝ) := mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hδ₀)
    filter_upwards [hm] with δ hδ
    have hbound : limsup (F δ) atTop ≤ b / 2 := by
      apply limsup_le_of_le (Filter.isCoboundedUnder_le_of_le atTop fun _ => measureReal_nonneg)
      filter_upwards [hsmall] with n hn
      apply le_trans (measureReal_mono ?_) hn
      intro ω hω
      exact hω.trans_le (heightOscillation_mono B n hT.le hδ₀.le hδ.le ω)
    linarith

/-- The largest adjacent height jump vanishes in probability on the height scale. -/
theorem maxHeightJump_tendstoInMeasure {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {T : ℝ} (hT : 0 < T) :
    TendstoInMeasure (offspringSeqLaw μ : Measure (ℕ → ℕ))
      (fun n ω => maxHeightJump B n T ω) atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_iff_measureReal_norm.mpr
  intro η hη
  apply tendsto_order.mpr
  constructor
  · intro a ha
    exact Eventually.of_forall fun _ => ha.trans_le measureReal_nonneg
  · intro b hb
    obtain ⟨δ, hδ, hsmall⟩ := exists_pos_eventually_forestHeight_modulus_small h
      (show 0 < T + 1 by positivity) (show 0 < η / 2 by positivity)
      (show 0 < b / 2 by positivity)
    have hinv : Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    filter_upwards [hsmall, hinv.eventually (gt_mem_nhds hδ), eventually_ge_atTop 1]
      with n hn hnδ hn1
    have hB := h.pos n hn1
    have hle : (offspringSeqLaw μ).toMeasure.real
        {ω | η ≤ ‖maxHeightJump B n T ω - 0‖} ≤ b / 2 := by
      apply le_trans (measureReal_mono ?_) hn
      intro ω hω
      have hnonneg : 0 ≤ maxHeightJump B n T ω := by unfold maxHeightJump; positivity
      simp only [mem_ofPred_eq, sub_zero, Real.norm_eq_abs, abs_of_nonneg hnonneg] at hω ⊢
      have hj := (maxHeightJump_le_heightOscillation B hn1 hT.le hB.le ω).trans
        (heightOscillation_mono B n (by positivity : 0 ≤ T + 1) hδ.le hnδ.le ω)
      linarith
    exact hle.trans_lt (by linarith)

end BGW.StableTrees.HeightTightness
