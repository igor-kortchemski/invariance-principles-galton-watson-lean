/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionDefs
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Algebra.Order.Group.MinMax

/-!
# Local clock corrections for stopped extraction

Local perturbations align moving excursion starts while preserving J1 approximation away
from a small continuity window. The horizon is arbitrary.
-/

@[expose] public section

open Set
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Move `g` to `a` by a time change supported in the radius `η` window around `g`.
The displacement is at most the distance between the two times.
Reference: Billingsley (1999), Chapter 3. -/
private theorem exists_extraction_local_timeChange {M : ℝ} (hM : 0 ≤ M)
    (g a : Icc (0 : ℝ) M) {η : ℝ} (hη : 0 < η)
    (hleft : η ≤ (g : ℝ)) (hright : (g : ℝ) + η ≤ M)
    (hnear : |(a : ℝ) - g| < η) :
    ∃ κ : TimeChange M, κ g = a ∧
      (∀ t : Icc (0 : ℝ) M, η ≤ |(t : ℝ) - g| → κ t = t) ∧
      ∀ t : Icc (0 : ℝ) M, |(κ t : ℝ) - t| ≤ |(a : ℝ) - g| := by
  let w : ℝ → ℝ := fun t => max (η - |t - g|) 0
  let k : ℝ := ((a : ℝ) - g) / η
  let F : ℝ → ℝ := fun t => t + k * w t
  have hw (t : ℝ) : 0 ≤ w t ∧ w t ≤ η :=
    ⟨le_max_right _ _, max_le (by linarith [abs_nonneg (t - g)]) hη.le⟩
  have hwlip (s t : ℝ) : |w s - w t| ≤ |s - t| := by
    calc
      |w s - w t| ≤ |(η - |s - g|) - (η - |t - g|)| :=
        abs_max_sub_max_le_abs _ _ 0
      _ = abs (|s - g| - |t - g|) := by
        rw [show (η - |s - g|) - (η - |t - g|) = -(|s - g| - |t - g|) by ring,
          abs_neg]
      _ ≤ |(s - g) - (t - g)| := abs_abs_sub_abs_le _ _
      _ = |s - t| := by congr 1; ring
  have hk : |k| < 1 := by
    dsimp [k]
    rw [abs_div, abs_of_pos hη]
    exact (div_lt_one hη).mpr hnear
  have hstrict : StrictMono F := by
    intro s t hst
    have hab : |k * (w t - w s)| ≤ |k| * (t - s) := by
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_left (hwlip t s) (abs_nonneg k)).trans_eq
        (by rw [abs_of_pos (sub_pos.mpr hst)])
    have hbound := (abs_le.mp hab).1
    have hpos := mul_pos (sub_pos.mpr hk) (sub_pos.mpr hst)
    dsimp [F]
    nlinarith
  have hcont : Continuous F := continuous_id.add
    (continuous_const.mul (((continuous_const.sub
      (continuous_id.sub continuous_const).abs).max continuous_const)))
  have hout (t : ℝ) (ht : η ≤ |t - g|) : F t = t := by
    simp [F, w, max_eq_right (sub_nonpos.mpr ht)]
  have hzero : F 0 = 0 := hout 0 (by simpa [abs_of_nonneg g.2.1] using hleft)
  have hone : F M = M := hout M (by rw [abs_of_nonneg (sub_nonneg.mpr g.2.2)]; linarith)
  have hfg : F g = a := by
    dsimp [F, w, k]
    rw [sub_self, abs_zero, sub_zero, max_eq_left hη.le, div_mul_cancel₀ _ hη.ne']
    ring
  let φ : Icc (0 : ℝ) M → Icc (0 : ℝ) M := fun t =>
    ⟨F t, by
      constructor
      · simpa only [hzero] using hstrict.monotone t.2.1
      · simpa only [hone] using hstrict.monotone t.2.2⟩
  have hsurj : Function.Surjective φ := by
    intro y
    have hy : (y : ℝ) ∈ Icc (F 0) (F M) := by rw [hzero, hone]; exact y.2
    obtain ⟨t, ht, hFt⟩ := intermediate_value_Icc hM hcont.continuousOn hy
    exact ⟨⟨t, ht⟩, Subtype.ext hFt⟩
  let κ : TimeChange M := StrictMono.orderIsoOfSurjective φ
    (fun s t hst => hstrict hst) hsurj
  refine ⟨κ, Subtype.ext hfg, fun t ht => Subtype.ext (hout t ht), ?_⟩
  intro t
  change |F t - t| ≤ |(a : ℝ) - g|
  calc
    |F t - t| = |k| * w t := by dsimp [F]; rw [add_sub_cancel_left, abs_mul,
      abs_of_nonneg (hw t).1]
    _ ≤ |k| * η := mul_le_mul_of_nonneg_left (hw t).2 (abs_nonneg _)
    _ = |(a : ℝ) - g| := by
      dsimp [k]
      rw [abs_div, abs_of_pos hη, div_mul_cancel₀ _ hη.ne']

/-- Align one time by a local correction, paying only the oscillation in its window.
Reference: Billingsley (1999), Chapter 3. -/
private theorem exists_extraction_aligned_timeChange {M : ℝ} (hM : 0 ≤ M) (u f : D M ℝ)
    (σ : TimeChange M) (g a : Icc (0 : ℝ) M) {η d e : ℝ} (hη : 0 < η)
    (hleft : η ≤ (g : ℝ)) (hright : (g : ℝ) + η ≤ M)
    (hnear : dist (σ.symm a) g < η)
    (hd : ∀ t, |(σ t : ℝ) - t| ≤ d)
    (hp : ∀ t, dist (u (σ t)) (f t) ≤ e)
    (hf : ∀ s, dist s g < 2 * η → dist (f s) (f g) ≤ e) :
    ∃ ρ : TimeChange M, ρ g = a ∧
      (∀ t, |(ρ t : ℝ) - t| ≤ d + η) ∧
      ∀ t, dist (u (ρ t)) (f t) ≤ 3 * e := by
  obtain ⟨κ, hκg, hκout, hκmove⟩ := exists_extraction_local_timeChange hM g (σ.symm a)
    hη hleft hright (by simpa only [Subtype.dist_eq, Real.dist_eq] using hnear)
  let ρ := κ.trans σ
  have he : 0 ≤ e := dist_nonneg.trans (hp g)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · change σ (κ g) = a
    rw [hκg, OrderIso.apply_symm_apply]
  · intro t
    change |(σ (κ t) : ℝ) - t| ≤ _
    calc
      |(σ (κ t) : ℝ) - t| ≤ |(σ (κ t) : ℝ) - κ t| + |(κ t : ℝ) - t| :=
        abs_sub_le _ _ _
      _ ≤ d + η := add_le_add (hd (κ t)) ((hκmove t).trans
        (by simpa only [Subtype.dist_eq, Real.dist_eq] using hnear.le))
  · intro t
    change dist (u (σ (κ t))) (f t) ≤ _
    by_cases ht : η ≤ |(t : ℝ) - g|
    · rw [hκout t ht]
      exact (hp t).trans (by linarith)
    · have htg : dist t g < η := by
        simpa only [Subtype.dist_eq, Real.dist_eq] using lt_of_not_ge ht
      have hκt : dist (κ t) t < η := by
        exact (show dist (κ t) t ≤ dist (σ.symm a) g from
          hκmove t).trans_lt hnear
      have hκg' : dist (κ t) g < 2 * η :=
        (dist_triangle (κ t) t g).trans_lt (by linarith)
      calc
        dist (u (σ (κ t))) (f t) ≤ dist (u (σ (κ t))) (f (κ t)) +
            dist (f (κ t)) (f g) + dist (f g) (f t) := dist_triangle4 _ _ _ _
        _ ≤ 3 * e := by
          have h1 := hp (κ t)
          have h2 := hf (κ t) hκg'
          have h3 := hf t (htg.trans (by linarith))
          rw [dist_comm (f t)] at h3
          linarith

end BGW.StableTrees
