/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.VervaatRotate
public import BGW.Skorokhod.VervaatWindow

/-!
# Rotating an aligned time change

Two clipped coordinates give a continuous formula for circular rotation of an
aligned time change. One coordinate is always an endpoint, so the two pieces
match at the circular cut.
-/

@[expose] public section

open Set

namespace BGW.Skorokhod

/-- An aligned time change rotates to a time change of the transformed paths. -/
theorem exists_rotated_timeChange (ρ : TimeChange 1) (g a : Icc (0 : ℝ) 1)
    (halign : ρ g = a) {d : ℝ} (hd : ∀ t, |(ρ t : ℝ) - t| ≤ d) :
    ∃ μ : TimeChange 1,
      (∀ t : Icc (0 : ℝ) 1, (μ t : ℝ) =
        if (g : ℝ) + t ≤ 1 then
          (ρ (projIcc 0 1 zero_le_one ((g : ℝ) + t)) : ℝ) - a
        else (ρ (projIcc 0 1 zero_le_one ((g : ℝ) + t - 1)) : ℝ) + 1 - a) ∧
      ∀ t, |(μ t : ℝ) - t| ≤ 2 * d + |(a : ℝ) - g| := by
  let A : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
    fun t => projIcc 0 1 zero_le_one ((g : ℝ) + t)
  let B : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
    fun t => projIcc 0 1 zero_le_one ((g : ℝ) + t - 1)
  have hA (t : Icc (0 : ℝ) 1) : (A t : ℝ) = min 1 ((g : ℝ) + t) := by
    dsimp [A, projIcc]
    exact max_eq_right (le_min zero_le_one (add_nonneg g.2.1 t.2.1))
  have hB (t : Icc (0 : ℝ) 1) : (B t : ℝ) = max 0 ((g : ℝ) + t - 1) := by
    dsimp [B, projIcc]
    rw [min_eq_right (by linarith [g.2.2, t.2.2])]
  have hsum (t : Icc (0 : ℝ) 1) : (A t : ℝ) + B t = (g : ℝ) + t := by
    rw [hA, hB]
    rcases le_total ((g : ℝ) + t) 1 with ht | ht
    · rw [min_eq_right ht, max_eq_left (by linarith)]
      ring
    · rw [min_eq_left ht, max_eq_right (by linarith)]
      ring
  have hAm : Monotone A := by
    intro s t hst
    change (A s : ℝ) ≤ A t
    rw [hA, hA]
    change (s : ℝ) ≤ t at hst
    exact min_le_min_left _ (by linarith)
  have hBm : Monotone B := by
    intro s t hst
    change (B s : ℝ) ≤ B t
    rw [hB, hB]
    exact max_le_max_left _ (by change (s : ℝ) ≤ t at hst; linarith)
  let F : Icc (0 : ℝ) 1 → ℝ := fun t => (ρ (A t) : ℝ) + ρ (B t) - a
  have hstrict : StrictMono F := by
    intro s t hst
    have ha := hAm hst.le
    have hb := hBm hst.le
    by_cases halt : A s < A t
    · have har : (ρ (A s) : ℝ) < ρ (A t) := ρ.strictMono halt
      have hbr : (ρ (B s) : ℝ) ≤ ρ (B t) := ρ.monotone hb
      dsimp [F]
      linarith
    · have hae : A s = A t := le_antisymm ha (le_of_not_gt halt)
      have hblt : B s < B t := by
        have hs := hsum s
        have ht := hsum t
        rw [hae] at hs
        change (s : ℝ) < t at hst
        change (B s : ℝ) < B t
        linarith
      have hbr : (ρ (B s) : ℝ) < ρ (B t) := ρ.strictMono hblt
      dsimp [F]
      rw [hae]
      linarith
  have hcA : Continuous A := continuous_projIcc.comp
    (continuous_const.add continuous_subtype_val)
  have hcB : Continuous B := continuous_projIcc.comp
    ((continuous_const.add continuous_subtype_val).sub continuous_const)
  have hcF : Continuous F :=
    ((continuous_subtype_val.comp (ρ.continuous.comp hcA)).add
      (continuous_subtype_val.comp (ρ.continuous.comp hcB))).sub continuous_const
  have hzero : F ⟨0, le_rfl, zero_le_one⟩ = 0 := by
    have ha0 : A ⟨0, le_rfl, zero_le_one⟩ = g := by simp [A, projIcc_val]
    have hb0 : B ⟨0, le_rfl, zero_le_one⟩ = ⟨0, le_rfl, zero_le_one⟩ :=
      projIcc_of_le_left zero_le_one (by linarith [g.2.2])
    simp [F, ha0, hb0, halign, TimeChange.apply_zero ρ zero_le_one]
  have hone : F ⟨1, zero_le_one, le_rfl⟩ = 1 := by
    have ha1 : A ⟨1, zero_le_one, le_rfl⟩ = ⟨1, zero_le_one, le_rfl⟩ :=
      projIcc_of_right_le zero_le_one (by linarith [g.2.1])
    have hb1 : B ⟨1, zero_le_one, le_rfl⟩ = g := by simp [B, projIcc_val]
    simp [F, ha1, hb1, halign, TimeChange.apply_top ρ zero_le_one]
  let φ : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 := fun t =>
    ⟨F t, by
      constructor
      · simpa only [hzero] using hstrict.monotone
          (show (⟨0, le_rfl, zero_le_one⟩ : Icc (0 : ℝ) 1) ≤ t from t.2.1)
      · simpa only [hone] using hstrict.monotone
          (show t ≤ (⟨1, zero_le_one, le_rfl⟩ : Icc (0 : ℝ) 1) from t.2.2)⟩
  have hsurj : Function.Surjective φ := by
    intro y
    let : PreconnectedSpace (Icc (0 : ℝ) 1) :=
      isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
    have hy : (y : ℝ) ∈ Icc (F ⟨0, le_rfl, zero_le_one⟩)
        (F ⟨1, zero_le_one, le_rfl⟩) := by rw [hzero, hone]; exact y.2
    obtain ⟨t, ht⟩ := intermediate_value_univ
      (f := F) (show Icc (0 : ℝ) 1 from ⟨0, le_rfl, zero_le_one⟩)
      (show Icc (0 : ℝ) 1 from ⟨1, zero_le_one, le_rfl⟩) hcF hy
    exact ⟨t, Subtype.ext ht⟩
  let μ : TimeChange 1 := StrictMono.orderIsoOfSurjective φ hstrict hsurj
  refine ⟨μ, ?_, ?_⟩
  · intro t
    change F t = _
    split_ifs with ht
    · have hb0 : B t = ⟨0, le_rfl, zero_le_one⟩ :=
        projIcc_of_le_left zero_le_one (by linarith)
      simp only [F, hb0, TimeChange.apply_zero ρ zero_le_one, add_zero, Subtype.coe_mk]
      rfl
    · have ha1 : A t = ⟨1, zero_le_one, le_rfl⟩ :=
        projIcc_of_right_le zero_le_one (le_of_not_ge ht)
      simp only [F, ha1, TimeChange.apply_top ρ zero_le_one, Subtype.coe_mk]
      ring
  · intro t
    change |F t - t| ≤ _
    have heq : F t - t = ((ρ (A t) : ℝ) - A t) +
        ((ρ (B t) : ℝ) - B t) + ((g : ℝ) - a) := by
      have hs := hsum t
      dsimp [F]
      linarith
    rw [heq]
    calc
      |((ρ (A t) : ℝ) - A t) + ((ρ (B t) : ℝ) - B t) + ((g : ℝ) - a)| ≤
          |(ρ (A t) : ℝ) - A t| + |(ρ (B t) : ℝ) - B t| + |(g : ℝ) - a| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ 2 * d + |(a : ℝ) - g| := by rw [abs_sub_comm (g : ℝ)]; linarith [hd (A t), hd (B t)]

end BGW.Skorokhod
