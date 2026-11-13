/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Vervaat

/-!
# Rotation of càdlàg paths

The correction at the wrap point matches the terminal value to the initial
right limit. In particular, a terminal jump is retained at the wrap point.
-/

@[expose] public section

open Set Filter Topology

namespace BGW.Skorokhod

private theorem isCadlag_rotate (f : D 1 ℝ) (g : Icc (0 : ℝ) 1) (m : ℝ) :
    IsCadlag (fun t : Icc (0 : ℝ) 1 =>
      if (g : ℝ) + t ≤ 1 then f (projIcc 0 1 zero_le_one ((g : ℝ) + t)) - m
      else f (projIcc 0 1 zero_le_one ((g : ℝ) + t - 1)) +
        f ⟨1, zero_le_one, le_rfl⟩ - m - f ⟨0, le_rfl, zero_le_one⟩) := by
  let A : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
    fun t => projIcc 0 1 zero_le_one ((g : ℝ) + t)
  let B : Icc (0 : ℝ) 1 → Icc (0 : ℝ) 1 :=
    fun t => projIcc 0 1 zero_le_one ((g : ℝ) + t - 1)
  have hA : Continuous A := continuous_projIcc.comp
    (continuous_const.add continuous_subtype_val)
  have hB : Continuous B := continuous_projIcc.comp
    ((continuous_const.add continuous_subtype_val).sub continuous_const)
  have hAr (t : Icc (0 : ℝ) 1) (ht : (g : ℝ) + t < 1) :
      Tendsto (fun s => f (A s)) (𝓝[>] t) (𝓝 (f (A t))) := by
    apply (isCadlag f).isRightContinuous (A t) |>.comp
      hA.continuousAt.continuousWithinAt
    intro s hs
    have hs' : (t : ℝ) < s := hs
    change max 0 (min 1 ((g : ℝ) + t)) < max 0 (min 1 ((g : ℝ) + s))
    have hgt : 0 ≤ (g : ℝ) + t := add_nonneg g.2.1 t.2.1
    rw [min_eq_right ht.le, max_eq_right hgt]
    exact lt_of_lt_of_le (lt_min ht (by linarith)) (le_max_right _ _)
  have hBr (t : Icc (0 : ℝ) 1) (ht : 1 ≤ (g : ℝ) + t) :
      Tendsto (fun s => f (B s)) (𝓝[>] t) (𝓝 (f (B t))) := by
    apply (isCadlag f).isRightContinuous (B t) |>.comp
      hB.continuousAt.continuousWithinAt
    intro s hs
    have hs' : (t : ℝ) < s := hs
    have hsumt : (g : ℝ) + t - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [g.2.2, t.2.2]
    have hsums : (g : ℝ) + s - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [g.2.2, s.2.2]
    change projIcc 0 1 zero_le_one ((g : ℝ) + t - 1) <
      projIcc 0 1 zero_le_one ((g : ℝ) + s - 1)
    rw [projIcc_of_mem zero_le_one hsumt, projIcc_of_mem zero_le_one hsums]
    change (g : ℝ) + t - 1 < (g : ℝ) + s - 1
    linarith
  have hAl (t : Icc (0 : ℝ) 1) (ht : (g : ℝ) + t ≤ 1) :
      Tendsto (fun s => f (A s)) (𝓝[<] t) (𝓝 (Function.leftLim f (A t))) := by
    apply ((isCadlag f).tendsto_nhdsLT_leftLim (A t)).comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hA.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (s : ℝ) < t := hs
    have hsumt : (g : ℝ) + t ∈ Icc (0 : ℝ) 1 :=
      ⟨add_nonneg g.2.1 t.2.1, ht⟩
    have hsums : (g : ℝ) + s ∈ Icc (0 : ℝ) 1 :=
      ⟨add_nonneg g.2.1 s.2.1, by linarith⟩
    change projIcc 0 1 zero_le_one ((g : ℝ) + s) <
      projIcc 0 1 zero_le_one ((g : ℝ) + t)
    rw [projIcc_of_mem zero_le_one hsumt, projIcc_of_mem zero_le_one hsums]
    change (g : ℝ) + s < (g : ℝ) + t
    linarith
  have hBl (t : Icc (0 : ℝ) 1) (ht : 1 < (g : ℝ) + t) :
      Tendsto (fun s => f (B s)) (𝓝[<] t) (𝓝 (Function.leftLim f (B t))) := by
    apply ((isCadlag f).tendsto_nhdsLT_leftLim (B t)).comp
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hB.continuousAt.tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hs' : (s : ℝ) < t := hs
    have hsumt : (g : ℝ) + t - 1 ∈ Icc (0 : ℝ) 1 := by
      constructor <;> linarith [g.2.2, t.2.2]
    change max 0 (min 1 ((g : ℝ) + s - 1)) <
      (projIcc 0 1 zero_le_one ((g : ℝ) + t - 1) : ℝ)
    rw [projIcc_of_mem zero_le_one hsumt]
    change max 0 (min 1 ((g : ℝ) + s - 1)) < (g : ℝ) + t - 1
    apply max_lt (by linarith)
    exact (min_le_right _ _).trans_lt (by linarith)
  constructor
  · intro t
    by_cases ht : (g : ℝ) + t < 1
    · have he : ∀ᶠ s : Icc (0 : ℝ) 1 in 𝓝[>] t, (g : ℝ) + s ≤ 1 :=
        ((continuous_const.add continuous_subtype_val).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds).eventually (eventually_le_nhds ht)
      have heq : (fun s : Icc (0 : ℝ) 1 =>
          if (g : ℝ) + s ≤ 1 then f (A s) - m
          else f (B s) + f ⟨1, zero_le_one, le_rfl⟩ - m -
            f ⟨0, le_rfl, zero_le_one⟩) =ᶠ[𝓝[>] t] (fun s => f (A s) - m) :=
        he.mono fun s hs => ite_eq_left hs
      change Tendsto _ _ _
      simp only [ite_eq_left ht.le]
      exact (tendsto_congr' heq).2 ((hAr t ht).sub_const m)
    · have ht' : 1 ≤ (g : ℝ) + t := le_of_not_gt ht
      have heq : (fun s : Icc (0 : ℝ) 1 =>
          if (g : ℝ) + s ≤ 1 then f (A s) - m
          else f (B s) + f ⟨1, zero_le_one, le_rfl⟩ - m -
            f ⟨0, le_rfl, zero_le_one⟩) =ᶠ[𝓝[>] t]
          (fun s => f (B s) + f ⟨1, zero_le_one, le_rfl⟩ - m -
            f ⟨0, le_rfl, zero_le_one⟩) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs' : (t : ℝ) < s := hs
        exact ite_eq_right (by linarith)
      have hlim := (((hBr t ht').add_const (f ⟨1, zero_le_one, le_rfl⟩)).sub_const m).sub_const
        (f ⟨0, le_rfl, zero_le_one⟩)
      change Tendsto _ _ _
      apply (tendsto_congr' heq).2
      by_cases he : (g : ℝ) + t = 1
      · have hBt : B t = ⟨0, le_rfl, zero_le_one⟩ := by simp [B, he]
        simpa only [he, le_refl, ↓reduceIte, projIcc_right, hBt, add_sub_cancel_right,
          show f ⟨0, le_rfl, zero_le_one⟩ + f ⟨1, zero_le_one, le_rfl⟩ - m -
            f ⟨0, le_rfl, zero_le_one⟩ = f ⟨1, zero_le_one, le_rfl⟩ - m by ring]
          using hlim
      · have hnot : ¬ (g : ℝ) + t ≤ 1 := fun h => he (le_antisymm h ht')
        simpa only [B, ite_eq_right hnot] using hlim
  · intro t
    by_cases ht : (g : ℝ) + t ≤ 1
    · have heq : (fun s : Icc (0 : ℝ) 1 =>
          if (g : ℝ) + s ≤ 1 then f (A s) - m
          else f (B s) + f ⟨1, zero_le_one, le_rfl⟩ - m -
            f ⟨0, le_rfl, zero_le_one⟩) =ᶠ[𝓝[<] t] (fun s => f (A s) - m) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        have hs' : (s : ℝ) < t := hs
        exact ite_eq_left (by linarith)
      exact ⟨_, (tendsto_congr' heq).2 ((hAl t ht).sub_const m)⟩
    · have ht' : 1 < (g : ℝ) + t := lt_of_not_ge ht
      have he : ∀ᶠ s : Icc (0 : ℝ) 1 in 𝓝[<] t, 1 < (g : ℝ) + s :=
        ((continuous_const.add continuous_subtype_val).continuousAt.tendsto.mono_left
          nhdsWithin_le_nhds).eventually (eventually_gt_nhds ht')
      have heq : (fun s : Icc (0 : ℝ) 1 =>
          if (g : ℝ) + s ≤ 1 then f (A s) - m
          else f (B s) + f ⟨1, zero_le_one, le_rfl⟩ - m -
            f ⟨0, le_rfl, zero_le_one⟩) =ᶠ[𝓝[<] t]
          (fun s => f (B s) + f ⟨1, zero_le_one, le_rfl⟩ - m -
            f ⟨0, le_rfl, zero_le_one⟩) := he.mono fun s hs => ite_eq_right hs.not_ge
      exact ⟨_, (tendsto_congr' heq).2
        ((((hBl t ht').add_const _).sub_const m).sub_const _)⟩

/-- The càdlàg Vervaat map: rotate at `g = vervaatTime f`, subtract the infimum, and correct
by `f 1 - f 0` after the wrap point:
`V f t = f (g + t) - m` if `g + t ≤ 1`, `V f t = f (g + t - 1) + f 1 - m - f 0` otherwise (C33). -/
noncomputable def vervaatD (f : D 1 ℝ) : D 1 ℝ where
  toFun t :=
    if (vervaatTime f : ℝ) + t ≤ 1 then
      f (Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t)) - ⨅ s, f s
    else
      f (Set.projIcc 0 1 zero_le_one ((vervaatTime f : ℝ) + t - 1)) +
        f ⟨1, zero_le_one, le_rfl⟩ - (⨅ s, f s) - f ⟨0, le_rfl, zero_le_one⟩
  isCadlag' := by
    exact isCadlag_rotate f (vervaatTime f) (⨅ s, f s)

end BGW.Skorokhod
