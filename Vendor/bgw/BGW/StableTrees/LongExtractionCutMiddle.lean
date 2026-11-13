/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionCutClocks

/-!
# Extension of a clock from an interior interval

Affine initial and final segments extend an increasing map to a time change. Its displacement
is bounded by the displacement on the preserved middle interval.
-/

@[expose] public section

open Set
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Extend a middle clock affinely to both endpoints without increasing its displacement bound.
Reference: Billingsley (1999), Chapter 3. -/
theorem exists_extraction_middle_timeChange {T l r D : ℝ}
    (hl : 0 < l) (hlr : l < r) (hrT : r < T)
    (h : Icc l r → ℝ) (hc : Continuous h) (hm : StrictMono h)
    (hlo : 0 < h ⟨l, le_rfl, hlr.le⟩) (hhi : h ⟨r, hlr.le, le_rfl⟩ < T)
    (hdisp : ∀ t, |h t - t| ≤ D) :
    ∃ τ : TimeChange T,
      (∀ (t : Icc (0 : ℝ) T) (htl : l ≤ (t : ℝ)) (htr : (t : ℝ) ≤ r),
        (τ t : ℝ) = h ⟨t, htl, htr⟩) ∧
      (∀ t : Icc (0 : ℝ) T, (t : ℝ) ≤ l → (τ t : ℝ) ≤ h ⟨l, le_rfl, hlr.le⟩) ∧
      (∀ t : Icc (0 : ℝ) T, r ≤ (t : ℝ) → h ⟨r, hlr.le, le_rfl⟩ ≤ (τ t : ℝ)) ∧
      ∀ t : Icc (0 : ℝ) T, |(τ t : ℝ) - t| ≤ D := by
  let L : Icc l r := ⟨l, le_rfl, hlr.le⟩
  let R : Icc l r := ⟨r, hlr.le, le_rfl⟩
  let m₀ := h L / l
  let m₁ := (T - h R) / (T - r)
  have hm₀ : 0 < m₀ := div_pos hlo hl
  have hm₁ : 0 < m₁ := div_pos (sub_pos.mpr hhi) (sub_pos.mpr hrT)
  let cap : Icc (0 : ℝ) T → Icc l r := fun t =>
    ⟨max l (min (t : ℝ) r), le_max_left _ _, max_le hlr.le (min_le_right _ _)⟩
  let F : Icc (0 : ℝ) T → ℝ := fun t =>
    h (cap t) + m₀ * min ((t : ℝ) - l) 0 + m₁ * max ((t : ℝ) - r) 0
  have hcap : Continuous cap := Continuous.subtype_mk
    (continuous_const.max (continuous_subtype_val.min continuous_const)) _
  have hF : Continuous F := ((hc.comp hcap).add
    (continuous_const.mul ((continuous_subtype_val.sub continuous_const).min continuous_const))).add
    (continuous_const.mul ((continuous_subtype_val.sub continuous_const).max continuous_const))
  have hhead (t : Icc (0 : ℝ) T) (ht : (t : ℝ) ≤ l) : F t = m₀ * t := by
    have hct : cap t = L := Subtype.ext (by simp [cap, L, min_eq_left (ht.trans hlr.le), ht])
    have heq : m₀ * l = h L := div_mul_cancel₀ _ hl.ne'
    simp only [F, hct, min_eq_left (sub_nonpos.mpr ht),
      max_eq_right (sub_nonpos.mpr (ht.trans hlr.le)), mul_zero, add_zero]
    linarith only [heq]
  have hmiddle (t : Icc (0 : ℝ) T) (htl : l ≤ (t : ℝ)) (htr : (t : ℝ) ≤ r) :
      F t = h ⟨t, htl, htr⟩ := by
    have hct : cap t = ⟨t, htl, htr⟩ :=
      Subtype.ext (by simp [cap, min_eq_left htr, max_eq_right htl])
    simp only [F, hct, min_eq_right (sub_nonneg.mpr htl),
      max_eq_right (sub_nonpos.mpr htr), mul_zero, add_zero]
  have htail (t : Icc (0 : ℝ) T) (ht : r ≤ (t : ℝ)) :
      F t = h R + m₁ * ((t : ℝ) - r) := by
    have hct : cap t = R := Subtype.ext (by simp [cap, R, min_eq_right ht, max_eq_right hlr.le])
    simp only [F, hct, min_eq_right (sub_nonneg.mpr (hlr.le.trans ht)),
      mul_zero, add_zero, max_eq_left (sub_nonneg.mpr ht)]
  have hstrict : StrictMono F := by
    intro x y hxy
    have hxy' : (x : ℝ) < y := hxy
    by_cases hy : (y : ℝ) ≤ l
    · rw [hhead x (hxy'.le.trans hy), hhead y hy]
      exact mul_lt_mul_of_pos_left hxy' hm₀
    by_cases hx : r ≤ (x : ℝ)
    · rw [htail x hx, htail y (hx.trans hxy'.le)]
      have hlt := mul_lt_mul_of_pos_left (sub_lt_sub_right hxy' r) hm₁
      linarith only [hlt]
    have hclt : cap x < cap y := by
      change max l (min (x : ℝ) r) < max l (min (y : ℝ) r)
      by_cases hxl : (x : ℝ) ≤ l
      · rw [min_eq_left (hxl.trans hlr.le), max_eq_left hxl]
        exact lt_of_lt_of_le (lt_min (lt_of_not_ge hy) hlr) (le_max_right _ _)
      · rw [min_eq_left (le_of_not_ge hx), max_eq_right (le_of_not_ge hxl)]
        exact lt_of_lt_of_le (lt_min hxy' (lt_of_not_ge hx)) (le_max_right _ _)
    have hhc := hm hclt
    have hh := mul_le_mul_of_nonneg_left
      (min_le_min_right (0 : ℝ) (sub_le_sub_right hxy'.le l)) hm₀.le
    have ht := mul_le_mul_of_nonneg_left
      (max_le_max_right (0 : ℝ) (sub_le_sub_right hxy'.le r)) hm₁.le
    dsimp only [F]
    linarith only [hhc, hh, ht]
  have hT : 0 ≤ T := (hl.trans (hlr.trans hrT)).le
  have hzero : F ⟨0, le_rfl, hT⟩ = 0 := by rw [hhead _ hl.le]; ring
  have htop : F ⟨T, hT, le_rfl⟩ = T := by
    rw [htail _ hrT.le]
    dsimp only [m₁]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hrT.ne')]
    ring
  let f : Icc (0 : ℝ) T → Icc (0 : ℝ) T := fun t => ⟨F t, by
    constructor
    · simpa only [hzero] using hstrict.monotone
        (show (⟨0, le_rfl, hT⟩ : Icc (0 : ℝ) T) ≤ t from t.2.1)
    · simpa only [htop] using hstrict.monotone
        (show t ≤ (⟨T, hT, le_rfl⟩ : Icc (0 : ℝ) T) from t.2.2)⟩
  let : PreconnectedSpace (Icc (0 : ℝ) T) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : ℝ) ∈ Icc (F ⟨0, le_rfl, hT⟩) (F ⟨T, hT, le_rfl⟩) := by
      rw [hzero, htop]
      exact y.2
    obtain ⟨x, hFx⟩ := intermediate_value_univ
      ⟨0, le_rfl, hT⟩ ⟨T, hT, le_rfl⟩ hF hy
    exact ⟨x, Subtype.ext hFx⟩
  let τ : TimeChange T := StrictMono.orderIsoOfSurjective f hstrict hsurj
  have hτmid := hmiddle
  refine ⟨τ, hτmid, ?_, ?_, ?_⟩
  · intro t ht
    have hmono := τ.monotone (show t ≤ (⟨l, hl.le, (hlr.trans hrT).le⟩ : Icc (0 : ℝ) T)
      from ht)
    change F t ≤ F ⟨l, hl.le, (hlr.trans hrT).le⟩ at hmono
    rw [hmiddle ⟨l, hl.le, (hlr.trans hrT).le⟩ le_rfl hlr.le] at hmono
    exact hmono
  · intro t ht
    have hmono := τ.monotone (show (⟨r, (hl.trans hlr).le, hrT.le⟩ : Icc (0 : ℝ) T) ≤ t
      from ht)
    change F ⟨r, (hl.trans hlr).le, hrT.le⟩ ≤ F t at hmono
    rw [hmiddle ⟨r, (hl.trans hlr).le, hrT.le⟩ hlr.le le_rfl] at hmono
    exact hmono
  · intro t
    change |F t - t| ≤ D
    by_cases htl : (t : ℝ) ≤ l
    · rw [hhead t htl]
      have heq : m₀ * (t : ℝ) - t = (h L - l) * ((t : ℝ) / l) := by
        dsimp only [m₀]
        field_simp
      rw [heq, abs_mul, abs_of_nonneg (div_nonneg t.2.1 hl.le)]
      exact (mul_le_mul_of_nonneg_left ((div_le_one hl).mpr htl) (abs_nonneg _)).trans
        (by simpa only [mul_one] using hdisp L)
    by_cases htr : r ≤ (t : ℝ)
    · rw [htail t htr]
      have heq : h R + m₁ * ((t : ℝ) - r) - t =
          (h R - r) * ((T - t) / (T - r)) := by
        dsimp only [m₁]
        field_simp
        ring
      rw [heq, abs_mul, abs_of_nonneg (div_nonneg (sub_nonneg.mpr t.2.2) (sub_pos.mpr hrT).le)]
      exact (mul_le_mul_of_nonneg_left
        ((div_le_one (sub_pos.mpr hrT)).mpr (sub_le_sub_left htr T)) (abs_nonneg _)).trans
          (by simpa only [mul_one] using hdisp R)
    rw [hmiddle t (le_of_not_ge htl) (le_of_not_ge htr)]
    exact hdisp _

end BGW.StableTrees
