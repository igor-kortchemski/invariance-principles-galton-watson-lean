/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.Skorokhod.Restrict
import Mathlib.Topology.Order.IntermediateValue

/-!
# Endpoint correction for time changes

An increasing continuous map can be kept up to an interior point and continued affinely
so that the terminal endpoint is fixed.
-/

@[expose] public section

open Set

namespace BGW.Skorokhod

/-- Correct the endpoint of an increasing continuous map by an affine final segment. -/
theorem exists_endpoint_timeChange {a r : ℝ} (hr : 0 ≤ r) (hra : r < a)
    (h : Icc (0 : ℝ) a → ℝ) (hc : Continuous h) (hm : StrictMono h)
    (h₀ : h ⟨0, le_rfl, hr.trans hra.le⟩ = 0)
    (hᵣ : h ⟨r, hr, hra.le⟩ < a) :
    ∃ τ : TimeChange a,
      (∀ t : Icc (0 : ℝ) a, (t : ℝ) ≤ r → (τ t : ℝ) = h t) ∧
      (∀ t : Icc (0 : ℝ) a, r ≤ (t : ℝ) → h ⟨r, hr, hra.le⟩ ≤ (τ t : ℝ)) := by
  let R : Icc (0 : ℝ) a := ⟨r, hr, hra.le⟩
  let m := (a - h R) / (a - r)
  have hmpos : 0 < m := div_pos (sub_pos.mpr hᵣ) (sub_pos.mpr hra)
  let cap : Icc (0 : ℝ) a → Icc (0 : ℝ) a := fun t =>
    ⟨min (t : ℝ) r, le_min t.2.1 hr, (min_le_left _ _).trans t.2.2⟩
  let F : Icc (0 : ℝ) a → ℝ := fun t => h (cap t) + m * max ((t : ℝ) - r) 0
  have hcap : Continuous cap := Continuous.subtype_mk
    (continuous_subtype_val.min continuous_const) _
  have hF : Continuous F := (hc.comp hcap).add
    (continuous_const.mul ((continuous_subtype_val.sub continuous_const).max continuous_const))
  have hhead (t : Icc (0 : ℝ) a) (ht : (t : ℝ) ≤ r) : F t = h t := by
    have heq : cap t = t := Subtype.ext (min_eq_left ht)
    simp [F, heq, max_eq_right (sub_nonpos.mpr ht)]
  have htail (t : Icc (0 : ℝ) a) (ht : r ≤ (t : ℝ)) :
      F t = h R + m * ((t : ℝ) - r) := by
    have heq : cap t = R := Subtype.ext (min_eq_right ht)
    simp [F, heq, max_eq_left (sub_nonneg.mpr ht)]
  have hstrict : StrictMono F := by
    intro x y hxy
    have hxy' : (x : ℝ) < y := hxy
    by_cases hy : (y : ℝ) ≤ r
    · rw [hhead x (hxy'.le.trans hy), hhead y hy]
      exact hm hxy
    · have hry : r < (y : ℝ) := lt_of_not_ge hy
      rw [htail y hry.le]
      by_cases hx : (x : ℝ) ≤ r
      · rw [hhead x hx]
        have hh : h x ≤ h R := hm.monotone hx
        have hp := mul_pos hmpos (sub_pos.mpr hry)
        linarith
      · rw [htail x (le_of_not_ge hx)]
        nlinarith
  have hF₀ : F ⟨0, le_rfl, hr.trans hra.le⟩ = 0 := by
    rw [hhead _ hr, h₀]
  have hFa : F ⟨a, hr.trans hra.le, le_rfl⟩ = a := by
    rw [htail _ hra.le]
    dsimp [m]
    rw [div_mul_cancel₀ _ (sub_ne_zero.mpr hra.ne')]
    ring
  let f : Icc (0 : ℝ) a → Icc (0 : ℝ) a := fun t =>
    ⟨F t, by
      constructor
      · simpa only [hF₀] using hstrict.monotone
          (show (⟨0, le_rfl, hr.trans hra.le⟩ : Icc (0 : ℝ) a) ≤ t from t.2.1)
      · simpa only [hFa] using hstrict.monotone
          (show t ≤ (⟨a, hr.trans hra.le, le_rfl⟩ : Icc (0 : ℝ) a) from t.2.2)⟩
  let : PreconnectedSpace (Icc (0 : ℝ) a) :=
    isPreconnected_iff_preconnectedSpace.mp isPreconnected_Icc
  have hsurj : Function.Surjective f := by
    intro y
    have hy : (y : ℝ) ∈ Icc (F ⟨0, le_rfl, hr.trans hra.le⟩)
        (F ⟨a, hr.trans hra.le, le_rfl⟩) := by
      rw [hF₀, hFa]
      exact y.2
    obtain ⟨x, hx⟩ := intermediate_value_univ
      ⟨0, le_rfl, hr.trans hra.le⟩ ⟨a, hr.trans hra.le, le_rfl⟩ hF hy
    exact ⟨x, Subtype.ext hx⟩
  let τ : TimeChange a := StrictMono.orderIsoOfSurjective f hstrict hsurj
  refine ⟨τ, hhead, ?_⟩
  intro t ht
  change h R ≤ F t
  rw [htail t ht]
  exact le_add_of_nonneg_right (mul_nonneg hmpos.le (sub_nonneg.mpr ht))

end BGW.Skorokhod
