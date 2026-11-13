/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumLocalTimeIdent

/-!
# Strict inversion of an additive restarted clock

Finite strict inverses of a monotone clock respect restart at an attained level.

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- A clock restart at level `z` implies addition of its finite strict inverses. -/
theorem supLadderTime_add_of_clock_restart {θ : ℝ} {f g : DLoc} {z s : ℝ≥0}
    (hm : Monotone (supLocalTime θ f))
    (hf : ∀ w, supLocalTimeInverse θ f w = (supLadderTime θ w f : WithTop ℝ≥0))
    (hg : ∀ w, supLocalTimeInverse θ g w = (supLadderTime θ w g : WithTop ℝ≥0))
    (hs : supLocalTime θ f s = z)
    (hrestart : ∀ t, supLocalTime θ f (s + t) = (z : ℝ) + supLocalTime θ g t)
    (u : ℝ≥0) :
    supLadderTime θ (z + u) f = s + supLadderTime θ u g := by
  have hle (r : ℝ≥0) (hr : (u : ℝ) < supLocalTime θ g r) :
      supLadderTime θ (z + u) f ≤ s + r := by
    have h := sInf_le (α := WithTop ℝ≥0)
      (show (s + r : WithTop ℝ≥0) ∈ {t : WithTop ℝ≥0 |
        ∃ v : ℝ≥0, t = v ∧ ((z + u : ℝ≥0) : ℝ) < supLocalTime θ f v} from
        ⟨s + r, by simp, by rw [hrestart, NNReal.coe_add]; linarith⟩)
    change supLocalTimeInverse θ f (z + u) ≤ _ at h
    rw [hf] at h
    exact_mod_cast h
  apply le_antisymm
  · apply le_of_forall_gt
    intro b hb
    have hslt : s < b := lt_of_le_of_lt
      (le_add_of_nonneg_right (show 0 ≤ supLadderTime θ u g from zero_le)) hb
    have hdiff : supLadderTime θ u g < b - s := by
      rw [← NNReal.coe_lt_coe, NNReal.coe_sub hslt.le]
      have hh : (s : ℝ) + supLadderTime θ u g < b := by exact_mod_cast hb
      linarith
    have hi : supLocalTimeInverse θ g u < ((b - s : ℝ≥0) : WithTop ℝ≥0) := by
      rw [hg]
      exact_mod_cast hdiff
    obtain ⟨v, hv, hvb⟩ := sInf_lt_iff.mp hi
    obtain ⟨r, rfl, hr⟩ := hv
    have hrb : r < b - s := by exact_mod_cast hvb
    exact (hle r hr).trans_lt (by
      rw [← NNReal.coe_lt_coe, NNReal.coe_add]
      have hh : (r : ℝ) < b - s := by
        simpa only [NNReal.coe_sub hslt.le] using (NNReal.coe_lt_coe.mpr hrb)
      linarith)
  · have hlower : ((s + supLadderTime θ u g : ℝ≥0) : WithTop ℝ≥0) ≤
        supLocalTimeInverse θ f (z + u) := by
      apply le_sInf
      rintro _ ⟨r, rfl, hr⟩
      have hsr : s ≤ r := by
        by_contra hn
        have h := hm (le_of_not_ge hn)
        rw [hs] at h
        rw [NNReal.coe_add] at hr
        have hu := u.coe_nonneg
        linarith
      have hc : (u : ℝ) < supLocalTime θ g (r - s) := by
        have he := hrestart (r - s)
        rw [add_tsub_cancel_of_le hsr] at he
        rw [he, NNReal.coe_add] at hr
        linarith
      have hi : supLocalTimeInverse θ g u ≤ ((r - s : ℝ≥0) : WithTop ℝ≥0) :=
        sInf_le ⟨r - s, rfl, hc⟩
      rw [hg] at hi
      have hi' : supLadderTime θ u g ≤ r - s := by exact_mod_cast hi
      have he : s + supLadderTime θ u g ≤ r := by
        have hh := add_le_add_left hi' s
        simpa only [tsub_add_cancel_of_le hsr, add_comm] using hh
      exact_mod_cast he
    rw [hf] at hlower
    exact_mod_cast hlower

end BGW.StableTrees
