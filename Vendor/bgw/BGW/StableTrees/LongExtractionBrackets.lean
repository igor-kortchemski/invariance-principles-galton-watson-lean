/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionMatching

/-!
# Bracketing a matching long block

Absence of ladder hits in an interval forces that interval into one consecutive ladder block.
-/

@[expose] public section

open Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- A discrete long block has endpoints arbitrarily close to the selected continuum interval.
Reference: Billingsley (1999), Chapter 3. -/
theorem eventually_exists_longBlock_near_firstLong {B : ℕ → ℝ} (hB : Tendsto B atTop atTop)
    {M : ℝ≥0} (ω : ℕ → ℕ → ℝ) (hω : ∀ n i, IsSkipFreeIncrement (ω n i))
    {f : DLoc} (hf : GoodLongExtractionPath M f)
    (hu : Tendsto (fun n => realStepPath (M : ℝ) n (B n) (ω n)) atTop
      (𝓝 (DLoc.restrict M f))) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in atTop, ∃ r ∈ longBlockSet n (ω n),
      (firstLongEnds f).1 - ε < (ladderTime (ω n) r : ℝ) / n ∧
      (ladderTime (ω n) r : ℝ) / n < (firstLongEnds f).1 + ε ∧
      (firstLongEnds f).2 - ε < (ladderTime (ω n) (r + 1) : ℝ) / n ∧
      (ladderTime (ω n) (r + 1) : ℝ) / n < (firstLongEnds f).2 + ε := by
  let L := firstLongLabel f
  let g := passageTimeMinus L f
  let d := passageTime L f
  have hL := hf.isLeast_firstLongLabel
  have hgd : g < d := hL.1.1.2
  have hlength : 1 < (d : ℝ) - g := by
    have h := hL.1.2
    change 1 < d - g at h
    exact_mod_cast h
  have hdM : (d : ℝ) < M := by exact_mod_cast hf.end_lt
  let δ : ℝ := min (ε / 8) (min (((d : ℝ) - g - 1) / 8) (((M : ℝ) - d) / 8))
  have hδ : 0 < δ := lt_min (by positivity)
    (lt_min (by linarith only [hlength]) (by linarith only [hdM]))
  have hδε : δ ≤ ε / 8 := min_le_left _ _
  have hδgap : δ ≤ ((d : ℝ) - g - 1) / 8 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have h2δε : 2 * δ ≤ ε := by linarith only [hδε, hε]
  have hδM : δ ≤ ((M : ℝ) - d) / 8 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let a : ℝ≥0 := ⟨(g : ℝ) + δ, by positivity⟩
  let b : ℝ≥0 := ⟨(d : ℝ) - δ, by
    apply sub_nonneg.mpr
    apply hδgap.trans
    apply sub_nonneg.mp
    have heq : (d : ℝ) - ((d : ℝ) - g - 1) / 8 = (7 * (d : ℝ) + g + 1) / 8 := by
      ring
    rw [heq]
    positivity⟩
  have hga : g < a := by change (g : ℝ) < (g : ℝ) + δ; linarith only [hδ]
  have hab : a ≤ b := by
    change (g : ℝ) + δ ≤ (d : ℝ) - δ
    linarith only [hδgap, hlength]
  have hbd : b < d := by change (d : ℝ) - δ < d; linarith only [hδ]
  have hspan : 1 < (b : ℝ) - a := by
    change 1 < ((d : ℝ) - δ) - ((g : ℝ) + δ)
    linarith only [hδgap, hlength]
  obtain ⟨_, _, _, hbound, hbefore, hafter⟩ := hf.regular L hL.1.1
  obtain ⟨c, hc, hR⟩ := hbound a b hga hab hbd
  let η : ℝ≥0 := ⟨δ, hδ.le⟩
  obtain ⟨y₁, y₂, hyy, hyx, hy₁, _, hgy, hy₂g⟩ := hbefore η hδ
  obtain ⟨z₁, z₂, hxz, hzz, _, hz₂, hd₁, hd₂⟩ := hafter η hδ
  have hzM : passageTime z₂ f < M := by
    have hdz : (passageTime z₂ f : ℝ) < (d : ℝ) + δ := by exact_mod_cast hd₂
    exact_mod_cast (show (passageTime z₂ f : ℝ) < M by
      linarith only [hdz, hδM, hdM])
  have hzb : b < passageTime z₂ f := hbd.trans (hd₁.trans (hf.strictMono hzz))
  have hyg : passageTime y₁ f < g := (hf.strictMono hyy).trans hy₂g
  have hyM : passageTime y₁ f < M := hyg.trans (hgd.trans hf.end_lt)
  have hyz : y₁ ≤ z₂ := (hyy.trans (hyx.trans (hxz.trans hzz))).le
  have hgylow : (g : ℝ) - 2 * δ < passageTime y₁ f := by
    have h : (g : ℝ) < (passageTime y₁ f : ℝ) + δ := by exact_mod_cast hgy
    linarith only [h, hδ]
  have hdzup : (passageTime z₂ f : ℝ) < (d : ℝ) + 2 * δ := by
    have h : (passageTime z₂ f : ℝ) < (d : ℝ) + δ := by exact_mod_cast hd₂
    linarith only [h, hδ]
  obtain ⟨_, hytimes⟩ := tendsto_ladderTime_of_not_mem_passageJumpSet
    hB ω hω hf hu hy₁ hyM
  obtain ⟨hfinite, htimes⟩ := tendsto_ladderTime_of_not_mem_passageJumpSet
    hB ω hω hf hu hz₂ hzM
  obtain ⟨σ, hσ, he⟩ := tendsto_iff_exists_timeChange.mp hu
  have haM : a ≤ M := (hab.trans hbd.le).trans hf.end_lt.le
  have hbM : b ≤ M := hbd.le.trans hf.end_lt.le
  let a' : Set.Icc (0 : ℝ) (M : ℝ) := ⟨a, a.2, by exact_mod_cast haM⟩
  let b' : Set.Icc (0 : ℝ) (M : ℝ) := ⟨b, b.2, by exact_mod_cast hbM⟩
  have hσa := tendsto_extraction_clock M.2 hσ a'
  have hσb := tendsto_extraction_clock M.2 hσ b'
  have ha0 : (0 : ℝ) < a := (show (0 : ℝ) ≤ g from g.2).trans_lt hga
  have hσspan := (hσb.sub hσa).eventually_const_lt hspan
  have hσR := hσb.eventually_lt htimes (by exact_mod_cast hzb)
  have hYa := hytimes.eventually_lt hσa (by exact_mod_cast hyg.trans hga)
  have hYlow := hytimes.eventually_const_lt hgylow
  have hZup := htimes.eventually_lt_const hdzup
  have hAup := hσa.eventually_lt_const
    (show (a' : ℝ) < (g : ℝ) + 2 * δ by change (g : ℝ) + δ < _; linarith only [hδ])
  have hBlow := hσb.eventually_const_lt
    (show (d : ℝ) - 2 * δ < (b' : ℝ) by change _ < (d : ℝ) - δ; linarith only [hδ])
  have hBpos := hB.eventually (eventually_gt_atTop 0)
  filter_upwards [hfinite, eventually_gt_atTop 0, hBpos, hσspan, hσR,
    hσa.eventually_const_lt ha0, eventually_extraction_error_lt he (by positivity : 0 < c / 4),
    hYa, hYlow, hZup, hAup, hBlow]
    with n hnfin hn hnB hnspan hnR hna hnerr hnYa hnYlow hnZup hnAup hnBlow
  let R := ⌈(z₂ : ℝ) * B n⌉₊
  have havoid (s : ℕ) (hs : s ≤ R) :
      ¬ ((σ n a' : ℝ) ≤ (ladderTime (ω n) s : ℝ) / n ∧
        (ladderTime (ω n) s : ℝ) / n ≤ (σ n b' : ℝ)) :=
    ladderTime_not_mem_aligned_interior hf.zero haM hbM hc
      (fun t ht₁ ht₂ => (hR t ht₁ ht₂).1) hn hnB (σ n) hnerr
      (ladderTime_mono_of_finite hs hnfin).1
  obtain ⟨r, hrR, hrfin, hrstart, hrend, hrmax⟩ := exists_ladderBlock_spanning hna
    (show (σ n a' : ℝ) ≤ (σ n b' : ℝ) from (σ n).monotone hab) hnfin hnR havoid
  have hYR : ⌈(y₁ : ℝ) * B n⌉₊ ≤ R :=
    Nat.ceil_mono (mul_le_mul_of_nonneg_right (by exact_mod_cast hyz) hnB.le)
  have hYr : ⌈(y₁ : ℝ) * B n⌉₊ ≤ r := hrmax _ hYR hnYa
  have hrfinite := (ladderTime_mono_of_finite (Nat.le_succ r) hrfin).1
  have hstartlow : (g : ℝ) - 2 * δ < (ladderTime (ω n) r : ℝ) / n := by
    apply hnYlow.trans_le
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (ladderTime_mono_of_finite hYr hrfinite).2
  have hendup : (ladderTime (ω n) (r + 1) : ℝ) / n < (d : ℝ) + 2 * δ := by
    apply lt_of_le_of_lt _ hnZup
    apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
    exact_mod_cast (ladderTime_mono_of_finite (Nat.succ_le_of_lt hrR) hnfin).2
  refine ⟨r, ⟨hrfin, ?_⟩, ?_, ?_, ?_, ?_⟩
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hdiv : 1 < ((ladderTime (ω n) (r + 1) : ℝ) - ladderTime (ω n) r) / n := by
      rw [sub_div]
      exact hnspan.trans (sub_lt_sub hrend hrstart)
    have hlen : (n : ℝ) < (ladderTime (ω n) (r + 1) : ℝ) - ladderTime (ω n) r := by
      simpa only [one_mul] using (lt_div_iff₀ hn').mp hdiv
    have hmono := (ladderTime_lt_succ (hω n) hrfin).le
    have hlen' : (n : ℝ) ≤ (ladderTime (ω n) (r + 1) - ladderTime (ω n) r : ℕ) := by
      rw [Nat.cast_sub hmono]
      exact hlen.le
    exact_mod_cast hlen'
  · change (g : ℝ) - ε < _
    exact (sub_le_sub_left h2δε (g : ℝ)).trans_lt hstartlow
  · change _ < (g : ℝ) + ε
    exact (hrstart.trans hnAup).trans_le (add_le_add le_rfl h2δε)
  · change (d : ℝ) - ε < _
    exact (sub_le_sub_left h2δε (d : ℝ)).trans_lt (hnBlow.trans hrend)
  · change _ < (d : ℝ) + ε
    exact hendup.trans_le (add_le_add le_rfl h2δε)

end BGW.StableTrees
