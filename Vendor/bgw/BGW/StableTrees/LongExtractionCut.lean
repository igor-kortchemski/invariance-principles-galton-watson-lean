/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.LongExtractionCutContinuity
public import BGW.StableTrees.LongExtractionCutSupport

/-!
# Stopped-cut convergence for the first long block

Endpoint convergence and joint continuity of moving stopped cuts identify the extracted path.
The modification of the last step costs at most one spatial mesh.
-/

@[expose] public section

open Set Filter Topology
open scoped NNReal
open BGW.Skorokhod BGW.Probability.RealWalk

namespace BGW.StableTrees

/-- **Stopped-cut convergence**: the whole triple `(g_n, d_n, cut_n)` converges, in
`ℝ × ℝ × D T ℝ`, for every cutoff `T` at which the limit cut is continuous.  The cut is the
translated block path, extended by zero. -/
theorem tendsto_firstLongBlock_cut {B : ℕ → ℝ} (hB : Tendsto B atTop atTop)
    {M T : ℝ≥0} (ω : ℕ → ℕ → ℝ) (hω : ∀ n i, IsSkipFreeIncrement (ω n i))
    {f : DLoc} (hf : GoodLongExtractionCutPath M T f)
    (hu : Tendsto (fun n => realStepPath (M : ℝ) n (B n) (ω n)) atTop
      (𝓝 (DLoc.restrict M f))) :
    Tendsto (fun n => extractionTriple (B n) n T (ω n)) atTop (𝓝 (longCutTriple T f)) := by
  have hends := tendsto_firstLongBlock_endpoints hB ω hω hf.1 hu
  let g := passageTimeMinus (firstLongLabel f) f
  let d := passageTime (firstLongLabel f) f
  have hgd : g < d := hf.1.isLeast_firstLongLabel.1.1.2
  have hdM : d < M := hf.1.end_lt
  let G : Icc (0 : ℝ) (M : ℝ) := ⟨g, g.2, by exact_mod_cast hgd.le.trans hdM.le⟩
  let D : Icc (0 : ℝ) (M : ℝ) := ⟨d, d.2, by exact_mod_cast hdM.le⟩
  let a (n : ℕ) : Icc (0 : ℝ) (M : ℝ) :=
    projIcc 0 (M : ℝ) M.2 (extractionEndpoints n (ω n)).1
  let c (n : ℕ) : Icc (0 : ℝ) (M : ℝ) :=
    projIcc 0 (M : ℝ) M.2 (extractionEndpoints n (ω n)).2
  let b (n : ℕ) := max (a n) (c n)
  have hab (n : ℕ) : a n ≤ b n := le_max_left _ _
  have hproj : Continuous (projIcc (0 : ℝ) (M : ℝ) M.2) := continuous_projIcc
  have hA : Tendsto a atTop (𝓝 G) := by
    have h := hproj.tendsto (g : ℝ) |>.comp hends.fst_nhds
    have hG : projIcc 0 (M : ℝ) M.2 (g : ℝ) = G := projIcc_of_mem M.2 G.2
    simpa only [a, Function.comp_def, hG] using h
  have hC : Tendsto c atTop (𝓝 D) := by
    have h := hproj.tendsto (d : ℝ) |>.comp hends.snd_nhds
    have hD : projIcc 0 (M : ℝ) M.2 (d : ℝ) = D := projIcc_of_mem M.2 D.2
    simpa only [c, Function.comp_def, hD] using h
  have hGD : G ≤ D := hgd.le
  have hBend : Tendsto b atTop (𝓝 D) := by
    simpa only [max_eq_right hGD] using hA.max hC
  let incM : Icc (0 : ℝ) (M : ℝ) → ℝ≥0 := fun t => ⟨(t : ℝ), t.2.1⟩
  have hincM : Continuous incM := Continuous.subtype_mk continuous_subtype_val _
  have hsourceG : ContinuousAt (DLoc.restrict M f) G :=
    hf.1.continuousAt_firstLong_ends.1.comp_of_eq (hincM.continuousAt (x := G)) rfl
  have hsourceD : ContinuousAt (DLoc.restrict M f) D :=
    hf.1.continuousAt_firstLong_ends.2.comp_of_eq (hincM.continuousAt (x := D)) rfl
  have hcutEq : translatedStoppedCut T (DLoc.restrict M f) G D hGD =
      excursionRestrict T (firstLongMark f) := hf.1.translatedStoppedCut_eq
  have hcutCont : ContinuousAt (translatedStoppedCut T (DLoc.restrict M f) G D hGD)
      ⟨T, T.2, le_rfl⟩ := by
    rw [hcutEq]
    let incT : Icc (0 : ℝ) (T : ℝ) → ℝ≥0 := fun t => ⟨(t : ℝ), t.2.1⟩
    have hincT : Continuous incT := Continuous.subtype_mk continuous_subtype_val _
    exact hf.2.comp_of_eq (hincT.continuousAt (x := ⟨T, T.2, le_rfl⟩)) rfl
  let Cn (n : ℕ) := translatedStoppedCut T
    (realStepPath (M : ℝ) n (B n) (ω n)) (a n) (b n) (hab n)
  have hCn : Tendsto Cn atTop (𝓝 (excursionRestrict T (firstLongMark f))) := by
    have h := tendsto_translatedStoppedCut T hu a b hab
      (show G < D from hgd) (continuous_subtype_val.tendsto G |>.comp hA)
      (continuous_subtype_val.tendsto D |>.comp hBend) hsourceG hsourceD hcutCont
    rwa [hcutEq] at h
  have hnonempty := eventually_longBlockSet_nonempty hB ω hω hf.1 hu
  have hupper : ∀ᶠ n in atTop, (extractionEndpoints n (ω n)).2 < M :=
    hends.snd_nhds.eventually_lt_const (by exact_mod_cast hdM)
  have hbound : ∀ᶠ n in atTop, dist (Cn n)
      (realStepPath (T : ℝ) n (B n) (blockIncrements (ω n) (firstLongIndex n (ω n)))) ≤
        1 / B n := by
    filter_upwards [hnonempty, hupper, eventually_gt_atTop 0,
      hB.eventually (eventually_gt_atTop 0)] with n hnmem hnM hn hnB
    have hmem : firstLongIndex n (ω n) ∈ longBlockSet n (ω n) := csInf_mem hnmem
    have hfin : walkHitTime (firstLongIndex n (ω n) + 1) (ω n) ≠ ⊤ := hmem.1
    have hmono := (ladderTime_mono_of_finite (Nat.le_succ _) hfin).2
    have hle : (extractionEndpoints n (ω n)).1 ≤ (extractionEndpoints n (ω n)).2 := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
      exact_mod_cast hmono
    have hnonneg₁ : 0 ≤ (extractionEndpoints n (ω n)).1 :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n)
    have hnonneg₂ : 0 ≤ (extractionEndpoints n (ω n)).2 :=
      div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg n)
    have ha : (a n : ℝ) = (extractionEndpoints n (ω n)).1 := by
      change max 0 (min (M : ℝ) (extractionEndpoints n (ω n)).1) = _
      rw [min_eq_right (hle.trans hnM.le), max_eq_right hnonneg₁]
    have hb : (b n : ℝ) = (extractionEndpoints n (ω n)).2 := by
      change max (a n : ℝ) (max 0 (min (M : ℝ) (extractionEndpoints n (ω n)).2)) = _
      rw [ha, min_eq_right hnM.le, max_eq_right hnonneg₂, max_eq_right hle]
    have h := dist_blockIncrements_translatedStoppedCut_le T (hω n) hfin hn hnB
      (a n) (b n) (hab n) ha hb
    exact (dist_comm _ _).trans_le h
  have hinv : Tendsto (fun n => 1 / B n) atTop (𝓝 (0 : ℝ)) := by
    have heq : (fun n => 1 / B n) = ((fun x : ℝ => x⁻¹) ∘ B) := by
      funext n
      exact one_div _
    rw [heq]
    exact tendsto_inv_atTop_zero.comp hB
  have hdist : Tendsto (fun n => dist (Cn n)
      (realStepPath (T : ℝ) n (B n) (blockIncrements (ω n) (firstLongIndex n (ω n)))))
      atTop (𝓝 0) :=
    squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg) hbound hinv
  have hcut := hCn.congr_dist hdist
  exact hends.fst_nhds.prodMk_nhds (hends.snd_nhds.prodMk_nhds hcut)

end BGW.StableTrees
