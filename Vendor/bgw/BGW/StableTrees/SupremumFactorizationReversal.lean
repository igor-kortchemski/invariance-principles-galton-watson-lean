/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableProcessReversal
public import BGW.StableTrees.SupremumLocalTime
public import BGW.StableTrees.StablePassageSubordinator
public import BGW.StableTrees.ReflectedRestart
import BGW.Skorokhod.MeasurableExtrema

/-! # Joint extrema under fixed-horizon reversal

Reference: J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- Reversal turns the supremum into the terminal value minus the running infimum,
for a path whose jumps are nonnegative. -/
theorem iSup_reverseIncrements {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ)
    (hf : ∀ t, Function.leftLim f t ≤ f t) :
    (⨆ u, reverseIncrements hT f u) = f ⟨T, hT, le_rfl⟩ - ⨅ u, f u := by
  let _ : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  have hb := (isBounded_range f).bddBelow
  have hrb := (isBounded_range (reverseIncrements hT f)).bddAbove
  apply le_antisymm
  · apply ciSup_le
    intro u
    rw [reverseIncrements_apply]
    apply sub_le_sub_left
    apply isClosed_Ici.mem_of_mapClusterPt (mapClusterPt_leftLim f _)
    exact Eventually.of_forall fun s => ciInf_le hb s
  · have hlo : f ⟨T, hT, le_rfl⟩ - (⨆ u, reverseIncrements hT f u) ≤ ⨅ u, f u := by
      apply le_ciInf
      intro v
      let u : Icc (0 : ℝ) T := ⟨T - v, by linarith [v.2.2], by linarith [v.2.1]⟩
      have he : (⟨T - u, by linarith [u.2.2], by linarith [u.2.1]⟩ : Icc (0 : ℝ) T) = v := by
        apply Subtype.ext
        dsimp [u]
        ring
      have hu := le_ciSup hrb u
      rw [reverseIncrements_apply, he] at hu
      linarith [hf v]
    linarith

/-- The reversed terminal value is the original increment over the whole interval. -/
theorem reverseIncrements_terminal {T : ℝ} (hT : 0 ≤ T) (f : D T ℝ) :
    reverseIncrements hT f ⟨T, hT, le_rfl⟩ =
      f ⟨T, hT, le_rfl⟩ - f ⟨0, le_rfl, hT⟩ := by
  rw [reverseIncrements_apply]
  have he : (⟨T - T, by linarith, by linarith⟩ : Icc (0 : ℝ) T) = ⟨0, le_rfl, hT⟩ := by
    apply Subtype.ext
    simp
  rw [he, leftLim_eq_of_isBot (fun u => u.2.1)]

private theorem measurable_fullSup {T : ℝ} (hT : 0 ≤ T) :
    Measurable (fun f : D T ℝ => ⨆ u, f u) := by
  have _ : Nonempty (Icc (0 : ℝ) T) := ⟨⟨0, le_rfl, hT⟩⟩
  have hm := measurable_iSup_eval (T := T) (J := univ) ordConnected_univ
  convert hm using 1
  funext f
  have hb := (isBounded_range f).bddAbove
  have hb' : BddAbove (range (fun u : (univ : Set (Icc (0 : ℝ) T)) => f u)) :=
    hb.mono (by rintro _ ⟨u, rfl⟩; exact ⟨u.1, rfl⟩)
  apply le_antisymm
  · exact ciSup_le fun u => le_ciSup hb' ⟨u, mem_univ _⟩
  · exact ciSup_le fun u => le_ciSup hb u.1

/-- Fixed-horizon joint reversal of the supremum and drawdown, in nonnegative test form. -/
theorem lintegral_sup_drawdown_reverse {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ f, F (⨆ u, f u) * G ((⨆ u, f u) - f ⟨T, hT.le, le_rfl⟩)
      ∂(stableProcessLaw θ T : Measure (D T ℝ))) =
    ∫⁻ f, G (-(⨅ u, f u)) * F (f ⟨T, hT.le, le_rfl⟩ - ⨅ u, f u)
      ∂(stableProcessLaw θ T : Measure (D T ℝ)) := by
  have hm : Measurable (fun f : D T ℝ =>
      F (⨆ u, f u) * G ((⨆ u, f u) - f ⟨T, hT.le, le_rfl⟩)) :=
    (hF.comp (measurable_fullSup hT.le)).mul
      (hG.comp ((measurable_fullSup hT.le).sub (measurable_eval_top hT.le)))
  calc
    _ = ∫⁻ f, F (⨆ u, reverseIncrements hT.le f u) *
        G ((⨆ u, reverseIncrements hT.le f u) -
          reverseIncrements hT.le f ⟨T, hT.le, le_rfl⟩)
        ∂(stableProcessLaw θ T : Measure (D T ℝ)) := by
      have hmap := congrArg (fun μ : ProbabilityMeasure (D T ℝ) => (μ : Measure (D T ℝ)))
        (map_reverseIncrements_stableProcessLaw hθ hT)
      change Measure.map (reverseIncrements hT.le) (stableProcessLaw θ T : Measure _) =
        (stableProcessLaw θ T : Measure _) at hmap
      rw [← lintegral_map hm (measurable_reverseIncrements hT.le), hmap]
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_eval_zero_stableProcessLaw hθ hT,
        ae_leftLim_le_stableProcessLaw hθ hT] with f hf0 hf
      rw [iSup_reverseIncrements hT.le f hf, reverseIncrements_terminal, hf0, sub_zero]
      have he : f ⟨T, hT.le, le_rfl⟩ - (⨅ u, f u) - f ⟨T, hT.le, le_rfl⟩ =
          -(⨅ u, f u) := by ring
      rw [he, mul_comm]

private theorem iSup_restrict_eq_supRunning (f : DLoc) (t : ℝ≥0) :
    (⨆ u, DLoc.restrict t f u) = supRunning f t := by
  let _ : Nonempty (Icc (0 : ℝ) (t : ℝ)) := ⟨⟨0, le_rfl, t.2⟩⟩
  apply le_antisymm
  · apply ciSup_le
    intro u
    exact eval_le_supRunning f (u := ⟨u, u.2.1⟩) (by exact_mod_cast u.2.2)
  · apply supRunning_le
    intro u
    exact le_ciSup (isBounded_range (DLoc.restrict t f)).bddAbove
      ⟨u, u.1.2, by exact_mod_cast u.2⟩

private theorem iInf_restrict_eq_runningInfLoc (f : DLoc) (t : ℝ≥0) :
    (⨅ u, DLoc.restrict t f u) = runningInfLoc f t := by
  let _ : Nonempty (Icc (0 : ℝ) (t : ℝ)) := ⟨⟨0, le_rfl, t.2⟩⟩
  apply le_antisymm
  · apply le_runningInfLoc
    intro u
    exact ciInf_le (isBounded_range (DLoc.restrict t f)).bddBelow
      ⟨u, u.1.2, by exact_mod_cast u.2⟩
  · apply le_ciInf
    intro u
    exact runningInfLoc_le_eval f t ⟨⟨u, u.2.1⟩, by exact_mod_cast u.2.2⟩

/-- Fixed-time joint reversal on the local stable path law. -/
theorem lintegral_sup_drawdown_reverse_local {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    {t : ℝ≥0} (ht : 0 < t) {F G : ℝ → ℝ≥0∞} (hF : Measurable F) (hG : Measurable G) :
    (∫⁻ f, F (supRunning f t) * G (supReflected f t)
      ∂(stableLocalLaw θ : Measure DLoc)) =
    ∫⁻ f, G (localTime f t) * F ((reflectedFrom 0 f).1 t)
      ∂(stableLocalLaw θ : Measure DLoc) := by
  let _ : Nonempty (Icc (0 : ℝ) (t : ℝ)) := ⟨⟨0, le_rfl, t.2⟩⟩
  let _ : Nonempty (univ : Set (Icc (0 : ℝ) (t : ℝ))) := ⟨⟨⟨0, le_rfl, t.2⟩, mem_univ _⟩⟩
  have htr : (0 : ℝ) < (t : ℝ) := ht
  have hSup : Measurable (fun f : D (t : ℝ) ℝ =>
      F (⨆ u, f u) * G ((⨆ u, f u) - f ⟨t, t.2, le_rfl⟩)) :=
    (hF.comp (measurable_fullSup t.2)).mul
      (hG.comp ((measurable_fullSup t.2).sub (measurable_eval_top t.2)))
  have hInf : Measurable (fun f : D (t : ℝ) ℝ => ⨅ u, f u) := by
    have hm := measurable_iInf_eval (T := (t : ℝ)) (J := univ) ordConnected_univ
    convert hm using 1
    funext f
    have hb := (isBounded_range f).bddBelow
    have hb' : BddBelow (range (fun u : (univ : Set (Icc (0 : ℝ) (t : ℝ))) => f u)) :=
      hb.mono (by rintro _ ⟨u, rfl⟩; exact ⟨u.1, rfl⟩)
    apply le_antisymm
    · exact le_ciInf fun u => ciInf_le hb u.1
    · exact le_ciInf fun u => ciInf_le hb' ⟨u, mem_univ _⟩
  have hPair : Measurable (fun f : D (t : ℝ) ℝ =>
      G (-(⨅ u, f u)) * F (f ⟨t, t.2, le_rfl⟩ - ⨅ u, f u)) :=
    (hG.comp hInf.neg).mul (hF.comp ((measurable_eval_top t.2).sub hInf))
  have heq := lintegral_sup_drawdown_reverse hθ htr hF hG
  rw [← map_restrict_stableLocalLaw hθ ht,
    lintegral_map hSup (DLoc.measurable_restrict t),
    lintegral_map hPair (DLoc.measurable_restrict t)] at heq
  simp_rw [iSup_restrict_eq_supRunning, iInf_restrict_eq_runningInfLoc] at heq
  change (∫⁻ f, F (supRunning f t) * G (supReflected f t)
    ∂(stableLocalLaw θ : Measure DLoc)) =
    ∫⁻ f, G (-(runningInfLoc f t)) * F (f.1 t - runningInfLoc f t)
      ∂(stableLocalLaw θ : Measure DLoc) at heq
  rw [heq]
  apply lintegral_congr_ae
  filter_upwards [ae_eval_zero_stableLocalLaw hθ] with f hf
  rw [reflectedFrom_zero_apply hf]
  rfl

end BGW.StableTrees
