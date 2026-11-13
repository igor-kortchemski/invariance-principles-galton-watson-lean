/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableProcess
public import BGW.Skorokhod.ReverseIncrements

/-!
# Invariance of the stable process under reversal of increments

On each finite grid, fixed-time continuity identifies reversed increments with the
original increments on the reversed grid. Independence and permutation of product
coordinates then give the stable Lévy characterization. This is the duality lemma of
J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter II, Lemma 2.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod

/-- Reversal of increments, general form: every stable Lévy law on `[0,T]` is invariant under
reversal. -/
theorem IsStableLevyLaw.map_reverseIncrements {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {P : ProbabilityMeasure (D T ℝ)} (hP : IsStableLevyLaw θ T P) :
    P.map (reverseIncrements hT.le) = P := by
  classical
  have hstable : IsStableLevyLaw θ T (P.map (reverseIncrements hT.le)) := by
    refine ⟨?_, ?_⟩
    · intro hT0
      let z : Set.Icc (0 : ℝ) T := ⟨0, le_rfl, hT0⟩
      let top : Set.Icc (0 : ℝ) T := ⟨T, hT.le, le_rfl⟩
      have heval : Measurable (fun f : D T ℝ => f z) := measurable_eval z
      have hs : MeasurableSet {f : D T ℝ | f z = 0} :=
        heval (measurableSet_singleton 0)
      change ∀ᵐ f : D T ℝ ∂((P : Measure (D T ℝ)).map (reverseIncrements hT.le)),
        f z = 0
      rw [ae_map_iff (measurable_reverseIncrements hT.le).aemeasurable hs]
      filter_upwards [hP.ae_continuousAt hθ hT top] with f hf
      have hleft : Function.leftLim f top = f top := hf.continuousWithinAt.leftLim_eq
      simp [z, top, reverseIncrements, reverseIncrementsFun, hleft]
    · intro k t ht ht0
      let s : Fin (k + 1) → Set.Icc (0 : ℝ) T := fun j =>
        ⟨T - (t j.rev : ℝ), by
          constructor
          · linarith [(t j.rev).property.2]
          · exact sub_le_self T (t j.rev).property.1⟩
      have hs : StrictMono s := by
        intro i j hij
        apply Subtype.coe_lt_coe.mpr
        change T - (t i.rev : ℝ) < T - (t j.rev : ℝ)
        have hrev : j.rev < i.rev := Fin.rev_strictAnti hij
        have htime := ht hrev
        exact sub_lt_sub_left (by exact_mod_cast htime) T
      let incS : D T ℝ → (Fin k → ℝ) := fun f j =>
        f (s j.succ) - f (s j.castSucc)
      let incR : D T ℝ → (Fin k → ℝ) := fun f i =>
        f (t i.succ) - f (t i.castSucc)
      let μ : Fin k → Measure ℝ := fun i =>
        stableLawAt θ ((t i.succ : ℝ) - t i.castSucc)
      let perm : (Fin k → ℝ) ≃ᵐ (Fin k → ℝ) :=
        MeasurableEquiv.piCongrLeft (fun _ : Fin k => ℝ) Fin.revPerm
      have hincS : Measurable incS := Measurable.of_eval fun j =>
        (measurable_eval (s j.succ)).sub (measurable_eval (s j.castSucc))
      have hincR : Measurable incR := Measurable.of_eval fun i =>
        (measurable_eval (t i.succ)).sub (measurable_eval (t i.castSucc))
      have hcont : ∀ᵐ f : D T ℝ ∂(P : Measure (D T ℝ)),
          ∀ j : Fin (k + 1), Function.leftLim f (s j) = f (s j) := by
        apply ae_all_iff.mpr
        intro j
        filter_upwards [hP.ae_continuousAt hθ hT (s j)] with f hf
        exact hf.continuousWithinAt.leftLim_eq
      have hae : incR ∘ reverseIncrements hT.le =ᵐ[(P : Measure (D T ℝ))]
          perm ∘ incS := by
        filter_upwards [hcont] with f hf
        funext i
        have hi : Fin.revPerm i.rev = i := Fin.rev_rev i
        change (reverseIncrements hT.le f (t i.succ) -
          reverseIncrements hT.le f (t i.castSucc)) = perm (incS f) i
        rw [← hi, show perm (incS f) (Fin.revPerm i.rev) = incS f i.rev by
          exact MeasurableEquiv.piCongrLeft_apply_apply _ _ _]
        have hsucc := hf i.rev.castSucc
        have hprev := hf i.rev.succ
        simp only [s, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev] at hsucc hprev
        simp only [incS, s, Fin.rev_castSucc, Fin.rev_succ, Fin.rev_rev]
        rw [reverseIncrements_apply, reverseIncrements_apply]
        simp only [Fin.revPerm_apply, Fin.rev_rev]
        change (f ⟨T, hT.le, le_rfl⟩ - Function.leftLim f ⟨T - (t i.succ : ℝ), by
          linarith [(t i.succ).property.2],
          sub_le_self T (t i.succ).property.1⟩ -
          (f ⟨T, hT.le, le_rfl⟩ - Function.leftLim f ⟨T - (t i.castSucc : ℝ), by
          linarith [(t i.castSucc).property.2],
          sub_le_self T (t i.castSucc).property.1⟩)) = _
        rw [hsucc, hprev]
        ring
      have hsource : Measure.map incS (P : Measure (D T ℝ)) =
          Measure.pi (fun j : Fin k =>
            (stableLawAt θ ((s j.succ : ℝ) - s j.castSucc) : Measure ℝ)) :=
        hP.map_increments k s hs
      have hlaws : (fun j : Fin k =>
            (stableLawAt θ ((s j.succ : ℝ) - s j.castSucc) : Measure ℝ)) =
          fun j => μ (Fin.revPerm j) := by
        funext j
        congr 2
        simp only [s, Fin.rev_castSucc, Fin.rev_succ, Fin.revPerm_apply]
        ring
      change Measure.map incR ((P : Measure (D T ℝ)).map (reverseIncrements hT.le)) =
        Measure.pi μ
      rw [Measure.map_map hincR (measurable_reverseIncrements hT.le), Measure.map_congr hae,
        ← Measure.map_map perm.measurable hincS, hsource, hlaws]
      exact Measure.pi_map_piCongrLeft Fin.revPerm μ
  exact hstable.unique hθ hT hP

/-- The stable process law is invariant under reversal of increments. -/
theorem map_reverseIncrements_stableProcessLaw {θ T : ℝ}
    (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T) :
    (stableProcessLaw θ T).map (reverseIncrements hT.le) = stableProcessLaw θ T := by
  exact (isStableLevyLaw_stableProcessLaw hθ hT).map_reverseIncrements hθ hT

end BGW.StableTrees
