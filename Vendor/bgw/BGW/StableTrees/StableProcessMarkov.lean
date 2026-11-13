/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StableProcessMarkovAux

/-!
# Scaling and the simple Markov property of the stable process

The time-space scaling identity follows from the characterization of the stable process law. The
simple Markov property expresses independence of the restricted past and the future increment
path, and identifies the law of the latter (J. Bertoin, *Lévy Processes*, Cambridge University
Press, 1996, Chapter I, Section 1 and Chapter VIII).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped Topology

namespace BGW.StableTrees

open BGW.Skorokhod

/-- Time-space scaling of the stable process law from horizon `c * T` to `T`. -/
theorem stableProcessLaw_scaling {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {c : ℝ} (hc : 0 < c) :
    (stableProcessLaw θ (c * T)).map
        (fun f : D (c * T) ℝ => timeSpaceScale T (mul_pos hc hT).le
          (f, c ^ (-(1 / θ)), (⟨c, Set.mem_Ioi.mpr hc⟩ : Set.Ioi (0 : ℝ)))) =
      stableProcessLaw θ T := by
  apply (eq_stableProcessLaw_iff hθ hT).mpr
  exact (isStableLevyLaw_stableProcessLaw hθ (mul_pos hc hT)).map_timeSpaceScale hθ hT hc

/-- Simple Markov property at a deterministic time `s ∈ [0, T]`, as independence of
the whole past path (the natural past, via `comap_restrict_eq_iSup_comap_eval`) and the whole
future increment path, together with the law of the future increment path. -/
theorem stableProcessLaw_simpleMarkov {θ T : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (hT : 0 < T)
    {s : ℝ} (hs : 0 ≤ s) (hsT : s ≤ T) :
    IndepFun (restrict (E := ℝ) hsT) (shiftIncrement hs hsT)
        (stableProcessLaw θ T : Measure (D T ℝ)) ∧
      (stableProcessLaw θ T).map (shiftIncrement hs hsT) =
        stableProcessLaw θ (T - s) := by
  have hP := isStableLevyLaw_stableProcessLaw hθ hT
  exact ⟨hP.indepFun_restrict_shiftIncrement hs hsT,
    map_shiftIncrement_stableProcessLaw hθ hT hs hsT⟩

end BGW.StableTrees
