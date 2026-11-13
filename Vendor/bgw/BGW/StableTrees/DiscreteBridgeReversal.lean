/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridgeBasic
import Mathlib.Data.Fin.Rev

/-!
# Reversal of the bridge offspring vector

Reindexing the iid product by the reversing permutation preserves its law and
the bridge event. Reversed partial sums describe the terminal window exactly.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteBridge

open BGW BGW.Skorokhod

/-- Reverse the order of the offspring counts. -/
def reverseVec {n : ℕ} (ω : Fin n → ℕ) : Fin n → ℕ := fun i => ω i.rev

/-- Reversal is a measurable involution on offspring vectors. -/
theorem measurable_reverseVec (n : ℕ) : Measurable (reverseVec (n := n)) :=
  measurable_of_countable _

/-- The Łukasiewicz word of the reversed vector is the reversed word. -/
theorem stepWord_reverseVec {n : ℕ} (ω : Fin n → ℕ) :
    stepWord (reverseVec ω) = (stepWord ω).reverse := by
  apply List.ext_getElem
  · simp [stepWord]
  · intro i hi hi'
    simp [stepWord, reverseVec, Fin.rev]
    congr 1
    apply Fin.ext
    change n - (i + 1) = n - 1 - i
    omega

/-- Reversing a vector preserves the bridge event. -/
theorem reverseVec_mem_countBridges_iff {n : ℕ} (ω : Fin n → ℕ) :
    reverseVec ω ∈ countBridges n ↔ ω ∈ countBridges n := by
  rw [← stepWord_mem_bridgeWords_iff, stepWord_reverseVec, ← stepWord_mem_bridgeWords_iff]
  simp only [bridgeWords, mem_ofPred_eq, List.length_reverse, List.mem_reverse, List.sum_reverse]

/-- Reversal preserves the iid offspring-vector law. -/
theorem map_reverseVec_offspringVec (μ : PMF ℕ) (n : ℕ) :
    (offspringVec μ n).map reverseVec = offspringVec μ n := by
  have hp := Measure.pi_map_piCongrLeft (Fin.revPerm (n := n))
    (fun _ : Fin n => μ.toMeasure)
  change (Measure.pi fun _ : Fin n => μ.toMeasure).map reverseVec =
    Measure.pi fun _ : Fin n => μ.toMeasure
  have hf : ⇑(MeasurableEquiv.piCongrLeft (fun _ : Fin n => ℕ) Fin.revPerm) =
      reverseVec := by
    funext ω i
    have hh := MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ : Fin n => ℕ)
      Fin.revPerm ω i.rev
    simpa [reverseVec] using hh
  rw [hf] at hp
  exact hp

/-- The bridge-conditioned offspring vector has the same law when reversed. -/
theorem map_reverseVec_cond_countBridges (μ : PMF ℕ) (n : ℕ) :
    ((offspringVec μ n)[|countBridges n]).map reverseVec =
      (offspringVec μ n)[|countBridges n] := by
  have hb : reverseVec ⁻¹' countBridges n = countBridges n := by
    ext ω
    exact reverseVec_mem_countBridges_iff ω
  have hm : ((offspringVec μ n)[|reverseVec ⁻¹' countBridges n]).map reverseVec =
      ((offspringVec μ n).map reverseVec)[|countBridges n] := by
    ext S hS
    rw [Measure.map_apply (measurable_reverseVec n) hS,
      cond_apply' ((measurable_reverseVec n) hS), cond_apply' hS,
      Measure.map_apply (measurable_reverseVec n) (Set.to_countable _).measurableSet,
      Measure.map_apply (measurable_reverseVec n) ((Set.to_countable _).measurableSet.inter hS),
      preimage_inter]
  simpa only [hb, map_reverseVec_offspringVec] using hm

/-- Reversed prefix sums are the full sum minus the corresponding original prefix. -/
theorem sum_take_stepWord_reverseVec {n k : ℕ} (ω : Fin n → ℕ) (hk : k ≤ n) :
    ((stepWord (reverseVec ω)).take (n - k)).sum =
      (stepWord ω).sum - ((stepWord ω).take k).sum := by
  rw [stepWord_reverseVec, List.take_reverse, List.sum_reverse]
  have hlen : (stepWord ω).length = n := by simp [stepWord]
  rw [hlen, Nat.sub_sub_self hk]
  have hs := List.sum_take_add_sum_drop (stepWord ω) k
  omega

end BGW.StableTrees.DiscreteBridge
