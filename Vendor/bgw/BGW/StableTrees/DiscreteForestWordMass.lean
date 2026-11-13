/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestCylinder
public import BGW.StableTrees.DiscreteForestRestart

/-!
# Masses of finite offspring words

A fixed initial word has the product of its coordinate masses. Fixed-time
suffixes are independent of that word, and their walk has the scalar walk law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal Classical

namespace BGW.StableTrees.DiscreteForest

/-- An initial degree-word cylinder has the product of its coordinate masses. -/
theorem seqPrefix_mass (μ : PMF ℕ) (a : List ℕ) :
    (offspringSeqLaw μ).toMeasure {ω | seqPrefix a.length ω = a} = (a.map μ).prod := by
  have heq : {ω | seqPrefix a.length ω = a} =
      (fun ω (i : Fin a.length) => ω i) ⁻¹' {a.get} := by
    ext ω
    change seqPrefix a.length ω = a ↔ (fun i : Fin a.length => ω i) = a.get
    constructor
    · intro h
      funext i
      have hv := congrArg (fun l : List ℕ => l[i.val]?) h
      simpa [seqPrefix, i.isLt] using hv
    · intro h
      rw [seqPrefix_eq_ofFn, h, List.ofFn_get]
  rw [heq, ← Measure.map_apply (by fun_prop) (measurableSet_singleton _),
    map_offspringSeqLaw_initial, Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]
  rw [← List.prod_ofFn]
  change (List.ofFn ((fun d : ℕ => μ d) ∘ a.get)).prod = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- The scalar walk law is the law of the integer walk coordinate. -/
theorem map_offspringSeqLaw_walk (μ : PMF ℕ) (n : ℕ) :
    (offspringSeqLaw μ).toMeasure.map (fun ω => walk ω n) = walkLaw μ n := by
  rw [Scalar.walkLaw_eq_map_offspring_sum, ← map_offspringSeqLaw_initial,
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext ω
  exact (Fin.sum_univ_eq_sum_range (fun i : ℕ => (ω i : ℤ) - 1) n).symm

/-- A degree-word cylinder is independent of the suffix after the word. -/
theorem seqPrefix_inter_shift_mass (μ : PMF ℕ) (a : List ℕ)
    {A : Set (ℕ → ℕ)} (hA : MeasurableSet A) :
    (offspringSeqLaw μ).toMeasure
        ({ω | seqPrefix a.length ω = a} ∩ shiftSeq a.length ⁻¹' A) =
      (a.map μ).prod * (offspringSeqLaw μ).toMeasure A := by
  have hN : IsSeqStoppingTime (fun _ : ℕ → ℕ => (a.length : ℕ∞)) :=
    fun _ _ _ hn _ => ⟨hn, Iff.rfl⟩
  have hE : PreStopped (fun _ : ℕ → ℕ => (a.length : ℕ∞))
      {ω | seqPrefix a.length ω = a} := by
    intro n ω ω' hn he
    have hlen : a.length = n := ENat.natCast_inj.mp hn
    subst n
    refine ⟨rfl, ?_⟩
    have hp : seqPrefix a.length ω = seqPrefix a.length ω' :=
      List.map_congr_left fun i hi => he i (List.mem_range.mp hi)
    change (seqPrefix a.length ω = a) ↔ (seqPrefix a.length ω' = a)
    rw [hp]
  have h := stoppedRestart μ (fun _ => (a.length : ℕ∞)) hN
    (ae_of_all _ fun _ => by simp) hE hA
  have hs : {ω | ∃ n : ℕ, (a.length : ℕ∞) = n ∧ shiftSeq n ω ∈ A} =
      shiftSeq a.length ⁻¹' A := by
    ext ω
    change (∃ n : ℕ, (a.length : ℕ∞) = n ∧ shiftSeq n ω ∈ A) ↔ shiftSeq a.length ω ∈ A
    constructor
    · rintro ⟨n, hn, ha⟩
      have hn' := ENat.natCast_inj.mp hn
      subst n
      exact ha
    · intro ha
      exact ⟨a.length, rfl, ha⟩
  rw [hs, seqPrefix_mass] at h
  exact h

/-- The walk value of a degree word is the sum of its integer increments. -/
theorem prefixWalk_eq_sum_steps (a : List ℕ) :
    prefixWalk a = (a.map (fun d : ℕ => (d : ℤ) - 1)).sum := by
  simp only [prefixWalk, bind_pure_comp]
  change ((a.map (fun d : ℕ => (d : ℤ))).map (fun d : ℤ => d - 1)).sum = _
  rw [List.map_map]
  rfl

end BGW.StableTrees.DiscreteForest
