/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteForestPaths
public import BGW.StableTrees.DiscreteForestHeight
import Mathlib.Probability.Independence.InfinitePi

/-!
# Restart at discrete stopping times

Pre-stopped events have measurable slices determined by finitely many coordinates.
Independence of each slice from the remaining coordinates gives stopped restart.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal Classical

namespace BGW.StableTrees.DiscreteForest

private def initialSeq (n : ℕ) (ω : ℕ → ℕ) : Fin n → ℕ := fun i => ω i

private def extendSeq (n : ℕ) (a : Fin n → ℕ) : ℕ → ℕ :=
  fun i => if hi : i < n then a ⟨i, hi⟩ else 0

private theorem indep_initial_shift (μ : PMF ℕ) (n : ℕ) :
    IndepFun (initialSeq n) (shiftSeq n) (offspringSeqLaw μ).toMeasure := by
  have hi : iIndepFun (fun (i : ℕ) (ω : ℕ → ℕ) => ω i)
      (offspringSeqLaw μ).toMeasure :=
    iIndepFun_infinitePi (X := fun _ (x : ℕ) => x) (by fun_prop)
  have hd : Disjoint (Iio n) (Ici n) := by
    apply Set.disjoint_left.mpr
    intro i hlt hge
    change i < n at hlt
    change n ≤ i at hge
    omega
  have h := hi.indepFun_set (Iio n) (Ici n) hd (fun i => measurable_pi_apply i)
  have hc := h.comp
    (φ := fun a : (Iio n → ℕ) => fun i : Fin n => a ⟨i, i.isLt⟩)
    (ψ := fun a : (Ici n → ℕ) => fun i : ℕ => a ⟨n + i, Nat.le_add_right n i⟩)
    (by fun_prop) (by fun_prop)
  exact hc

private theorem preStopped_slice {N : (ℕ → ℕ) → ℕ∞} {E : Set (ℕ → ℕ)}
    (hE : PreStopped N E) (n : ℕ) :
    {ω | N ω = n ∧ ω ∈ E} = initialSeq n ⁻¹'
      {a | N (extendSeq n a) = n ∧ extendSeq n a ∈ E} := by
  ext ω
  change (N ω = n ∧ ω ∈ E) ↔
    (N (extendSeq n (initialSeq n ω)) = n ∧ extendSeq n (initialSeq n ω) ∈ E)
  have he (i : ℕ) (hi : i < n) : ω i = extendSeq n (initialSeq n ω) i := by
    simp [extendSeq, initialSeq, hi]
  constructor
  · rintro ⟨hn, hmem⟩
    have h := hE n ω (extendSeq n (initialSeq n ω)) hn he
    exact ⟨h.1, h.2.mp hmem⟩
  · rintro ⟨hn, hmem⟩
    have h := hE n (extendSeq n (initialSeq n ω)) ω hn (fun i hi => (he i hi).symm)
    exact ⟨h.1, h.2.mp hmem⟩

private theorem measurableSet_preStopped_slice {N : (ℕ → ℕ) → ℕ∞}
    {E : Set (ℕ → ℕ)} (hE : PreStopped N E) (n : ℕ) :
    MeasurableSet {ω | N ω = n ∧ ω ∈ E} := by
  rw [preStopped_slice hE n]
  exact (Set.to_countable _).measurableSet.preimage (by unfold initialSeq; fun_prop)

/-- (Stopped iid restart, finite guard) For an a.s. finite stopping time `N`, a pre-`N`
event `E` and a measurable `A`, the restarted sequence `shiftSeq N ω` is independent of `E`
and has the law `P`.  Consequence of the product law (item 2 of the plan). -/
theorem stoppedRestart (μ : PMF ℕ) (N : (ℕ → ℕ) → ℕ∞) (hN : IsSeqStoppingTime N)
    (hfin : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, N ω ≠ ⊤)
    {E : Set (ℕ → ℕ)} (hE : PreStopped N E) {A : Set (ℕ → ℕ)} (hA : MeasurableSet A) :
    (offspringSeqLaw μ).toMeasure
        (E ∩ {ω | ∃ n : ℕ, N ω = n ∧ shiftSeq n ω ∈ A}) =
      (offspringSeqLaw μ).toMeasure E * (offspringSeqLaw μ).toMeasure A := by
  have hstop : PreStopped N E := fun n ω ω' hn he =>
    ⟨(hN n ω ω' hn he).1, (hE n ω ω' hn he).2⟩
  let P := (offspringSeqLaw μ).toMeasure
  let C (n : ℕ) := {ω | N ω = n ∧ ω ∈ E}
  have hC (n : ℕ) : MeasurableSet (C n) := measurableSet_preStopped_slice hstop n
  have hdis : Pairwise (fun i j => Disjoint (C i) (C j)) := by
    intro i j hij
    exact Set.disjoint_left.mpr fun ω hi hj => hij (ENat.natCast_inj.mp (hi.1.symm.trans hj.1))
  have hCE : (⋃ n, C n) =ᵐ[P] E := by
    filter_upwards [hfin] with ω hω
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hω
    simp only [mem_iUnion, C, mem_ofPred_eq]
    apply propext
    exact ⟨fun ⟨_, _, he⟩ => he, fun he => ⟨n, hn.symm, he⟩⟩
  have hslice (n : ℕ) : P (C n ∩ shiftSeq n ⁻¹' A) = P (C n) * P A := by
    have h := (indep_initial_shift μ n).measure_inter_preimage_eq_mul _ _
      ((Set.to_countable _).measurableSet : MeasurableSet
        {a | N (extendSeq n a) = n ∧ extendSeq n a ∈ E}) hA
    rw [← preStopped_slice hstop n] at h
    have hshift : P (shiftSeq n ⁻¹' A) = P A := by
      rw [← Measure.map_apply (measurable_shiftSeq n) hA, map_shiftSeq_offspringSeqLaw]
    exact h.trans (congrArg (fun x => P (C n) * x) hshift)
  have hmain : E ∩ {ω | ∃ n : ℕ, N ω = n ∧ shiftSeq n ω ∈ A} =
      ⋃ n, C n ∩ shiftSeq n ⁻¹' A := by
    ext ω
    simp only [mem_inter_iff, mem_ofPred_eq, mem_iUnion, mem_preimage, C]
    aesop
  rw [hmain, measure_iUnion (fun i j hij => (hdis hij).mono inter_subset_left inter_subset_left)
    (fun n => (hC n).inter ((measurable_shiftSeq n) hA))]
  change (∑' n, P (C n ∩ shiftSeq n ⁻¹' A)) = P E * P A
  simp_rw [hslice]
  rw [ENNReal.tsum_mul_right, ← measure_iUnion hdis hC, measure_congr hCE]

/-- (Regeneration of the height at a stopping time) For `N` a.s. finite stopping time and `E`
pre-`N`, the height seen from `N` is independent of `E` and has the law of the height. -/
theorem stoppedRestart_height (μ : PMF ℕ) (N : (ℕ → ℕ) → ℕ∞) (hN : IsSeqStoppingTime N)
    (hfin : ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, N ω ≠ ⊤)
    {E : Set (ℕ → ℕ)} (hE : PreStopped N E) {A : Set (ℕ → ℤ)} (hA : MeasurableSet A) :
    (offspringSeqLaw μ).toMeasure
        (E ∩ {ω | ∃ n : ℕ, N ω = n ∧ (fun k => shiftedHeight ω n k) ∈ A}) =
      (offspringSeqLaw μ).toMeasure E *
        (offspringSeqLaw μ).toMeasure {ω | (fun k => (forestHeight ω k : ℤ)) ∈ A} := by
  have hm : Measurable (fun ω k => (forestHeight ω k : ℤ)) :=
    Measurable.of_eval fun k => (measurable_of_countable (fun x : ℕ => (x : ℤ))).comp
      (measurable_forestHeight k)
  simp_rw [shiftedHeight_eq]
  exact stoppedRestart μ N hN hfin hE (hm hA)

end BGW.StableTrees.DiscreteForest
