module

public import BGWLeaves.GeneralAFunctional.WalkVervaat
public import BGWLeaves.Vervaat.MarkTime
public import BGWLeaves.Vervaat.TimeReversal
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-! Exponential concentration of the arbitrary-mark walk clock. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.WalkClock

open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees
open BGWLeaves.GeneralAFunctional.WalkCyclic BGWLeaves.GeneralAFunctional.WalkVervaat
open scoped ENNReal Topology

noncomputable section
attribute [local instance] Classical.propDecidable

/-- The zero/one law obtained by recording whether an offspring is marked. -/
def indicatorLaw (μ : PMF ℕ) (A : Set ℕ) : PMF ℕ :=
  μ.map (fun a => if a ∈ A then 0 else 1)

theorem indicatorLaw_zero (μ : PMF ℕ) (A : Set ℕ) :
    indicatorLaw μ A 0 = μ.toMeasure A := by
  have he : (fun a : ℕ => if a ∈ A then 0 else 1) ⁻¹' {0} = A := by
    ext a
    simp
  rw [← PMF.toMeasure_apply_singleton (indicatorLaw μ A) 0 (measurableSet_singleton _)]
  change (μ.map (fun a => if a ∈ A then 0 else 1)).toMeasure {0} = _
  rw [← PMF.toMeasure_map (fun a : ℕ => if a ∈ A then 0 else 1) μ measurable_from_top,
    Measure.map_apply measurable_from_top (measurableSet_singleton _), he]

theorem map_markIndicator (μ : PMF ℕ) (A : Set ℕ) :
    (iidWalk μ).map (markIndicator A) = iidWalk (indicatorLaw μ A) := by
  unfold iidWalk markIndicator
  rw [Measure.infinitePi_map_pi (f := fun (_ : ℕ) (a : ℕ) => if a ∈ A then 0 else 1)
    _ (fun _ => measurable_from_top)]
  congr 1
  funext i
  exact PMF.toMeasure_map (fun a : ℕ => if a ∈ A then 0 else 1) μ measurable_from_top

theorem isMarkTime_indicator_iff (A : Set ℕ) (n : ℕ) (ω : ℕ → ℕ) (k : ℕ) :
    IsMarkTime n (markIndicator A ω) k ↔ IsAMarkTime A n ω k := by
  simp only [IsMarkTime, IsAMarkTime, walkLeafCount_markIndicator]

/-- G: the error probability in `T⁽ᴬ⁾ₙ/n → 1/μ(A)` decays exponentially in `√n`.
The event explicitly includes a missing stopping time. -/
theorem markTime_exponential (μ : PMF ℕ) (A : Set ℕ) (hA0 : μ.toMeasure A ≠ 0)
    (hA1 : μ.toMeasure A ≠ 1) :
    IsOe (1 / 2) fun n : ℕ =>
      (iidWalk μ).real {ω | (¬ ∃ k, IsAMarkTime A n ω k) ∨
        ∃ k, IsAMarkTime A n ω k ∧
          1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / (μ.toMeasure A).toReal|} := by
  have ht := Vervaat.MarkTime.lem_CVf2_i (indicatorLaw μ A)
    (by rwa [indicatorLaw_zero]) (by rwa [indicatorLaw_zero])
  have he (n : ℕ) :
      (iidWalk (indicatorLaw μ A)).real
        {ω | (¬ ∃ k, IsMarkTime n ω k) ∨
          ∃ k, IsMarkTime n ω k ∧
            1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / (indicatorLaw μ A 0).toReal|} =
      (iidWalk μ).real {ω | (¬ ∃ k, IsAMarkTime A n ω k) ∨
        ∃ k, IsAMarkTime A n ω k ∧
          1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / (μ.toMeasure A).toReal|} := by
    rw [← map_markIndicator μ A, measureReal_def, Measure.map_apply
      (measurable_markIndicator A)]
    · simp only [Set.preimage_ofPred_eq, isMarkTime_indicator_iff, indicatorLaw_zero,
        measureReal_def]
    · have hm (k : ℕ) : MeasurableSet {ω : ℕ → ℕ | IsMarkTime n ω k} := by
        have he : {ω : ℕ → ℕ | IsMarkTime n ω k} =
            {ω | walkLeafCount ω k = n} ∩
              ⋂ q ∈ Finset.range k, {ω | walkLeafCount ω q < n} := by
          ext ω
          simp [IsMarkTime]
        rw [he]
        exact ((Vervaat.TimeReversal.measurable_walkLeafCount k) (measurableSet_singleton _)).inter
          (Finset.measurableSet_biInter _ fun q _ =>
            (Vervaat.TimeReversal.measurable_walkLeafCount q) (MeasurableSet.of_discrete (s := Set.Iio n)))
      simp only [Set.ofPred_or, ← Set.compl_ofPred, Set.ofPred_exists]
      refine ((MeasurableSet.iUnion hm).compl).union ?_
      exact MeasurableSet.iUnion fun (k : ℕ) =>
        (hm k).inter (MeasurableSet.const _)
  simpa only [← he, iidWalk] using ht

/-- Positive mark mass suffices for every mark time to be finite almost surely,
including the case where every offspring is marked. -/
theorem ae_exists_aMarkTime (μ : PMF ℕ) (A : Set ℕ) (hA : μ.toMeasure A ≠ 0) :
    ∀ᵐ ω ∂iidWalk μ, ∀ n, ∃ k, IsAMarkTime A n ω k := by
  have ht := Vervaat.MarkTime.ae_exists_markTime (indicatorLaw μ A)
    (by rwa [indicatorLaw_zero])
  change ∀ᵐ ω ∂iidWalk (indicatorLaw μ A), ∀ n, ∃ k, IsMarkTime n ω k at ht
  have hp : MeasurePreserving (markIndicator A) (iidWalk μ) (iidWalk (indicatorLaw μ A)) :=
    ⟨measurable_markIndicator A, map_markIndicator μ A⟩
  have h := hp.quasiMeasurePreserving.ae ht
  simpa only [isMarkTime_indicator_iff] using h

end
end BGWLeaves.GeneralAFunctional.WalkClock
