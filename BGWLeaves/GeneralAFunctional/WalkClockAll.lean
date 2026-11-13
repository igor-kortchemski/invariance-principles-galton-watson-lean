module

public import BGWLeaves.GeneralAFunctional.WalkClock

/-! The full-mass marking boundary for the walk clocks. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.WalkClockAll
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees
open BGWLeaves.GeneralAFunctional.WalkCyclic BGWLeaves.GeneralAFunctional.WalkVervaat
open scoped ENNReal Topology

theorem ae_all_marked {μ : PMF ℕ} {A : Set ℕ} (hA : μ.toMeasure A = 1) :
    ∀ᵐ ω ∂iidWalk μ, ∀ i, ω i ∈ A := by
  have hm : ∀ᵐ k ∂μ.toMeasure, k ∈ A := by
    rw [ae_iff]
    change μ.toMeasure Aᶜ = 0
    rw [prob_compl_eq_one_sub MeasurableSet.of_discrete, hA, tsub_self]
  exact ae_all_iff.mpr fun i =>
    (measurePreserving_eval_infinitePi (fun _ : ℕ => μ.toMeasure) i).quasiMeasurePreserving.ae hm

theorem markTime_all_marked {A : Set ℕ} {ω : ℕ → ℕ} (hω : ∀ i, ω i ∈ A) (n : ℕ) :
    IsAMarkTime A n ω n := by
  have hc (k : ℕ) : walkACount A ω k = k := by
    classical
    simp [walkACount, hω]
  exact ⟨hc n, fun k hk => by rwa [hc k]⟩

theorem markTime_exponential (μ : PMF ℕ) (A : Set ℕ) (hA0 : μ.toMeasure A ≠ 0) :
    IsOe (1 / 2) fun n : ℕ =>
      (iidWalk μ).real {ω | (¬ ∃ k, IsAMarkTime A n ω k) ∨
        ∃ k, IsAMarkTime A n ω k ∧
          1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / (μ.toMeasure A).toReal|} := by
  by_cases hA1 : μ.toMeasure A = 1
  · refine ⟨1, 1, zero_lt_one, zero_lt_one, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
    · have hz : (iidWalk μ) {ω | (¬ ∃ k, IsAMarkTime A n ω k) ∨
          ∃ k, IsAMarkTime A n ω k ∧
            1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / (μ.toMeasure A).toReal|} = 0 := by
        have hg : ∀ᵐ ω ∂iidWalk μ, ¬ ((¬ ∃ k, IsAMarkTime A n ω k) ∨
            ∃ k, IsAMarkTime A n ω k ∧
              1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / (μ.toMeasure A).toReal|) := by
          filter_upwards [ae_all_marked hA1] with ω hω
          have hm := markTime_all_marked hω n
          rintro (he | ⟨k, hk, hbad⟩)
          · exact he ⟨n, hm⟩
          · have he := IsAMarkTime.unique hk hm
            subst k
            have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
            simp only [hA1, ENNReal.toReal_one, div_self hnR, div_one, sub_self, abs_zero] at hbad
            exact (not_lt_of_ge (by positivity)) hbad
        simpa only [not_not] using (ae_iff.mp hg)
      simp only [measureReal_def, hz, ENNReal.toReal_zero]
      positivity
  · exact WalkClock.markTime_exponential μ A hA0 hA1

end BGWLeaves.GeneralAFunctional.WalkClockAll
