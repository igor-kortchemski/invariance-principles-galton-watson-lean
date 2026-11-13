module

public import BGWLeaves.GeneralA.MarkedTime

/-! The exact span of the marked-time law, including unmarked zero and a null
complement of the marking set. -/

@[expose] public section

namespace BGWLeaves.GeneralA.MarkedSpan

open MeasureTheory ProbabilityTheory BGW BGW.StableTrees BGWLeaves.StableAnalysis
open MarkedWalk Regroup MarkedTime
open scoped ENNReal

private instance markedStep_finite (μ : PMF ℕ) (A : Set ℕ) :
    IsFiniteMeasure (markedStep (fun k => μ k) A) := by
  rw [markedStep_eq_map_restrict]
  infer_instance

private instance unmarkedStep_finite (μ : PMF ℕ) (A : Set ℕ) :
    IsFiniteMeasure (unmarkedStep (fun k => μ k) A) := by unfold unmarkedStep; infer_instance

private instance walk_sfinite (ν : Measure ℤ) [SFinite ν] (n : ℕ) : SFinite (intWalk ν n) := by
  induction n with
  | zero => simp only [intWalk]; infer_instance
  | succ n ih => simpa only [intWalk] using (inferInstance : SFinite ((intWalk ν n).conv ν))

private theorem walk_dvd (ν : Measure ℤ) [SFinite ν] (d : ℕ)
    (hν : ∀ᵐ z ∂ν, (d : ℤ) ∣ z) (n : ℕ) : ∀ᵐ z ∂intWalk ν n, (d : ℤ) ∣ z := by
  induction n with
  | zero => simp [intWalk]
  | succ n ih =>
    rw [intWalk, Measure.conv, ae_map_iff (by fun_prop) MeasurableSet.of_discrete]
    apply (Measure.ae_prod_iff_ae_ae MeasurableSet.of_discrete).2
    filter_upwards [ih] with x hx
    filter_upwards [hν] with y hy
    exact dvd_add hx hy

private theorem blockLaw_ae_dvd_iff (α β : Measure ℤ) [SFinite α] [SFinite β]
    (hα : α Set.univ ≠ 0) (d : ℕ) (r : ℤ) :
    (∀ᵐ z ∂blockLaw α β, (d : ℤ) ∣ z - r) ↔
      (∀ᵐ z ∂α, (d : ℤ) ∣ z - r) ∧ (∀ᵐ z ∂β, (d : ℤ) ∣ z) := by
  have hs : blockLaw α β = Measure.sum fun k : ℕ => α.conv (intWalk β k) := by
    rw [blockLaw, conv_sum_right]
  constructor
  · intro h
    have hαle : α ≤ blockLaw α β := by
      rw [hs]
      simpa [intWalk] using (Measure.le_sum (fun k : ℕ => α.conv (intWalk β k)) 0)
    have hαβle : α.conv β ≤ blockLaw α β := by
      rw [hs]
      simpa [intWalk] using (Measure.le_sum (fun k : ℕ => α.conv (intWalk β k)) 1)
    have ha := h.filter_mono (ae_mono hαle)
    have hab := h.filter_mono (ae_mono hαβle)
    have hex : ∃ a : ℤ, α {a} ≠ 0 := by
      by_contra h
      push Not at h
      have hz : α = 0 := Measure.ext_of_singleton (fun a => by simpa using h a)
      exact hα (by rw [hz]; simp)
    obtain ⟨a, ha0⟩ := hex
    have har := (ae_iff_of_countable.mp ha) a ha0
    rw [Measure.conv, ae_map_iff (by fun_prop) MeasurableSet.of_discrete,
      Measure.ae_prod_iff_ae_ae MeasurableSet.of_discrete] at hab
    have hb := (ae_iff_of_countable.mp hab) a ha0
    refine ⟨ha, ?_⟩
    filter_upwards [hb] with b hbr
    convert dvd_sub hbr har using 1; ring
  · rintro ⟨ha, hb⟩
    rw [hs, Measure.ae_sum_iff]
    intro k
    rw [Measure.conv, ae_map_iff (by fun_prop) MeasurableSet.of_discrete]
    apply (Measure.ae_prod_iff_ae_ae MeasurableSet.of_discrete).2
    filter_upwards [ha] with a har
    filter_upwards [walk_dvd β d hb k] with b hbr
    convert dvd_add har hbr using 1; ring

private theorem markedStep_ae_dvd_iff (μ : PMF ℕ) (A : Set ℕ) (d : ℕ) (r : ℤ) :
    (∀ᵐ z ∂markedStep (fun k => μ k) A, (d : ℤ) ∣ z - r) ↔
      ∀ k : ℕ, μ k ≠ 0 → k ∈ A → (d : ℤ) ∣ (k : ℤ) - 1 - r := by
  rw [markedStep_eq_map_restrict,
    ae_map_iff (by fun_prop) MeasurableSet.of_discrete,
    ae_restrict_iff' MeasurableSet.of_discrete, ae_iff_of_countable]
  simp only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)]

/-- The corrected arithmetic factor is exactly the span of the marked-time law. -/
theorem blockLaw_span {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) :
    let ν := blockLaw (markedStep (fun k => μ k) A) (unmarkedStep (fun k => μ k) A)
    HasSpan ν (arithFactor μ A) ∧ ∀ᵐ z ∂ν, (arithFactor μ A : ℤ) ∣ z - (-1) := by
  have hmass : markedStep (fun k => μ k) A Set.univ ≠ 0 := by rw [markedStep_mass]; exact hA
  have hα : ∀ᵐ z ∂markedStep (fun k => μ k) A, (arithFactor μ A : ℤ) ∣ z - (-1) := by
    apply (markedStep_ae_dvd_iff μ A (arithFactor μ A) (-1)).2
    intro k hk hkA
    simpa using Arithmetic.arithFactor_dvd hc hne (A := A) ⟨k, hk, Or.inl ⟨hkA, rfl⟩⟩
  have hβ : ∀ᵐ z ∂unmarkedStep (fun k => μ k) A, (arithFactor μ A : ℤ) ∣ z := by
    have h := (markedStep_ae_dvd_iff μ Aᶜ (arithFactor μ A) 0).2 (by
      intro k hk hkA
      simpa using Arithmetic.arithFactor_dvd hc hne (A := A) ⟨k, hk, Or.inr ⟨hkA, rfl⟩⟩)
    simpa [unmarkedStep] using h
  have hs := (blockLaw_ae_dvd_iff _ _ hmass (arithFactor μ A) (-1)).2 ⟨hα, hβ⟩
  refine ⟨⟨Arithmetic.arithFactor_pos hc hne A, ⟨-1, hs⟩, ?_⟩, hs⟩
  rintro d ⟨r, hr⟩
  obtain ⟨ha, hb⟩ := (blockLaw_ae_dvd_iff _ _ hmass d r).1 hr
  have hb' : ∀ᵐ z ∂markedStep (fun k => μ k) Aᶜ, (d : ℤ) ∣ z - 0 := by
    simpa [unmarkedStep] using hb
  have hcmem := (markedStep_ae_dvd_iff μ Aᶜ d 0).1 hb'
  have hamem := (markedStep_ae_dvd_iff μ A d r).1 ha
  have hzero := LeafMass.Arithmetic.mu_zero_ne_zero hc hne
  by_cases h0 : 0 ∈ A
  · have hr0 := hamem 0 hzero h0
    apply Arithmetic.dvd_arithFactor hc hne A
    rintro s ⟨k, hk, ⟨hkA, rfl⟩ | ⟨hkA, rfl⟩⟩
    · have hd := hamem k hk hkA
      convert dvd_sub hd hr0 using 1; ring
    · simpa using hcmem k hk hkA
  · have hd : (d : ℤ) ∣ (-1 : ℤ) := by simpa using hcmem 0 hzero h0
    have hd' : (d : ℤ) ∣ (1 : ℤ) := by simpa using dvd_neg.mp hd
    have hd1 : d = 1 := Nat.dvd_one.mp (Int.natCast_dvd_natCast.mp hd')
    simp [hd1]

end BGWLeaves.GeneralA.MarkedSpan
