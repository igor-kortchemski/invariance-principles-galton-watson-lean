module

public import BGWLeaves.GeneralAFunctional.TreeDensity
public import BGWLeaves.GeneralAInf.Asymptotic

/-! Event adapters and the null-mark and full-mark boundary cases. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreeEvents

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralA.MarkedLaw
open scoped ENNReal Classical

theorem ae_finite (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∀ᵐ T ∂bienaymeLaw μ.toMeasure, FiniteVertices T := by
  have hmean : (∫⁻ k : ℕ, (k : ℝ≥0∞) ∂μ.toMeasure) = 1 := by
    rw [lintegral_countable']
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using (show ∑' k : ℕ, (k : ℝ≥0∞) * μ k = 1 from hc)
  have hne' : μ.toMeasure {1} ≠ 1 := by
    simpa only [PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hne
  exact ae_finiteVertices_bienaymeLaw μ.toMeasure hmean.le hne'

theorem zetaAEvent_ae (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (n : ℕ) :
    {T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} =ᵐ[bienaymeLaw μ.toMeasure]
      {T | zetaA A T = (n : ℕ∞)} := by
  filter_upwards [ae_finite μ hc hne] with T hT
  simp only [hT, true_and]

theorem markedForestEvent_ae (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (j n : ℕ) :
    markedForestEvent A j n =ᵐ[Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure]
      {F | ∑ i, zetaA A (F i) = (n : ℕ∞)} := by
  have hf : ∀ᵐ F ∂(Measure.pi fun _ : Fin j => bienaymeLaw μ.toMeasure),
      ∀ i, FiniteVertices (F i) :=
    ae_all_iff.mpr fun _ => Measure.tendsto_eval_ae_ae.eventually (ae_finite μ hc hne)
  filter_upwards [hf] with F hF
  apply propext
  exact and_iff_right hF

theorem markedMass_eq_zetaAProb (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (n : ℕ) :
    markedMass μ A n = zetaAProb μ A n := by
  exact congrArg ENNReal.toReal (measure_congr (zetaAEvent_ae μ hc hne A n))

theorem admissible_iff (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (n : ℕ) :
    ZetaAAdmissible μ A n ↔ bienaymeLaw μ.toMeasure {T | zetaA A T = (n : ℕ∞)} ≠ 0 := by
  unfold ZetaAAdmissible
  rw [measure_congr (zetaAEvent_ae μ hc hne A n)]

/-- A positive admissible count forces positive mark probability. -/
theorem measure_ne_zero_of_admissible {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} {n : ℕ} (hn : 1 ≤ n) (ha : ZetaAAdmissible μ A n) :
    μ.toMeasure A ≠ 0 := by
  intro hzero
  exact (admissible_iff μ hc hne A n).mp ha
    (GeneralAInf.Asymptotic.zetaA_eq_zero_of_measure_zero hc hne hzero hn)

/-- The null-mark case cannot support any unbounded admissible sequence. -/
theorem measure_ne_zero_of_sequence {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} {q : ℕ → ℕ} (hqtop : Tendsto q atTop atTop)
    (hq : ∀ k, ZetaAAdmissible μ A (q k)) : μ.toMeasure A ≠ 0 := by
  obtain ⟨k, hk⟩ := (hqtop.eventually_ge_atTop 1).exists
  exact measure_ne_zero_of_admissible hc hne hk (hq k)

/-- If every offspring is marked almost surely, so is every letter of the iid exploration. -/
theorem ae_all_marks {μ : PMF ℕ} {A : Set ℕ} (hA : μ.toMeasure A = 1) :
    ∀ᵐ ω ∂(offspringSeqLaw μ).toMeasure, ∀ i, ω i ∈ A := by
  have ha : ∀ᵐ k ∂μ.toMeasure, k ∈ A :=
    (mem_ae_iff_prob_eq_one MeasurableSet.of_discrete).mpr hA
  apply ae_all_iff.mpr
  intro i
  exact (measurePreserving_eval_infinitePi (μ := fun _ : ℕ => μ.toMeasure) i).quasiMeasurePreserving.ae ha

/-- The case `μ(A)=1` includes degree sets different from `univ`. -/
theorem ae_zetaA_eq_size {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} (hA : μ.toMeasure A = 1) :
    ∀ᵐ T ∂bienaymeLaw μ.toMeasure, zetaA A T = (treeSize T : ℕ∞) := by
  rw [← first_block_law μ hc hne]
  have hm : MeasurableSet {T : LocallyFinite.Tree | FiniteVertices T ∧
      zetaA A T = (treeSize T : ℕ∞)} :=
    (ExactContour.countable_finiteVertices.mono fun _ h => h.1).measurableSet
  suffices h : ∀ᵐ T ∂((offspringSeqLaw μ).toMeasure.map (fun ω => blockLF ω 0)),
      FiniteVertices T ∧ zetaA A T = (treeSize T : ℕ∞) from h.mono (fun _ h => h.2)
  apply (ae_map_iff measurable_blockLF.eval.aemeasurable hm).mpr
  filter_upwards [ae_ladderFinite μ hc hne, ae_all_marks hA] with ω hω hmarks
  refine ⟨(blockTree ω 0).finiteVertices_toLocallyFinite, ?_⟩
  rw [zetaA_first_block hω]
  congr 1
  unfold completionMarks prefixMarks
  have hm : (seqPrefix (ladderTime ω 1) ω).countP (fun d => decide (d ∈ A)) =
      (seqPrefix (ladderTime ω 1) ω).length := by
    apply List.countP_eq_length.mpr
    intro d hd
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hd
    simpa only [decide_eq_true_eq] using hmarks i
  rw [hm]
  simp only [seqPrefix, List.length_map, List.length_range]
  change ladderTime ω 1 = treeSize (blockTree ω 0).toLocallyFinite
  rw [treeSize, ncard_present_toLocallyFinite, first_block_size hω]

/-- Equality of conditioning events in the full-mark case, including finiteness. -/
theorem full_marks_event_ae {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} (hA : μ.toMeasure A = 1) (n : ℕ) :
    {T | FiniteVertices T ∧ zetaA A T = (n : ℕ∞)} =ᵐ[bienaymeLaw μ.toMeasure] sizeEvent n := by
  filter_upwards [ae_zetaA_eq_size hc hne hA] with T hT
  simp only [mem_ofPred_eq, sizeEvent, hT, ENat.natCast_inj]
  rfl

/-- Conditioning on marks is exactly conditioning on total size when `μ(A)=1`. -/
theorem full_marks_law_eq {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {A : Set ℕ} (hA : μ.toMeasure A = 1) {n : ℕ} (hn : ZetaAAdmissible μ A n) :
    zetaATreeLaw μ A n = exactTreeLaw μ n := by
  have he := full_marks_event_ae hc hne hA n
  have hadm : Admissible μ n := by
    change bienaymeLaw μ.toMeasure (sizeEvent n) ≠ 0
    rwa [← measure_congr he]
  apply Subtype.ext
  change (zetaATreeLaw μ A n : Measure LocallyFinite.Tree) = (exactTreeLaw μ n : Measure LocallyFinite.Tree)
  rw [coe_zetaATreeLaw hn, exactTreeLaw_toMeasure μ n hadm]
  unfold ProbabilityTheory.cond
  rw [measure_congr he, Measure.restrict_congr_set he]

end BGWLeaves.GeneralAFunctional.TreeEvents
