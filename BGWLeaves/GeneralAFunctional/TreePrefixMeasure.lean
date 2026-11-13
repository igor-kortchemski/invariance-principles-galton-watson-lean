module

public import BGWLeaves.GeneralAFunctional.TreeTailPositive
public import BGWLeaves.GeneralAFunctional.TreeSurvival

/-! The exact prefix density is a finite-measure identity on surviving words.
It is deliberately not asserted to have mass one. -/

@[expose] public section

namespace BGWLeaves.GeneralAFunctional.TreePrefixMeasure

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralAFunctional.TreeEvents BGWLeaves.GeneralAFunctional.TreeSurvival
open BGWLeaves.GeneralAFunctional.TreeTailPositive
open scoped ENNReal Topology Classical

local instance : MeasurableSpace (List ℕ) := ⊤
local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

def goodWords (m : ℕ) : Set (List ℕ) := {a | a.length = m ∧ IsSurvivingPrefix a}

noncomputable def wordDensity (μ : PMF ℕ) (A : Set ℕ) (n r m : ℕ) (a : List ℕ) : ℝ≥0∞ :=
  if a ∈ goodWords m then ENNReal.ofReal (TreeDensity.prefixDensity μ A n r a) else 0

theorem prefix_atom_eq_cylinder (P : Measure LocallyFinite.Tree)
    (hP : ∀ᵐ T ∂P, FiniteVertices T) (m : ℕ) (a : List ℕ) :
    P (treePrefix m ⁻¹' {a}) = P (prefixCylinder m a) := by
  apply measure_congr
  filter_upwards [hP] with T hT
  exact propext ⟨fun ha => ⟨hT, ha⟩, fun ha => ha.2⟩

theorem ae_tail_finite (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1) (r : ℕ) :
    ∀ᵐ T ∂(tailTreeLaw μ r).toMeasure, FiniteVertices T := by
  rw [tailTreeLaw_toMeasure μ r (bienaymeLaw_sizeGeEvent_ne_zero μ hc hne r)]
  exact cond_absolutelyContinuous.ae_le (ae_finite μ hc hne)

/-- The target prefix law restricted to surviving words is the tail prefix law
weighted by the marked RN density. This identity keeps the missing mass visible. -/
theorem surviving_prefix_map_eq_withDensity (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) {n r m : ℕ} (hn : ZetaAAdmissible μ A n) (hmr : m < r) :
    (((zetaATreeLaw μ A n).toMeasure.map (treePrefix m)).restrict (goodWords m)) =
      ((tailTreeLaw μ r).toMeasure.map (treePrefix m)).withDensity (wordDensity μ A n r m) := by
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.restrict_apply (measurableSet_singleton a),
    withDensity_apply _ (measurableSet_singleton a), lintegral_singleton]
  by_cases hg : a ∈ goodWords m
  · rw [Set.inter_eq_left.mpr (Set.singleton_subset_iff.mpr hg),
      Measure.map_apply (measurable_treePrefix m) (measurableSet_singleton a),
      Measure.map_apply (measurable_treePrefix m) (measurableSet_singleton a),
      prefix_atom_eq_cylinder _ ((ae_conditioning_event hn).mono fun _ h => h.1),
      prefix_atom_eq_cylinder _ (ae_tail_finite μ hc hne r), wordDensity, ite_eq_left hg]
    have ha : a.length = m ∧ IsSurvivingPrefix a := hg
    have hreal := TreeTailPositive.markedPrefixMass_eq_density_mul μ hc hne A a n r hn
      (by omega) ha.2
    rw [ha.1] at hreal
    have hnn : 0 ≤ TreeDensity.prefixDensity μ A n r a := by
      unfold TreeDensity.prefixDensity
      apply mul_nonneg
      · exact div_nonneg (forestTail_pos μ hc hne r).le (markedMass_pos hn).le
      · apply div_nonneg
        · unfold remainingMass
          split_ifs <;> positivity
        · exact (forestTail_stack_pos μ hc hne (prefixStack_pos ha.2) _).le
    have h := congrArg ENNReal.ofReal hreal
    simp only [measureReal_def, ENNReal.ofReal_mul hnn,
      ENNReal.ofReal_toReal (measure_ne_top _ _)] at h
    exact h
  · rw [Set.disjoint_iff_inter_eq_empty.mp (Set.disjoint_singleton_left.mpr hg),
      measure_empty, wordDensity, ite_eq_right hg, zero_mul]

theorem good_prefix_of_lt_size (t : PlaneTree) {m : ℕ} (hm : m < t.size) :
    treePrefix m t.toLocallyFinite ∈ goodWords m := by
  rw [treePrefix_toLocallyFinite]
  have hl : (t.degrees.take m).length = m := by simp [List.length_take, hm.le]
  refine ⟨hl, ?_⟩
  intro i hi
  rw [hl] at hi
  change 0 ≤ prefixWalk ((t.degrees.take m).take i)
  rw [prefixWalk_eq_sum_steps, List.take_take, min_eq_left hi]
  have hh := PlaneTree.sum_take_increments_nonneg t (i := i) (by simpa using hi.trans_lt hm)
  simpa only [PlaneTree.increments, ← List.map_take] using hh

/-- The missing mass in the finite prefix density is bounded by the probability
that the conditioned tree has already finished. -/
theorem missing_prefix_mass_le {μ : PMF ℕ} {A : Set ℕ} {n m : ℕ}
    (hn : ZetaAAdmissible μ A n) :
    (zetaATreeLaw μ A n).toMeasure.real (treePrefix m ⁻¹' (goodWords m)ᶜ) ≤
      (zetaATreeLaw μ A n).toMeasure.real {T | treeSize T ≤ m} := by
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  apply measure_mono_ae
  filter_upwards [ae_conditioning_event hn] with T hT
  intro hbad
  obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff T).mpr hT.1
  rw [treeSize, ncard_present_toLocallyFinite]
  by_contra h
  exact hbad (good_prefix_of_lt_size t (by omega))

/-- Along admissible counts the missing mass vanishes for every deterministic
prefix clock shorter than the asymptotic total size. -/
theorem missing_prefix_mass_tendsto {μ : PMF ℕ} {θ : ℝ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hDA : ∃ a, StableDomain μ θ a)
    {A : Set ℕ} (hA : μ.toMeasure A ≠ 0) {q : ℕ → ℕ}
    (hqtop : Tendsto q atTop atTop) (hq : ∀ k, ZetaAAdmissible μ A (q k))
    {l : ℕ → ℕ} {s : ℝ}
    (hl : Tendsto (fun k => (l k : ℝ) / q k) atTop (𝓝 s))
    (hs : s < 1 / (μ.toMeasure A).toReal) :
    Tendsto (fun k => (zetaATreeLaw μ A (q k)).toMeasure.real
      (treePrefix (l k) ⁻¹' (goodWords (l k))ᶜ)) atTop (𝓝 0) :=
  squeeze_zero (fun _ => measureReal_nonneg) (fun k => missing_prefix_mass_le (hq k))
    (small_size_probability_tendsto hc hne hDA hA hqtop hq hl hs)

end BGWLeaves.GeneralAFunctional.TreePrefixMeasure
