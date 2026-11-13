module

public import BGWLeaves.GeneralAFunctional.TreePathDensity

/-! Lifting the finite-word RN identity through smaller-horizon path locality. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreePathMeasure

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGW.StableTrees.TailPair BGW.StableTrees.ExactPair BGW.Skorokhod
open BGWLeaves.GeneralAFunctional.TreePrefix BGWLeaves.GeneralAFunctional.TreeDensity
open BGWLeaves.GeneralAFunctional.TreePrefixMeasure BGWLeaves.GeneralAFunctional.TreePrefixSupport
open BGWLeaves.GeneralAFunctional.TreeAugmented BGWLeaves.GeneralAFunctional.TreeClocks
open BGWLeaves.GeneralAFunctional.TreePathDensity
open scoped ENNReal NNReal Topology Classical

local instance : MeasurableSpace (List ℕ) := ⊤
local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

theorem prefix_eq_lintegral (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) {n r m : ℕ} (hn : ZetaAAdmissible μ A n) (hmr : m < r)
    (S : Set (List ℕ)) :
    (zetaATreeLaw μ A n).toMeasure (treePrefix m ⁻¹' (S ∩ goodWords m)) =
      ∫⁻ T in treePrefix m ⁻¹' S, wordDensity μ A n r m (treePrefix m T)
        ∂(tailTreeLaw μ r).toMeasure := by
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  have hw : Measurable (wordDensity μ A n r m) := measurable_of_countable _
  have he := congrArg (fun M : Measure (List ℕ) => M S)
    (surviving_prefix_map_eq_withDensity μ hc hne A hn hmr)
  rw [Measure.restrict_apply hS, Measure.map_apply (measurable_treePrefix m)
      (hS.inter (Set.to_countable _).measurableSet), withDensity_apply _ hS,
    setLIntegral_map hS hw (measurable_treePrefix m)] at he
  exact he

theorem pathWeight_eq_wordDensity_ae (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (B : ℕ → ℝ) {n r : ℕ} (hn : ZetaAAdmissible μ A n)
    (hn0 : 0 < n) (hB : B r ≠ 0) (b : ℝ≥0) (hmr : prefixLength b r < r) :
    ∀ᵐ T ∂(tailTreeLaw μ r).toMeasure,
      wordDensity μ A n r (prefixLength b r) (treePrefix (prefixLength b r) T) =
        ENNReal.ofReal (pathWeight μ A B n r b (augmentedMap A B n r b T)) := by
  filter_upwards [ae_tail_finite μ hc hne r, ae_tail_good_prefix μ hc hne hmr,
    ae_tail_prefix_supported μ hc hne r (prefixLength b r)] with T hT hg hs
  obtain ⟨t, rfl⟩ := (exists_toLocallyFinite_iff T).mpr hT
  rw [pathWeight_augmented μ hc hne A B hn hn0 hB b t hg hs, wordDensity, ite_eq_left hg]

/-- Exact finite-measure path identity at `a<b`. The left side is restricted to
prefix survival; its missing mass tends to zero by `TreePrefixMeasure`. -/
theorem surviving_pair_eq_map_withDensity (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (B : ℕ → ℝ) {n r : ℕ} (hn : ZetaAAdmissible μ A n)
    (hn0 : 0 < n) (hB : B r ≠ 0) {a b : ℝ≥0} (hab : a ≤ b)
    (hmr : prefixLength b r < r) (hroom : ⌊(a : ℝ) * r⌋₊ + 1 ≤ prefixLength b r) :
    (((zetaATreeLaw μ A n).toMeasure.restrict
      (treePrefix (prefixLength b r) ⁻¹' goodWords (prefixLength b r))).map (treePairPath B r a)) =
      ((((tailTreeLaw μ r).map (augmentedMap A B n r b)).toMeasure.withDensity
        (fun z => ENNReal.ofReal (pathWeight μ A B n r b z))).map
          (fun z => restrictPair hab z.1)) := by
  let m := prefixLength b r
  obtain ⟨g, hg⟩ := exists_treePairPath_eq_comp_treePrefix B r a hroom
  have hgm : Measurable g := measurable_of_countable _
  have hρ : Measurable (fun z => ENNReal.ofReal (pathWeight μ A B n r b z)) :=
    ENNReal.measurable_ofReal.comp (measurable_pathWeight μ A B n r b)
  have hout : Measurable (fun z : PairSpace b × ℝ => restrictPair hab z.1) :=
    (measurable_restrictPair hab).comp measurable_fst
  ext S hS
  rw [Measure.map_apply (measurable_treePairPath B r a) hS,
    Measure.restrict_apply ((measurable_treePairPath B r a) hS),
    Measure.map_apply hout hS, withDensity_apply _ (hout hS),
    ProbabilityMeasure.toMeasure_map,
    setLIntegral_map (hout hS) hρ (measurable_augmentedMap A B n r b)]
  have hpre : treePairPath B r a ⁻¹' S = treePrefix m ⁻¹' (g ⁻¹' S) := by
    ext T
    simp only [mem_preimage, hg, m]
  have hset : augmentedMap A B n r b ⁻¹' ((fun z : PairSpace b × ℝ => restrictPair hab z.1) ⁻¹' S) =
      treePairPath B r a ⁻¹' S := by
    ext T
    simp only [mem_preimage, augmentedMap, restrictPair_treePairPath]
  rw [hset, hpre, ← Set.preimage_inter, prefix_eq_lintegral μ hc hne A hn hmr (g ⁻¹' S)]
  apply setLIntegral_congr_fun_ae ((measurable_treePrefix m) (hgm hS))
  exact (pathWeight_eq_wordDensity_ae μ hc hne A B hn hn0 hB b hmr).mono
    (fun _ he _ => he)

/-- Bounded test-integral form of the surviving path identity. -/
theorem integral_surviving_pair (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (B : ℕ → ℝ) {n r : ℕ} (hn : ZetaAAdmissible μ A n)
    (hn0 : 0 < n) (hB : B r ≠ 0) {a b : ℝ≥0} (hab : a ≤ b)
    (hmr : prefixLength b r < r) (hroom : ⌊(a : ℝ) * r⌋₊ + 1 ≤ prefixLength b r)
    (F : BoundedContinuousFunction (PairSpace a) ℝ) :
    (∫ T in treePrefix (prefixLength b r) ⁻¹' goodWords (prefixLength b r),
      F (treePairPath B r a T) ∂(zetaATreeLaw μ A n).toMeasure) =
      ∫ z, F (restrictPair hab z.1) * pathWeight μ A B n r b z
        ∂((tailTreeLaw μ r).map (augmentedMap A B n r b)).toMeasure := by
  have hm := congrArg (fun M : Measure (PairSpace a) => ∫ z, F z ∂M)
    (surviving_pair_eq_map_withDensity μ hc hne A B hn hn0 hB hab hmr hroom)
  have hout : Measurable (fun z : PairSpace b × ℝ => restrictPair hab z.1) :=
    (measurable_restrictPair hab).comp measurable_fst
  rw [integral_map (measurable_treePairPath B r a).aemeasurable F.continuous.aestronglyMeasurable,
    integral_map hout.aemeasurable F.continuous.aestronglyMeasurable] at hm
  rw [integral_withDensity_eq_integral_toReal_smul
      (f := fun z => ENNReal.ofReal (pathWeight μ A B n r b z))
      (g := fun z => F (restrictPair hab z.1))
      (ENNReal.measurable_ofReal.comp (measurable_pathWeight μ A B n r b))
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hm
  convert hm using 1
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only
    rw [ENNReal.toReal_ofReal (pathWeight_nonneg μ A B n r b z), smul_eq_mul, mul_comm]

end BGWLeaves.GeneralAFunctional.TreePathMeasure
