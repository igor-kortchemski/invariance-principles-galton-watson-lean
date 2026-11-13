module

public import BGWLeaves.GeneralAFunctional.TreePathMeasure
public import BGWLeaves.GeneralAFunctional.TreePathLimit

/-! Integrability and limiting mass of the augmented path weights. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreePathMass

open MeasureTheory ProbabilityTheory Filter Set BGW
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGW.StableTrees.TailPair BGW.Skorokhod
open BGWLeaves.GeneralAFunctional.TreePrefixMeasure BGWLeaves.GeneralAFunctional.TreeSurvival
open BGWLeaves.GeneralAFunctional.TreeAugmented BGWLeaves.GeneralAFunctional.TreeClocks
open BGWLeaves.GeneralAFunctional.TreePathDensity BGWLeaves.GeneralAFunctional.TreePathMeasure
open BGWLeaves.GeneralAFunctional.TreePathLimit
open scoped ENNReal NNReal Topology Classical

local instance : MeasurableSpace (List ℕ) := ⊤
local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

theorem lintegral_pathWeight_eq_mass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (B : ℕ → ℝ) {n r : ℕ} (hn : ZetaAAdmissible μ A n)
    (hn0 : 0 < n) (hB : B r ≠ 0) (b : ℝ≥0) (hm0 : 0 < prefixLength b r)
    (hmr : prefixLength b r < r) :
    (∫⁻ z, ENNReal.ofReal (pathWeight μ A B n r b z)
      ∂((tailTreeLaw μ r).map (augmentedMap A B n r b)).toMeasure) =
      (zetaATreeLaw μ A n).toMeasure
        (treePrefix (prefixLength b r) ⁻¹' goodWords (prefixLength b r)) := by
  have he := surviving_pair_eq_map_withDensity μ hc hne A B hn hn0 hB (a := 0) (b := b)
    (show (0 : ℝ≥0) ≤ b from zero_le) hmr (by simpa only [NNReal.coe_zero, zero_mul, Nat.floor_zero, zero_add] using (show 1 ≤ prefixLength b r by omega))
  have hm := congrArg (fun M : Measure (PairSpace 0) => M univ) he
  have hout : Measurable (fun z : PairSpace b × ℝ => restrictPair (show (0 : ℝ≥0) ≤ b from zero_le) z.1) :=
    (measurable_restrictPair _).comp measurable_fst
  rw [Measure.map_apply (measurable_treePairPath B r 0) MeasurableSet.univ,
    Set.preimage_univ, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
    Measure.map_apply hout MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at hm
  exact hm.symm

theorem integrable_pathWeight (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (B : ℕ → ℝ) {n r : ℕ} (hn : ZetaAAdmissible μ A n)
    (hn0 : 0 < n) (hB : B r ≠ 0) (b : ℝ≥0) (hm0 : 0 < prefixLength b r)
    (hmr : prefixLength b r < r) :
    Integrable (pathWeight μ A B n r b)
      ((tailTreeLaw μ r).map (augmentedMap A B n r b)).toMeasure := by
  apply (lintegral_ofReal_ne_top_iff_integrable (measurable_pathWeight μ A B n r b).aestronglyMeasurable
    (ae_of_all _ (pathWeight_nonneg μ A B n r b))).mp
  rw [lintegral_pathWeight_eq_mass μ hc hne A B hn hn0 hB b hm0 hmr]
  exact measure_ne_top _ _

theorem integral_pathWeight_eq_mass (μ : PMF ℕ) (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (A : Set ℕ) (B : ℕ → ℝ) {n r : ℕ} (hn : ZetaAAdmissible μ A n)
    (hn0 : 0 < n) (hB : B r ≠ 0) (b : ℝ≥0) (hm0 : 0 < prefixLength b r)
    (hmr : prefixLength b r < r) :
    (∫ z, pathWeight μ A B n r b z
      ∂((tailTreeLaw μ r).map (augmentedMap A B n r b)).toMeasure) =
      (zetaATreeLaw μ A n).toMeasure.real
        (treePrefix (prefixLength b r) ⁻¹' goodWords (prefixLength b r)) := by
  have hm := congrArg ENNReal.toReal (lintegral_pathWeight_eq_mass μ hc hne A B hn hn0 hB b hm0 hmr)
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_pathWeight μ hc hne A B hn hn0 hB b hm0 hmr)
    (ae_of_all _ (pathWeight_nonneg μ A B n r b)),
    ENNReal.toReal_ofReal (integral_nonneg (pathWeight_nonneg μ A B n r b))] at hm
  exact hm

/-- Suppress finitely many small clocks, where the prefix may be empty.
This changes no asymptotic statement and ensures integrability at every index. -/
noncomputable def safeWeight (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ) (n r : ℕ) (b : ℝ≥0)
    (z : PairSpace b × ℝ) : ℝ :=
  if 0 < n ∧ 0 < r ∧ 0 < prefixLength b r ∧ prefixLength b r < r then
    pathWeight μ A B n r b z else 0

theorem measurable_safeWeight (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ) (n r : ℕ) (b : ℝ≥0) :
    Measurable (safeWeight μ A B n r b) := by
  unfold safeWeight
  split_ifs
  · exact measurable_pathWeight μ A B n r b
  · exact measurable_const

theorem safeWeight_nonneg (μ : PMF ℕ) (A : Set ℕ) (B : ℕ → ℝ) (n r : ℕ) (b : ℝ≥0)
    (z : PairSpace b × ℝ) : 0 ≤ safeWeight μ A B n r b z := by
  unfold safeWeight
  split_ifs
  · exact pathWeight_nonneg μ A B n r b z
  · rfl

theorem integrable_safeWeight {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ} (h : StableDomain μ θ B)
    (A : Set ℕ) {n : ℕ} (hn : ZetaAAdmissible μ A n) (b : ℝ≥0) :
    Integrable (safeWeight μ A B n (explorationIndex μ A n) b)
      (augmentedTailLaw μ A B n b).toMeasure := by
  unfold safeWeight
  split_ifs with hi
  · exact integrable_pathWeight μ h.critical h.nondegenerate A B hn hi.1
      (h.pos _ hi.2.1).ne' b hi.2.2.1 hi.2.2.2
  · exact integrable_zero _ _ _

theorem eventually_safeWeight {μ : PMF ℕ} {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) {b : ℝ≥0} (hb0 : 0 < b) (hb1 : b < 1)
    (B : ℕ → ℝ) :
    ∀ᶠ i in atTop, safeWeight μ A B (q i) (explorationIndex μ A (q i)) b =
      pathWeight μ A B (q i) (explorationIndex μ A (q i)) b := by
  have hr := (explorationIndex_atTop hA).comp hq
  have hm : Tendsto (fun i => prefixLength b (explorationIndex μ A (q i))) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      ((tendsto_natCast_atTop_atTop.comp hr).const_mul_atTop hb0)
  filter_upwards [hq.eventually_ge_atTop 1, hr.eventually_ge_atTop 1, hm.eventually_ge_atTop 1]
    with i hqi hri hmi
  change 1 ≤ explorationIndex μ A (q i) at hri
  funext z
  unfold safeWeight
  rw [ite_eq_left ⟨by omega, by omega, by omega, prefixLength_lt hb1 (by omega)⟩]

theorem safeWeight_mass_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) {A : Set ℕ} (hA : μ.toMeasure A ≠ 0)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) (hqadm : ∀ i, ZetaAAdmissible μ A (q i))
    {b : ℝ≥0} (hb0 : 0 < b) (hb1 : b < 1) :
    Tendsto (fun i => ∫ z, safeWeight μ A B (q i) (explorationIndex μ A (q i)) b z
      ∂(augmentedTailLaw μ A B (q i) b).toMeasure) atTop (𝓝 1) := by
  have hp : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have hl := (prefixLength_exploration_ratio hA b).comp hq
  have hs : (b : ℝ) / (μ.toMeasure A).toReal < 1 / (μ.toMeasure A).toReal :=
    div_lt_div_of_pos_right hb1 hp
  have hmissing := missing_prefix_mass_tendsto h.critical h.nondegenerate ⟨B, h⟩ hA hq hqadm hl hs
  have ht := (tendsto_const_nhds (x := (1 : ℝ))).sub hmissing
  simp only [sub_zero] at ht
  apply ht.congr'
  have hr := (explorationIndex_atTop hA).comp hq
  have hm : Tendsto (fun i => prefixLength b (explorationIndex μ A (q i))) atTop atTop :=
    tendsto_nat_floor_atTop.comp
      ((tendsto_natCast_atTop_atTop.comp hr).const_mul_atTop hb0)
  filter_upwards [eventually_safeWeight hA hq hb0 hb1 B, hq.eventually_ge_atTop 1,
    hr.eventually_ge_atTop 1, hm.eventually_ge_atTop 1] with i hi hqi hri hmi
  change 1 ≤ explorationIndex μ A (q i) at hri
  rw [hi]
  dsimp only [augmentedTailLaw]
  rw [integral_pathWeight_eq_mass μ h.critical h.nondegenerate A B (hqadm i)
    (by omega) (h.pos _ (by omega)).ne' b (by omega) (prefixLength_lt hb1 (by omega))]
  have hS : MeasurableSet (treePrefix (prefixLength b (explorationIndex μ A (q i))) ⁻¹'
      goodWords (prefixLength b (explorationIndex μ A (q i)))) :=
    (measurable_treePrefix _) (Set.to_countable _).measurableSet
  have hc := probReal_add_probReal_compl (μ := (zetaATreeLaw μ A (q i)).toMeasure) hS
  simp only [Set.preimage_compl]
  linarith

end BGWLeaves.GeneralAFunctional.TreePathMass
