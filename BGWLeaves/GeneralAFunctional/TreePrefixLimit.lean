module

public import BGWLeaves.GeneralAFunctional.TreePathMass
public import BGWLeaves.GeneralAFunctional.TreeLimitWeight
public import BGWLeaves.GeneralAFunctional.TreeWeighted

/-! Joint deterministic-prefix convergence under exact arbitrary-mark conditioning. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.TreePrefixLimit

open MeasureTheory ProbabilityTheory Filter Set BGW BGWLeaves.StableAnalysis
open BGW.StableTrees BGW.StableTrees.DiscreteForest BGW.LocallyFinite
open BGW.StableTrees.TailPair BGW.Skorokhod
open BGWLeaves.GeneralAFunctional.TreeAugmented BGWLeaves.GeneralAFunctional.TreeClocks
open BGWLeaves.GeneralAFunctional.TreePathDensity BGWLeaves.GeneralAFunctional.TreePathLimit
open BGWLeaves.GeneralAFunctional.TreePathMeasure BGWLeaves.GeneralAFunctional.TreePathMass
open BGWLeaves.GeneralAFunctional.TreePrefixMeasure BGWLeaves.GeneralAFunctional.TreeSurvival
open BGWLeaves.GeneralAFunctional.TreeGoodState BGWLeaves.GeneralAFunctional.TreeLimitWeight
open BGWLeaves.GeneralAFunctional.TreeWeighted
open scoped ENNReal NNReal Topology

local instance : MeasurableSpace (List ℕ) := ⊤
local instance : MeasurableSingletonClass (List ℕ) := ⟨fun _ => trivial⟩

/-- Step E: the walk and height converge JOINTLY on each proper initial interval,
under exact `ζ_A` conditioning, on the deterministic total-size scale. -/
theorem marked_pair_prefix_tendsto {μ : PMF ℕ} {θ : ℝ} {B : ℕ → ℝ}
    (h : StableDomain μ θ B) (hap : Aperiodic μ) {A : Set ℕ}
    (hA : μ.toMeasure A ≠ 0) (hA1 : μ.toMeasure A ≠ 1)
    {q : ℕ → ℕ} (hq : Tendsto q atTop atTop) (hqadm : ∀ i, ZetaAAdmissible μ A (q i))
    (a : ℝ≥0) (ha : a ∈ Ioo (0 : ℝ≥0) 1) :
    Tendsto (fun i => (zetaATreeLaw μ A (q i)).map
      (treePairPath B (explorationIndex μ A (q i)) a)) atTop
      (𝓝 ((excLaw θ).map (restrictPair ha.2.le))) := by
  let b : ℝ≥0 := (a + 1) / 2
  have hablt : a < b := by
    change (a : ℝ) < (b : ℝ)
    dsimp [b]
    linarith [show (a : ℝ) < 1 from ha.2]
  have hb : b ∈ Ioo (0 : ℝ≥0) 1 := by
    refine ⟨ha.1.trans hablt, ?_⟩
    change (b : ℝ) < 1
    dsimp [b]
    linarith [show (a : ℝ) < 1 from ha.2]
  let r := fun i => explorationIndex μ A (q i)
  let P := fun i => augmentedTailLaw μ A B (q i) b
  let P₀ := augmentedTailLimit θ b
  let w := fun i => safeWeight μ A B (q i) (r i) b
  let w₀ := limitWeight θ b
  have hr : Tendsto r atTop atTop := (explorationIndex_atTop hA).comp hq
  have hP : Tendsto P atTop (𝓝 P₀) := augmentedTailLaw_tendsto h hap hA hA1 hq hb.1 hb.2
  have hmass : Tendsto (fun i => ∫ z, w i z ∂(P i).toMeasure) atTop (𝓝 1) :=
    safeWeight_mass_tendsto h hA hq hqadm hb.1 hb.2
  let G := goodState hablt.le
  have hG : (P₀ : Measure (PairSpace b × ℝ)) Gᶜ = 0 :=
    ae_iff.mp (ae_goodState h.alpha_mem ha.1 hablt.le hb)
  have hconv : ∀ z ∈ G, ∀ v : ℕ → PairSpace b × ℝ,
      (∀ i, v i ∈ (Set.univ : Set (PairSpace b × ℝ))) → Tendsto v atTop (𝓝 z) →
      Tendsto (fun i => w i (v i)) atTop (𝓝 (w₀ z)) := by
    intro z hz v _ hv
    have ht := pathWeight_continuousConv h hA hq hqadm hb.1 hb.2
      (continuousAt_of_leftLim_eq z.1.1 _ hz.1) hz.2.1 hz.2.2.1 hv
    have hnn := gammaA_nonneg h.alpha_mem hb.2 hz.2.1
    change Tendsto (fun i => w i (v i)) atTop (𝓝 (max (gammaA θ b (DiscreteBridge.endValue b z.1.1)) 0))
    erw [max_eq_left hnn]
    apply ht.congr'
    filter_upwards [eventually_safeWeight hA hq hb.1 hb.2 B] with i hi
    exact (congrFun hi (v i)).symm
  have hp : 0 < (μ.toMeasure A).toReal := ENNReal.toReal_pos hA (measure_ne_top _ _)
  have hmissing := missing_prefix_mass_tendsto h.critical h.nondegenerate ⟨B, h⟩ hA hq hqadm
    ((prefixLength_exploration_ratio hA b).comp hq) (div_lt_div_of_pos_right hb.2 hp)
  rw [ProbabilityMeasure.tendsto_iff_forall_integral_tendsto]
  intro F
  let test : PairSpace b × ℝ → ℝ := fun z => F (restrictPair hablt.le z.1)
  have htest : Measurable test := F.continuous.measurable.comp
    ((measurable_restrictPair hablt.le).comp measurable_fst)
  have htestb : ∀ z, |test z| ≤ ‖F‖ :=
    fun z => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (restrictPair hablt.le z.1)
  have htestc : ∀ z ∈ G, ContinuousAt test z := by
    intro z hz
    exact F.continuous.continuousAt.comp
      ((continuousAt_restrictPair hablt.le (continuousAt_of_leftLim_eq z.1.1 _ hz.2.2.2)).comp continuousAt_fst)
  have hweighted := tendsto_integral_mul_weight_test hP
    (fun i => measurable_safeWeight μ A B (q i) (r i) b) (measurable_limitWeight θ b)
    (fun i => safeWeight_nonneg μ A B (q i) (r i) b) (limitWeight_nonneg θ b)
    (fun i => integrable_safeWeight h A (hqadm i) b) hmass (integral_limitWeight h.alpha_mem hb)
    (fun _ => Set.univ) (fun _ => by simp) G hG hconv test htest htestb htestc
  rw [integral_limitWeight_restrict h.alpha_mem hablt.le hb F] at hweighted
  have hroom := hr.eventually (prefixLength_room hablt)
  have herror : Tendsto (fun i =>
      (∫ T, F (treePairPath B (r i) a T) ∂(zetaATreeLaw μ A (q i)).toMeasure) -
        ∫ z, test z * w i z ∂(P i).toMeasure) atTop (𝓝 0) := by
    have hbound := hmissing.const_mul ‖F‖
    rw [mul_zero] at hbound
    apply squeeze_zero_norm' _ hbound
    filter_upwards [hroom, hq.eventually_ge_atTop 1, hr.eventually_ge_atTop 1,
      eventually_safeWeight hA hq hb.1 hb.2 B] with i hri hqi hsize hwi
    have hrpos : 0 < r i := by omega
    have hmr := prefixLength_lt hb.2 hrpos
    have hBr : B (r i) ≠ 0 := (h.pos _ hrpos).ne'
    have he := integral_surviving_pair μ h.critical h.nondegenerate A B (hqadm i)
      (by omega) hBr hablt.le hmr hri F
    have hS : MeasurableSet (treePrefix (prefixLength b (r i)) ⁻¹' goodWords (prefixLength b (r i))) :=
      (measurable_treePrefix _) (Set.to_countable _).measurableSet
    have hInt : Integrable (fun T => F (treePairPath B (r i) a T)) (zetaATreeLaw μ A (q i)).toMeasure :=
      (F.integrable ((zetaATreeLaw μ A (q i)).toMeasure.map (treePairPath B (r i) a))).comp_measurable
        (measurable_treePairPath B (r i) a)
    have hh := integral_restrict_error hS hInt
      (fun T => by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (treePairPath B (r i) a T))
    rw [he] at hh
    change ‖_‖ ≤ _
    rw [Real.norm_eq_abs]
    change |_ - ∫ z, test z * safeWeight μ A B (q i) (r i) b z ∂(P i).toMeasure| ≤ _
    rw [hwi]
    exact hh
  have ht := herror.add hweighted
  dsimp only [w, r] at ht
  simp only [sub_add_cancel, zero_add] at ht
  apply ht.congr
  intro i
  exact (integral_map (μ := (zetaATreeLaw μ A (q i)).toMeasure)
    (measurable_treePairPath B (r i) a).aemeasurable
    F.continuous.aestronglyMeasurable).symm

end BGWLeaves.GeneralAFunctional.TreePrefixLimit
