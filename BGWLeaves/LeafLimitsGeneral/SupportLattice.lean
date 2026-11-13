module

public import BGWLeaves.LeafLimitsGeneral.DensityLattice
public import BGWLeaves.LeafLimitsGeneral.BridgeLattice
public import BGWLeaves.Vervaat.Discrete

/-! Arithmetic support of stopped prefixes, with the two clock conventions explicit. -/

@[expose] public section
namespace BGWLeaves.LeafLimitsGeneral.SupportLattice
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.GeneralA MarkedLaw
open scoped ENNReal NNReal Topology

private theorem step_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {k : ℕ} (hk : μ k ≠ 0) (hk0 : k ≠ 0) :
    (arithFactor μ {0} : ℤ) ∣ (k : ℤ) - 1 := by
  apply GeneralA.Arithmetic.arithFactor_dvd hc hne
  exact ⟨k, hk, Or.inr ⟨by simpa using hk0, rfl⟩⟩

/-- For any supported word, walk displacement plus its leaf count is a multiple of the span. -/
theorem list_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (ds : List ℕ) (hs : ∀ k ∈ ds, μ k ≠ 0) :
    (arithFactor μ {0} : ℤ) ∣ (ds.map (fun k : ℕ => (k : ℤ) - 1)).sum + ds.count 0 := by
  induction ds with
  | nil => simp
  | cons k ds ih =>
    have hi := ih (fun l hl => hs l (List.mem_cons_of_mem k hl))
    by_cases hk : k = 0
    · subst k
      convert hi using 1; simp only [List.map_cons, List.sum_cons, List.count_cons_self, Nat.cast_add, Nat.cast_one, Nat.cast_zero]; ring
    · have hd := step_dvd hc hne (hs k (by simp)) hk
      convert dvd_add hd hi using 1; simp [hk]; ring

/-- At the tree clock, the `k`-th leaf has not yet been read. -/
theorem treeStopPos_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (t : PlaneTree) (hw : PlaneTree.weight (fun k => μ k) t ≠ 0)
    {k : ℕ} (hk : 1 ≤ k) (hkl : k ≤ t.degreeCount 0) :
    (arithFactor μ {0} : ℤ) ∣ treeStopPos t k + (k : ℤ) - 1 := by
  obtain ⟨i, hi, _, hc'⟩ := Conditioning.AbsCont.exists_treeLeafTime hk hkl
  have hs := (PlaneTree.weight_ne_zero_iff (fun k => μ k) t).1 hw
  have hd := list_dvd hc hne (t.degrees.take i)
    (fun k hk => hs k (List.mem_of_mem_take hk))
  have hW : treeStopPos t k = (t.increments.take i).sum := by
    simp only [treeStopPos, hi, ENat.toNat_natCast, PlaneTree.lukasiewicz]
  rw [hW]
  simpa only [PlaneTree.increments, List.map_take] using
    (show (arithFactor μ {0} : ℤ) ∣ (t.increments.take i).sum + (k : ℤ) - 1 from by
      have he : ((t.degrees.take i).count 0 : ℤ) = (k : ℤ) - 1 := by omega
      simpa only [PlaneTree.increments, List.map_take, he, ← add_sub_assoc] using hd)

/-- At the walk clock, the `k`-th leaf step has already been read. -/
theorem walkSum_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (ω : ℕ → ℕ) (hs : ∀ i, μ (ω i) ≠ 0) (m : ℕ) :
    (arithFactor μ {0} : ℤ) ∣ walkSum ω m + walkLeafCount ω m := by
  induction m with
  | zero => simp [walkSum, walkLeafCount]
  | succ m ih =>
    have hw : walkSum ω (m + 1) = walkSum ω m + ((ω m : ℤ) - 1) := by
      simp only [walkSum, Finset.sum_range_succ]
    rw [hw, Vervaat.Discrete.walkLeafCount_succ']
    by_cases hz : ω m = 0
    · convert ih using 1; simp only [hz, Nat.cast_zero, zero_sub, ite_eq_left, Nat.cast_add, Nat.cast_one]; ring
    · have hd := step_dvd hc hne (hs m) hz
      convert dvd_add ih hd using 1; simp [hz]; ring

/-- Every iid coordinate has nonzero offspring mass almost surely. -/
theorem ae_iid_supported (μ : PMF ℕ) : ∀ᵐ ω ∂iidWalk μ, ∀ i, μ (ω i) ≠ 0 := by
  have hμ : ∀ᵐ k ∂μ.toMeasure, μ k ≠ 0 := by
    rw [ae_iff_of_countable]
    intro k hk
    simpa only [PMF.toMeasure_apply_singleton μ k (measurableSet_singleton k)] using hk
  apply ae_all_iff.2
  intro i
  exact ((measurePreserving_eval_infinitePi (fun _ : ℕ => μ.toMeasure) i).quasiMeasurePreserving.ae hμ)

/-- A finite tree sampled from the BGW law has nonzero weight almost surely. -/
theorem ae_tree_weight_ne_zero (μ : PMF ℕ) :
    ∀ᵐ T ∂bienaymeLaw μ.toMeasure, ∀ t : PlaneTree, T = t.toLocallyFinite →
      PlaneTree.weight (fun k => μ k) t ≠ 0 := by
  apply ae_all_iff.2
  intro t
  by_cases hw : PlaneTree.weight (fun k => μ k) t = 0
  · have hnull : bienaymeLaw μ.toMeasure {t.toLocallyFinite} = 0 := by
      simpa only [bienaymeLaw_toLocallyFinite, PMF.toMeasure_apply_singleton μ _ (measurableSet_singleton _)] using hw
    have ht : ∀ᵐ T ∂bienaymeLaw μ.toMeasure, T ≠ t.toLocallyFinite := by
      simpa only [ae_iff, not_not, Set.ofPred_eq_eq_singleton] using hnull
    filter_upwards [ht] with T hT
    exact fun h => (hT h).elim
  · exact Eventually.of_forall fun _ _ => hw

/-- The natural projection fixes permitted endpoints. -/
theorem natProject_eq_self {g : ℕ} {r : ℤ} {z : ℕ} (h : (g : ℤ) ∣ r - z) :
    Residue.natProject g r z = z := by
  simp only [Residue.natProject, Residue.project_eq_self h, Int.toNat_natCast]

private theorem evalEnd_absPair (μ0 : ℝ) (B : ℕ → ℝ) (r : ℕ) (a : ℝ≥0)
    (ha : 0 < (a : ℝ)) (t : PlaneTree) :
    evalEnd a (absPair μ0 B r a ha t.toLocallyFinite).1 =
      (treeStopPos t ⌊(a : ℝ) * μ0 * r⌋₊ : ℝ) / B r := by
  change 1 * (BGW.Probability.RealWalk.partialSum
      (PathTail.treeIncrementSeq t.toLocallyFinite)
      ⌊(treeLeafClock t.toLocallyFinite ((a : ℝ) * μ0 * r) : ℝ) *
        min (1 / (a : ℝ) * a) 1⌋₊ / B r) = _
  rw [one_div_mul_cancel ha.ne', min_self, mul_one, Nat.floor_natCast, one_mul]
  simp only [treeLeafClock, toPlaneTree_toLocallyFinite,
    BGW.Probability.RealWalk.partialSum, PathTail.treeIncrementSeq,
    ExactPrefix.treeIncrements_toLocallyFinite, ExactPrefix.sum_range_getD]
  rfl

/-- Agreement of the projected forest density on supported finite trees. -/
theorem absWeight_absPair {μ : PMF ℕ} {B : ℕ → ℝ} {r n : ℕ} {a : ℝ≥0}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (ha : 0 < (a : ℝ)) (hB : B r ≠ 0)
    (hadm : LeafAdmissible μ n) (t : PlaneTree)
    (hw : PlaneTree.weight (fun k => μ k) t ≠ 0)
    (hk : 1 ≤ ⌊(a : ℝ) * (μ 0).toReal * r⌋₊)
    (hkn : ⌊(a : ℝ) * (μ 0).toReal * r⌋₊ < n) (ht : n ≤ t.degreeCount 0) :
    DensityLattice.absWeight μ B r n a (absPair (μ 0).toReal B r a ha t.toLocallyFinite) =
      ((psi μ (n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊)
          (pendingTrees t ⌊(a : ℝ) * (μ 0).toReal * r⌋₊) / psi μ n 1) /
        (psiStar μ (n - ⌊(a : ℝ) * (μ 0).toReal * r⌋₊)
          (pendingTrees t ⌊(a : ℝ) * (μ 0).toReal * r⌋₊) / psiStar μ n 1)) := by
  let k := ⌊(a : ℝ) * (μ 0).toReal * r⌋₊
  have hkl : k ≤ t.degreeCount 0 := hkn.le.trans ht
  have hpos := (Conditioning.AbsCont.abscon_pending_nonneg t hk hkl).1
  have hpend : (pendingTrees t k : ℤ) = treeStopPos t k := Int.toNat_of_nonneg hpos
  have hn1 : 1 ≤ n := by omega
  have hres : (arithFactor μ {0} : ℤ) ∣ ((n - k : ℕ) : ℤ) - pendingTrees t k := by
    rw [Nat.cast_sub hkn.le, hpend]
    convert dvd_sub (DenominatorLattice.admissible_dvd hc hne hn1 hadm)
      (treeStopPos_dvd hc hne t hw hk hkl) using 1; ring
  have hfix := natProject_eq_self hres
  simp only [k, ← Int.floor_toNat, pendingTrees] at hfix
  simp only [DensityLattice.absWeight, evalEnd_absPair, mul_div_cancel₀ _ hB,
    ← Int.floor_toNat, Int.floor_intCast, pendingTrees]
  rw [hfix]

/-- The projected bridge density agrees with the true prefix density almost surely. -/
theorem clockPrefixDensity_leafClockPath {μ : PMF ℕ} {B : ℕ → ℝ} {n : ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hn : 1 ≤ n) (hadm : LeafAdmissible μ n)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hB : B ⌊(n : ℝ) / (μ 0).toReal⌋₊ ≠ 0) :
    ∀ᵐ ω ∂iidWalk μ,
      BridgeLattice.clockPrefixDensity μ B n ha (leafClockPath (μ 0).toReal B n ha ω) =
        chi μ (n - ⌊a * n⌋₊) (walkStopPos ω ⌊a * n⌋₊) / chi μ n 0 := by
  filter_upwards [ae_iid_supported μ, ae_exists_markTime μ (hc.apply_zero_ne_zero hne)] with ω hs hm
  let k := ⌊a * n⌋₊
  obtain ⟨m, hm⟩ := hm k
  have hstop : walkStopPos ω k = walkSum ω m := by
    simp only [walkStopPos, LeafLimits.Bridge.walkLeafTime_eq_of_isMarkTime hm, ENat.toNat_natCast]
  have hd := walkSum_dvd hc hne ω hs m
  rw [hm.1] at hd
  have hk : k ≤ n := LeafLimits.Bridge.floor_mark_le ha1 n
  have hres : (arithFactor μ {0} : ℤ) ∣ ((n - k : ℕ) : ℤ) - 1 - walkStopPos ω k := by
    rw [Nat.cast_sub hk, hstop]
    convert dvd_sub (DenominatorLattice.admissible_dvd hc hne hn hadm) hd using 1; ring
  unfold BridgeLattice.clockPrefixDensity
  rw [LeafLimits.Bridge.leafClockPath_end, div_mul_cancel₀ _ hB, round_intCast,
    Residue.project_eq_self hres]

private theorem lintegral_absPair_abscon {μ : PMF ℕ} {B : ℕ → ℝ} {r n : ℕ} {a : ℝ≥0}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (ha : 0 < (a : ℝ)) (hb : B r ≠ 0)
    (hadm : LeafAdmissible μ n)
    (hk : 1 ≤ ⌊(a : ℝ) * (μ 0).toReal * r⌋₊)
    (hkn : ⌊(a : ℝ) * (μ 0).toReal * r⌋₊ < n)
    (F : Skorokhod.D (a : ℝ) ℝ × C(Set.Icc (0 : ℝ) a, ℝ) → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z ∂((leafTreeLaw μ n).map (absPair (μ 0).toReal B r a ha)).toMeasure =
      ∫⁻ z, F z * DensityLattice.absWeight μ B r n a z
        ∂((leafGeTreeLaw μ n).map (absPair (μ 0).toReal B r a ha)).toMeasure := by
  obtain ⟨G, hG⟩ := LeafLimits.Absolue.exists_absPair_eq_comp_treeStopPath (μ 0).toReal B r a ha hk
  have hΦ := measurable_absPair (μ 0).toReal B r a ha
  have hge := BGWLeaves.leafGeEvent_ne_zero hc hne n
  rw [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.toMeasure_map,
    lintegral_map hF hΦ,
    lintegral_map (f := fun z => F z * DensityLattice.absWeight μ B r n a z)
      (hF.mul (DensityLattice.measurable_absWeight μ B r n a)) hΦ,
    coe_leafTreeLaw hadm, coe_leafGeTreeLaw hge]
  calc
    _ = ∫⁻ τ, finiteTreeLift (fun t => F (G (treeStopPath t
        ⌊(a : ℝ) * (μ 0).toReal * r⌋₊))) τ
        ∂((bienaymeLaw μ.toMeasure)[|leafCountEvent n]) := by
      apply lintegral_congr_ae
      filter_upwards [ae_cond_mem (measurableSet_leafCountEvent n)] with τ hτ
      obtain ⟨t, rfl, ht⟩ := hτ
      rw [finiteTreeLift_toLocallyFinite, ← hG t (by omega)]
    _ = _ := BGWLeaves.prop_abscon hc hne hk hkn (fun w => F (G w))
    _ = _ := by
      apply lintegral_congr_ae
      filter_upwards [ae_cond_mem
        (BGWLeaves.Conditioning.AbsCont.measurableSet_finiteTreeEvent
          (fun t => n ≤ t.degreeCount 0)),
        (cond_absolutelyContinuous : ((bienaymeLaw μ.toMeasure)[|leafGeEvent n]) ≪ bienaymeLaw μ.toMeasure).ae_le (ae_tree_weight_ne_zero μ)] with τ hτ hw
      obtain ⟨t, rfl, ht⟩ := hτ
      rw [finiteTreeLift_toLocallyFinite, ← hG t (by omega), absWeight_absPair hc hne ha hb hadm t (hw t rfl) hk hkn ht]

theorem map_leaf_eq_withDensity_absWeight {μ : PMF ℕ} {B : ℕ → ℝ} {r n : ℕ}
    {a : ℝ≥0} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (ha : 0 < (a : ℝ)) (hb : B r ≠ 0)
    (hadm : LeafAdmissible μ n) (hk : 1 ≤ ⌊(a : ℝ) * (μ 0).toReal * r⌋₊)
    (hkn : ⌊(a : ℝ) * (μ 0).toReal * r⌋₊ < n) :
    ((leafTreeLaw μ n).map (absPair (μ 0).toReal B r a ha)).toMeasure =
      (((leafGeTreeLaw μ n).map (absPair (μ 0).toReal B r a ha)).toMeasure).withDensity
        (DensityLattice.absWeight μ B r n a) := by
  refine Measure.ext_of_lintegral _ fun F hF => ?_
  rw [lintegral_withDensity_eq_lintegral_mul _ (DensityLattice.measurable_absWeight μ B r n a) hF]
  simpa only [Pi.mul_apply, mul_comm] using
    lintegral_absPair_abscon hc hne ha hb hadm hk hkn F hF


theorem map_leafClockPath_eq_withDensity {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    {n : ℕ} (hn : 1 ≤ n) (hadm : LeafAdmissible μ n) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (B : ℕ → ℝ)
    (hB : B ⌊(n : ℝ) / (μ 0).toReal⌋₊ ≠ 0) :
    ((bridgeWalkLaw μ n).map (leafClockPath (μ 0).toReal B n ha)).toMeasure =
      ((walkLawPM μ).map (leafClockPath (μ 0).toReal B n ha)).toMeasure.withDensity
        (BridgeLattice.clockPrefixDensity μ B n ha) := by
  ext s hs
  have hX := measurable_leafClockPath (μ 0).toReal B n ha
  rw [ProbabilityMeasure.toMeasure_map,
    ← lintegral_indicator_one hs, lintegral_map ((measurable_one : Measurable (1 : Skorokhod.D a ℝ → ℝ≥0∞)).indicator hs) hX,
    LeafLimits.Bridge.lintegral_bridgeWalkLaw_leafClockPath (hc.apply_zero_ne_zero hne) hn hadm ha ha1,
    withDensity_apply _ hs, ← lintegral_indicator hs, ProbabilityMeasure.toMeasure_map,
    lintegral_map ((BridgeLattice.measurable_clockPrefixDensity μ B n ha).indicator hs) hX]
  apply lintegral_congr_ae
  filter_upwards [clockPrefixDensity_leafClockPath hc hne hn hadm ha ha1 hB] with ω hωeq
  rw [← hωeq]
  by_cases hω : leafClockPath (μ 0).toReal B n ha ω ∈ s <;>
    simp [hω]


end BGWLeaves.LeafLimitsGeneral.SupportLattice
