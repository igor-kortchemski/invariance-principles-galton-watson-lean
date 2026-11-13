module

public import BGWLeaves.GeneralAFunctional.WalkStrongMarkov
public import BGWLeaves.GeneralAFunctional.WalkDensity
public import BGWLeaves.LeafLimitsGeneral.SupportLattice

/-! The stopped-path density as a density on the original clocked walk. -/

@[expose] public section
namespace BGWLeaves.GeneralAFunctional.WalkPathDensity
open MeasureTheory ProbabilityTheory Filter BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis BGWLeaves.GeneralA
open BGWLeaves.GeneralAFunctional.WalkCyclic BGWLeaves.GeneralAFunctional.WalkVervaat
open BGWLeaves.GeneralAFunctional.WalkStrongMarkov BGWLeaves.GeneralAFunctional.WalkFCLT
open BGWLeaves.LeafLimits.Bridge BGWLeaves.LeafLimitsGeneral
open scoped ENNReal NNReal Topology

theorem timeE_toNat (A : Set ℕ) (ω : ℕ → ℕ) (n : ℕ) :
    (timeE A ω n).toNat = aMarkTime A n ω := by
  unfold timeE aMarkTime markTime walkLeafTime
  simp_rw [walkLeafCount_markIndicator]

theorem lintegral_bridge_stopPath (A : Set ℕ) {μ : PMF ℕ} (h0 : μ.toMeasure A ≠ 0)
    {n k : ℕ} (hn : 1 ≤ n) (hadm : ZetaAAdmissible μ A n) (hkn : k < n)
    (f : List ℤ → ℝ≥0∞) :
    ∫⁻ ω, f (stopPath A ω k) ∂(Walk.aBridgeLaw μ A n).toMeasure =
      ∫⁻ ω, f (stopPath A ω k) *
        (WalkLocal.chiA μ A (n-k) (stopPos A ω k) / WalkLocal.chiA μ A n 0) ∂iidWalk μ := by
  rw [Walk.coe_aBridgeLaw hn hadm]
  have he : bridgeAtAMark A n = stopEvent A n (-1) := by
    rw [stopEvent_eq]
    rfl
  rw [he]
  exact WalkStrongMarkov.lem_absolueC2_k A h0 hkn f

theorem stopPath_getD (A : Set ℕ) (ω : ℕ → ℕ) (k i : ℕ) (hi : i ≤ aMarkTime A k ω) :
    (stopPath A ω k).getD i 0 = walkSum ω i := by
  unfold stopPath
  rw [timeE_toNat]
  rw [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range (show i < aMarkTime A k ω + 1 by exact Nat.lt_succ_of_le hi)]
  rfl

theorem clockPath_apply_stopPath (A : Set ℕ) (p : ℝ) (B : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (ω : ℕ → ℕ) (t : Set.Icc (0 : ℝ) a) :
    aClockPath A p B n ha ω t =
      (((stopPath A ω ⌊a * n⌋₊).getD
        ⌊(aClock A ω (a * n) : ℝ) * min (1 / a * (t : ℝ)) 1⌋₊ 0 : ℤ) : ℝ) /
          B ⌊(n : ℝ) / p⌋₊ := by
  change 1 * (BGW.Probability.RealWalk.partialSum (walkIncr ω) _ / _) = _
  rw [one_mul, partialSum_walkIncr, stopPath_getD A]
  apply Nat.floor_le_of_le
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (min_le_right _ _)

theorem clockPath_eq_of_stopPath_eq (A : Set ℕ) (p : ℝ) (B : ℕ → ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) {ω ω' : ℕ → ℕ}
    (h : stopPath A ω ⌊a * n⌋₊ = stopPath A ω' ⌊a * n⌋₊) :
    aClockPath A p B n ha ω = aClockPath A p B n ha ω' := by
  have hl := congrArg List.length h
  simp only [stopPath, timeE_toNat, List.length_map, List.length_range] at hl
  have hm : aClock A ω (a * n) = aClock A ω' (a * n) := Nat.add_right_cancel hl
  apply Skorokhod.ext
  intro t
  rw [clockPath_apply_stopPath A, clockPath_apply_stopPath A, h, hm]

theorem exists_clockPath_eq_comp_stopPath (A : Set ℕ) (p : ℝ) (B : ℕ → ℝ) (n : ℕ)
    {a : ℝ} (ha : 0 < a) :
    ∃ F : List ℤ → Skorokhod.D a ℝ, ∀ ω,
      F (stopPath A ω ⌊a * n⌋₊) = aClockPath A p B n ha ω := by
  classical
  let F : List ℤ → Skorokhod.D a ℝ := fun z =>
    if hz : ∃ ω, stopPath A ω ⌊a * n⌋₊ = z then
      aClockPath A p B n ha (Classical.choose hz)
    else aClockPath A p B n ha (fun _ => 0)
  refine ⟨F, fun ω => ?_⟩
  dsimp only [F]
  rw [dite_eq_left (show ∃ ω', stopPath A ω' ⌊a * n⌋₊ = stopPath A ω ⌊a * n⌋₊ from ⟨ω, rfl⟩)]
  exact clockPath_eq_of_stopPath_eq A p B n ha (Classical.choose_spec (show ∃ ω', stopPath A ω' ⌊a * n⌋₊ = stopPath A ω ⌊a * n⌋₊ from ⟨ω, rfl⟩))

theorem lintegral_bridge_clockPath (A : Set ℕ) {μ : PMF ℕ} (h0 : μ.toMeasure A ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) (hadm : ZetaAAdmissible μ A n) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (p : ℝ) (B : ℕ → ℝ)
    (g : Skorokhod.D a ℝ → ℝ≥0∞) :
    ∫⁻ ω, g (aClockPath A p B n ha ω) ∂(Walk.aBridgeLaw μ A n).toMeasure =
      ∫⁻ ω, g (aClockPath A p B n ha ω) *
        (WalkLocal.chiA μ A (n - ⌊a * n⌋₊) (stopPos A ω ⌊a * n⌋₊) / WalkLocal.chiA μ A n 0) ∂iidWalk μ := by
  obtain ⟨F, hF⟩ := exists_clockPath_eq_comp_stopPath A p B n ha
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hkn : ⌊a * n⌋₊ < n := (Nat.floor_lt (by positivity)).mpr (by nlinarith)
  simpa only [Function.comp_def, hF] using lintegral_bridge_stopPath A h0 hn hadm hkn (g ∘ F)

theorem clockPath_end (A : Set ℕ) (p : ℝ) (B : ℕ → ℝ) (n : ℕ) {a : ℝ} (ha : 0 < a)
    (ω : ℕ → ℕ) :
    aClockPath A p B n ha ω ⟨a, ha.le, le_rfl⟩ =
      (stopPos A ω ⌊a * n⌋₊ : ℝ) / B ⌊(n : ℝ) / p⌋₊ := by
  change 1 * (BGW.Probability.RealWalk.partialSum (walkIncr ω)
    ⌊(aClock A ω (a * n) : ℝ) * min (1 / a * a) 1⌋₊ / _) = _
  rw [one_div_mul_cancel ha.ne', min_self, mul_one, Nat.floor_natCast,
    partialSum_walkIncr, one_mul]
  simp only [stopPos, aClock, timeE_toNat]



theorem walkSum_dvd {μ : PMF ℕ} {A : Set ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (ω : ℕ → ℕ) (hs : ∀ i, μ (ω i) ≠ 0) (m : ℕ) :
    (arithFactor μ A : ℤ) ∣ walkSum ω m + walkACount A ω m := by
  induction m with
  | zero => simp [walkSum, walkACount]
  | succ m ih =>
    have hw : walkSum ω (m+1) = walkSum ω m + ((ω m : ℤ)-1) := by
      simp only [walkSum, Finset.sum_range_succ]
    rw [hw, walkACount_succ]
    by_cases hz : ω m ∈ A
    · have hd : (arithFactor μ A : ℤ) ∣ (ω m : ℤ) :=
        GeneralA.Arithmetic.arithFactor_dvd hc hne ⟨ω m, hs m, Or.inl ⟨hz, rfl⟩⟩
      convert dvd_add ih hd using 1
      simp only [ite_eq_left hz, Nat.cast_add, Nat.cast_one]
      ring
    · have hd : (arithFactor μ A : ℤ) ∣ (ω m : ℤ)-1 :=
        GeneralA.Arithmetic.arithFactor_dvd hc hne ⟨ω m, hs m, Or.inr ⟨hz, rfl⟩⟩
      convert dvd_add ih hd using 1
      simp only [ite_eq_right hz, add_zero]
      ring

/-- The projected bridge density agrees with the true prefix density almost surely. -/
theorem clockPrefixDensity_clockPath {μ : PMF ℕ} {A : Set ℕ} {B : ℕ → ℝ} {n : ℕ}
    (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hA : μ.toMeasure A ≠ 0) (_hn : 1 ≤ n) (hadm : ZetaAAdmissible μ A n)
    {a : ℝ} (ha : 0 < a) (ha1 : a < 1)
    (hB : B ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊ ≠ 0) :
    ∀ᵐ ω ∂iidWalk μ,
      WalkDensity.clockPrefixDensity μ A B n ha (aClockPath A (μ.toMeasure A).toReal B n ha ω) =
        WalkLocal.chiA μ A (n - ⌊a * n⌋₊) (stopPos A ω ⌊a * n⌋₊) / WalkLocal.chiA μ A n 0 := by
  filter_upwards [SupportLattice.ae_iid_supported μ, WalkClock.ae_exists_aMarkTime μ A hA] with ω hs hm
  let k := ⌊a * n⌋₊
  obtain ⟨m, hm⟩ := hm k
  have hstop : stopPos A ω k = walkSum ω m := by
    simp only [stopPos, timeE_toNat, aMarkTime_eq hm]
  have hd := walkSum_dvd (A := A) hc hne ω hs m
  rw [hm.1] at hd
  have hk : k ≤ n := LeafLimits.Bridge.floor_mark_le ha1 n
  have hres : (arithFactor μ A : ℤ) ∣ ((n - k : ℕ) : ℤ) - 1 - stopPos A ω k := by
    rw [Nat.cast_sub hk, hstop]
    convert dvd_sub (WalkDenominator.admissible_dvd hc hne hadm) hd using 1; ring
  unfold WalkDensity.clockPrefixDensity
  rw [clockPath_end A, div_mul_cancel₀ _ hB, round_intCast,
    Residue.project_eq_self hres]


theorem map_clockPath_eq_withDensity {μ : PMF ℕ} {A : Set ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hA : μ.toMeasure A ≠ 0)
    {n : ℕ} (hn : 1 ≤ n) (hadm : ZetaAAdmissible μ A n) {a : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (B : ℕ → ℝ)
    (hB : B ⌊(n : ℝ) / (μ.toMeasure A).toReal⌋₊ ≠ 0) :
    ((Walk.aBridgeLaw μ A n).map (aClockPath A (μ.toMeasure A).toReal B n ha)).toMeasure =
      ((walkLawPM μ).map (aClockPath A (μ.toMeasure A).toReal B n ha)).toMeasure.withDensity
        (WalkDensity.clockPrefixDensity μ A B n ha) := by
  ext s hs
  have hX := measurable_aClockPath A (μ.toMeasure A).toReal B n ha
  rw [ProbabilityMeasure.toMeasure_map,
    ← lintegral_indicator_one hs, lintegral_map ((measurable_one : Measurable (1 : Skorokhod.D a ℝ → ℝ≥0∞)).indicator hs) hX,
    lintegral_bridge_clockPath A hA hn hadm ha ha1,
    withDensity_apply _ hs, ← lintegral_indicator hs, ProbabilityMeasure.toMeasure_map,
    lintegral_map ((WalkDensity.measurable_clockPrefixDensity μ A B n ha).indicator hs) hX]
  apply lintegral_congr_ae
  filter_upwards [clockPrefixDensity_clockPath hc hne hA hn hadm ha ha1 hB] with ω hωeq
  rw [← hωeq]
  by_cases hω : aClockPath A (μ.toMeasure A).toReal B n ha ω ∈ s <;>
    simp [hω]

end BGWLeaves.GeneralAFunctional.WalkPathDensity
