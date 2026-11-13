module

public import BGWLeaves.MaxDegree.Defs
public import BGWLeaves.Vervaat
public import BGWLeaves.Conditioning
public import BGWLeaves.MaxDegree.Concentration
import BGWLeaves.MaxDegree.Transfer
import Mathlib.Probability.Independence.InfinitePi

/-!
# Maximum degree: the two halves of the bridge

The first half of the marks (`eq:i`) and the reverse half under the bridge: `bridge_reverse_half`, `eq_i_lower`,
`eq_i_upper`.  The theorems are those stated in `BGWLeaves.MaxDegree`; they are exported in namespace
`BGWLeaves.MaxDegree.Bridge` with exactly the types stated there.

Proof outline.
* `bridge_reverse_half`: decompose the bridge by `k = T_n`; `{T_n = k, W_k = -1} = {ω_{k-1} = 0} ∩ {W_{k-1} = 0, Λ(k-1) = n-1}`
  (the last coordinate is independent of the first `k-1`, `iIndepFun_infinitePi`).  Both events are written through the
  counts `Λ(i)` (`i ≥ T_m ⟺ Λ(i) ≥ m`, `i < T_{n-m} ⟺ Λ(i) < n-m`) as events of the path `(W_0, …, W_{k-1})`
  and of its reversal; `timeReversal_map` identifies the two laws.  For `q < -1` both events are the whole bridge.
* `eq_i_lower`, `eq_i_upper`: the strong Markov property `lem_absolueC2_k` for events of the stopped path
  (`stopEv`, encoded by the partial sums), the global density bounds `chi_sup_bound`, `chi_zero_lower` (module
  `Concentration`), the clock concentration `lem_CVf2_i` and the product law of the first `⌊n/(4μ₀)⌋` (resp.
  `⌊n/μ₀⌋`) steps.  The term `P[|W_{T_m}| ≥ α√n | W_{T_n} = -1]` of the statements is nonnegative and not needed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis BGWLeaves
open BGWLeaves.MaxDegree.Concentration
open scoped ENNReal NNReal Topology

local notation "𝐏w[" μ "]" => Measure.infinitePi (fun _ : ℕ => μ)

namespace BGWLeaves.MaxDegree.Bridge


/-- stopped-prefix events -/
private def stopEv (k : ℕ) (Φ : ℕ → Set (ℕ → ℕ)) : Set (ℕ → ℕ) := {ω | ∃ T, IsMarkTime k ω T ∧ ω ∈ Φ T}

private def PrefDep (Φ : ℕ → Set (ℕ → ℕ)) : Prop :=
  ∀ (T : ℕ) (ω ω' : ℕ → ℕ), (∀ i < T, ω i = ω' i) → (ω ∈ Φ T ↔ ω' ∈ Φ T)

private theorem measurableSet_stopEv (k : ℕ) {Φ : ℕ → Set (ℕ → ℕ)} (hΦ : PrefDep Φ) :
    MeasurableSet (stopEv k Φ) := by
  have : stopEv k Φ = ⋃ T : ℕ, {ω | IsMarkTime k ω T ∧ ω ∈ Φ T} := by
    ext ω; simp [stopEv]
  rw [this]
  refine MeasurableSet.iUnion fun T => ?_
  have hd : ∀ ω ω' : ℕ → ℕ, (∀ i < T, ω i = ω' i) →
      ((IsMarkTime k ω T ∧ ω ∈ Φ T) ↔ (IsMarkTime k ω' T ∧ ω' ∈ Φ T)) := by
    intro ω ω' hh
    rw [isMarkTime_congr hh, hΦ T ω ω' hh]
  have hS : {ω : ℕ → ℕ | IsMarkTime k ω T ∧ ω ∈ Φ T} =
      pref T ⁻¹' {y | IsMarkTime k (extendZ T y) T ∧ extendZ T y ∈ Φ T} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    exact hd _ _ (extendZ_pref_agree T ω)
  rw [hS]
  exact measurable_pref T (Set.to_countable _).measurableSet

/-- decode the increments from a path of partial sums -/
private def extPath (ℓ : List ℤ) : ℕ → ℕ := fun i =>
  if i + 1 < ℓ.length then (ℓ.getD (i + 1) 0 - ℓ.getD i 0 + 1).toNat else 0

private theorem stopPath_eq (ω : ℕ → ℕ) {k T : ℕ} (hk : IsMarkTime k ω T) :
    walkStopPath ω k = (List.range (T + 1)).map (walkSum ω) := by
  have : (walkLeafTime ω k).toNat = T := by rw [isMarkTime_walkLeafTime hk]; simp
  unfold walkStopPath
  rw [this]

private theorem extPath_agree (ω : ℕ → ℕ) (T : ℕ) :
    ∀ i < T, extPath ((List.range (T + 1)).map (walkSum ω)) i = ω i := by
  intro i hi
  unfold extPath
  have hl : i + 1 < ((List.range (T + 1)).map (walkSum ω)).length := by simp; omega
  simp only [hl, ↓reduceIte]
  have g1 : ((List.range (T + 1)).map (walkSum ω)).getD (i + 1) 0 = walkSum ω (i + 1) := by
    have hr : (List.range (T + 1))[i + 1]? = some (i + 1) := List.getElem?_range (by omega)
    rw [List.getD_eq_getElem?_getD]; simp [List.getElem?_map, hr]
  have g2 : ((List.range (T + 1)).map (walkSum ω)).getD i 0 = walkSum ω i := by
    have hr : (List.range (T + 1))[i]? = some i := List.getElem?_range (by omega)
    rw [List.getD_eq_getElem?_getD]; simp [List.getElem?_map, hr]
  rw [g1, g2]
  have : walkSum ω (i + 1) = walkSum ω i + ((ω i : ℤ) - 1) := by
    unfold walkSum; rw [Finset.sum_range_succ]
  rw [this]
  have : walkSum ω i + ((ω i : ℤ) - 1) - walkSum ω i + 1 = (ω i : ℤ) := by ring
  rw [this]; exact Int.toNat_natCast _

private theorem wlc_le (ω : ℕ → ℕ) (T : ℕ) : walkLeafCount ω T ≤ T := by
  induction T with
  | zero => simp [wlc_zero]
  | succ T ih => rw [wlc_succ]; split_ifs <;> omega

open scoped Classical in
/-- the path functional encoding a stopped-prefix event -/
private noncomputable def pathF (Φ : ℕ → Set (ℕ → ℕ)) (ℓ : List ℤ) : ℝ≥0∞ :=
  if 2 ≤ ℓ.length ∧ extPath ℓ ∈ Φ (ℓ.length - 1) then 1 else 0

private theorem pathF_stopPath {k : ℕ} (hk1 : 1 ≤ k) {Φ : ℕ → Set (ℕ → ℕ)} (hΦ : PrefDep Φ) (ω : ℕ → ℕ) :
    pathF Φ (walkStopPath ω k) = (stopEv k Φ).indicator 1 ω := by
  classical
  by_cases hex : ∃ T, IsMarkTime k ω T
  · obtain ⟨T, hT⟩ := hex
    have hp := stopPath_eq ω hT
    have hTk : 1 ≤ T := by
      have := wlc_le ω T
      rw [hT.1] at this; omega
    have hlen : ((List.range (T + 1)).map (walkSum ω)).length = T + 1 := by simp
    have hmem : (extPath ((List.range (T + 1)).map (walkSum ω)) ∈ Φ T) ↔ ω ∈ Φ T := by
      apply hΦ T
      exact extPath_agree ω T
    unfold pathF
    rw [hp, hlen]
    have h2 : 2 ≤ T + 1 := by omega
    simp only [Nat.add_sub_cancel, h2, true_and]
    by_cases hΦω : ω ∈ Φ T
    · have : ω ∈ stopEv k Φ := ⟨T, hT, hΦω⟩
      simp [hmem.2 hΦω, this]
    · have : ω ∉ stopEv k Φ := by
        rintro ⟨T', hT', hΦ'⟩
        have := BGWLeaves.IsMarkTime.unique hT hT'
        subst this
        exact hΦω hΦ'
      have h3 : extPath ((List.range (T + 1)).map (walkSum ω)) ∉ Φ T := fun h => hΦω (hmem.1 h)
      simp [h3, this]
  · have hnot : ω ∉ stopEv k Φ := fun ⟨T, hT, _⟩ => hex ⟨T, hT⟩
    have htop : walkLeafTime ω k = ⊤ := by
      by_contra hne
      exact hex (walkLeafTime_ne_top_iff.1 hne)
    have : walkStopPath ω k = [0] := by
      simp [walkStopPath, htop, walkSum]
    rw [this]
    unfold pathF
    simp [hnot]

private theorem cond_stopEv_le {μ : PMF ℕ} (h : HypW μ) {C1 c : ℝ} (hC1 : 0 < C1) (hc : 0 < c)
    (hsup : ∀ n : ℕ, 1 ≤ n → ∀ j : ℤ, (chi μ n j).toReal ≤ C1 / Real.sqrt n)
    {n k : ℕ} (hk1 : 1 ≤ k) (hkn : k < n) (hlow : c / Real.sqrt n ≤ (chi μ n 0).toReal)
    {Φ : ℕ → Set (ℕ → ℕ)} (hΦ : PrefDep Φ) :
    ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (stopEv k Φ) ≤
      (C1 / Real.sqrt ((n - k : ℕ) : ℝ)) / (c / Real.sqrt n) * (iidWalk μ).real (stopEv k Φ) := by
  have h0 : μ 0 ≠ 0 := h.critical.apply_zero_ne_zero h.nondegenerate
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hkn' : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
  have hsq' : 0 < Real.sqrt ((n - k : ℕ) : ℝ) := Real.sqrt_pos.2 hkn'
  set E := stopEv k Φ with hE
  have hEm : MeasurableSet E := measurableSet_stopEv k hΦ
  have : IsProbabilityMeasure (iidWalk μ) := by unfold iidWalk; infer_instance
  rw [bridgeAtMark_eq]
  have hkey : ∫⁻ ω, E.indicator 1 ω ∂((iidWalk μ)[|walkStopEvent n (-1)]) =
      ∫⁻ ω, E.indicator 1 ω * (chi μ (n - k) (walkStopPos ω k) / chi μ n 0) ∂iidWalk μ := by
    have := BGWLeaves.lem_absolueC2_k h0 hkn (pathF Φ)
    simpa only [pathF_stopPath hk1 hΦ] using this
  rw [lintegral_indicator_one hEm] at hkey
  set K : ℝ≥0∞ := ENNReal.ofReal (C1 / Real.sqrt ((n - k : ℕ) : ℝ)) / ENNReal.ofReal (c / Real.sqrt n) with hK
  have hKne : K ≠ ⊤ := ENNReal.div_ne_top ENNReal.ofReal_ne_top
    (ENNReal.ofReal_pos.2 (by positivity)).ne'
  have hratio : ∀ ω, chi μ (n - k) (walkStopPos ω k) / chi μ n 0 ≤ K := by
    intro ω
    apply ENNReal.div_le_div
    · rw [ENNReal.le_ofReal_iff_toReal_le (chi_ne_top _ _ _) (by positivity)]
      exact hsup (n - k) (by omega) _
    · rw [ENNReal.ofReal_le_iff_le_toReal (chi_ne_top _ _ _)]
      exact hlow
  have h1 : ((iidWalk μ)[|walkStopEvent n (-1)]) E ≤ (iidWalk μ) E * K := by
    rw [hkey]
    calc ∫⁻ ω, E.indicator 1 ω * (chi μ (n - k) (walkStopPos ω k) / chi μ n 0) ∂iidWalk μ
        ≤ ∫⁻ ω, E.indicator 1 ω * K ∂iidWalk μ := lintegral_mono fun ω => mul_le_mul' le_rfl (hratio ω)
      _ = (∫⁻ ω, E.indicator 1 ω ∂iidWalk μ) * K := lintegral_mul_const' _ _ hKne
      _ = (iidWalk μ) E * K := by rw [lintegral_indicator_one hEm]
  have h2 : (((iidWalk μ)[|walkStopEvent n (-1)]) E).toReal ≤ (iidWalk μ).real E * K.toReal := by
    calc _ ≤ ((iidWalk μ) E * K).toReal := ENNReal.toReal_mono (ENNReal.mul_ne_top (measure_ne_top _ _) hKne) h1
      _ = _ := by rw [ENNReal.toReal_mul]; rfl
  have hKr : K.toReal = (C1 / Real.sqrt ((n - k : ℕ) : ℝ)) / (c / Real.sqrt n) := by
    rw [hK, ENNReal.toReal_div, ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_ofReal (by positivity)]
  rw [hKr] at h2
  show (((iidWalk μ)[|walkStopEvent n (-1)]) E).toReal ≤ _
  calc _ ≤ _ := h2
    _ = _ := by ring

private theorem real_cyl (μ : PMF ℕ) (N : ℕ) (t : Set ℕ) :
    (iidWalk μ).real {ω : ℕ → ℕ | ∀ i < N, ω i ∈ t} = (μ.toMeasure.real t) ^ N := by
  have hset : {ω : ℕ → ℕ | ∀ i < N, ω i ∈ t} = Set.pi (↑(Finset.range N) : Set ℕ) (fun _ => t) := by
    ext ω; simp
  rw [hset, Measure.real, iidWalk, Measure.infinitePi_pi _ (fun i _ => MeasurableSet.of_discrete)]
  rw [ENNReal.toReal_prod]
  simp [Measure.real]

private theorem stepTail_eq (μ : PMF ℕ) (p : ℝ) :
    stepTail μ p = μ.toMeasure.real {x : ℕ | p ≤ (((x : ℤ) - 1 : ℤ) : ℝ)} := by
  unfold stepTail stepLaw
  simp only [Measure.real]
  rw [Measure.map_apply (measurable_of_countable _) MeasurableSet.of_discrete]
  rfl

private theorem real_cylLt (μ : PMF ℕ) (p : ℝ) (N : ℕ) :
    (iidWalk μ).real {ω : ℕ → ℕ | ∀ i < N, (((ω i : ℤ) - 1 : ℤ) : ℝ) < p} = (1 - stepTail μ p) ^ N := by
  have h1 := real_cyl μ N {x : ℕ | (((x : ℤ) - 1 : ℤ) : ℝ) < p}
  have e : {ω : ℕ → ℕ | ∀ i < N, (((ω i : ℤ) - 1 : ℤ) : ℝ) < p} =
      {ω : ℕ → ℕ | ∀ i < N, ω i ∈ {x : ℕ | (((x : ℤ) - 1 : ℤ) : ℝ) < p}} := rfl
  rw [e, h1, stepTail_eq]
  congr 1
  have hc : {x : ℕ | (((x : ℤ) - 1 : ℤ) : ℝ) < p} = {x : ℕ | p ≤ (((x : ℤ) - 1 : ℤ) : ℝ)}ᶜ := by
    ext x; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_le]
  have : IsProbabilityMeasure μ.toMeasure := inferInstance
  rw [hc, probReal_compl_eq_one_sub MeasurableSet.of_discrete]

private theorem real_cylGt_le (μ : PMF ℕ) (q : ℝ) (N : ℕ) :
    (iidWalk μ).real {ω : ℕ → ℕ | ∃ i < N, q < (((ω i : ℤ) - 1 : ℤ) : ℝ)} ≤
      1 - (1 - stepTail μ q) ^ N := by
  have hc : {ω : ℕ → ℕ | ∃ i < N, q < (((ω i : ℤ) - 1 : ℤ) : ℝ)} =
      {ω : ℕ → ℕ | ∀ i < N, ω i ∈ {x : ℕ | (((x : ℤ) - 1 : ℤ) : ℝ) ≤ q}}ᶜ := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_forall, not_le, exists_prop]
  have : IsProbabilityMeasure (iidWalk μ) := by unfold iidWalk; infer_instance
  have hm : MeasurableSet {ω : ℕ → ℕ | ∀ i < N, ω i ∈ {x : ℕ | (((x : ℤ) - 1 : ℤ) : ℝ) ≤ q}} := by
    have : {ω : ℕ → ℕ | ∀ i < N, ω i ∈ {x : ℕ | (((x : ℤ) - 1 : ℤ) : ℝ) ≤ q}} =
        pref N ⁻¹' {y | ∀ i : Fin N, y i ∈ {x : ℕ | (((x : ℤ) - 1 : ℤ) : ℝ) ≤ q}} := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, pref]
      constructor
      · intro h i; exact h i i.2
      · intro h i hi; exact h ⟨i, hi⟩
    rw [this]; exact measurable_pref N (Set.to_countable _).measurableSet
  rw [hc, probReal_compl_eq_one_sub hm, real_cyl]
  have hprob : IsProbabilityMeasure μ.toMeasure := inferInstance
  have ht : 1 - stepTail μ q ≤ μ.toMeasure.real {x : ℕ | (((x : ℤ) - 1 : ℤ) : ℝ) ≤ q} := by
    rw [stepTail_eq]
    have hc2 : {x : ℕ | (((x : ℤ) - 1 : ℤ) : ℝ) ≤ q} = {x : ℕ | q < (((x : ℤ) - 1 : ℤ) : ℝ)}ᶜ := by
      ext x; simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, not_lt]
    have hsub : {x : ℕ | q < (((x : ℤ) - 1 : ℤ) : ℝ)} ⊆ {x : ℕ | q ≤ (((x : ℤ) - 1 : ℤ) : ℝ)} :=
      Set.ofPred_subset_ofPred.2 fun x hx => le_of_lt hx
    rw [hc2, probReal_compl_eq_one_sub MeasurableSet.of_discrete]
    have := measureReal_mono (μ := μ.toMeasure) hsub
    linarith
  have h0 : 0 ≤ 1 - stepTail μ q := by
    rw [stepTail_eq]
    have := measureReal_le_one (μ := μ.toMeasure) (s := {x : ℕ | q ≤ (((x : ℤ) - 1 : ℤ) : ℝ)})
    linarith
  have := pow_le_pow_left₀ h0 ht N
  linarith

private theorem ratio_le {C1 c : ℝ} (hC1 : 0 < C1) (hc : 0 < c) {n k : ℕ} (hkn : k < n) (h3 : n ≤ 3 * (n - k)) :
    (C1 / Real.sqrt ((n - k : ℕ) : ℝ)) / (c / Real.sqrt n) ≤ C1 * Real.sqrt 3 / c := by
  have hnr : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 hnr
  have hnk : (n : ℝ) ≤ 3 * ((n - k : ℕ) : ℝ) := by exact_mod_cast h3
  have hkpos : 0 < ((n - k : ℕ) : ℝ) := by exact_mod_cast (show 0 < n - k by omega)
  have hsq' : 0 < Real.sqrt ((n - k : ℕ) : ℝ) := Real.sqrt_pos.2 hkpos
  have hr : Real.sqrt n ≤ Real.sqrt 3 * Real.sqrt ((n - k : ℕ) : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hnk
  rw [div_div_div_eq, div_le_div_iff₀ (by positivity) hc]
  have : C1 * Real.sqrt n * c ≤ C1 * (Real.sqrt 3 * Real.sqrt ((n - k : ℕ) : ℝ)) * c := by
    apply mul_le_mul_of_nonneg_right _ hc.le
    exact mul_le_mul_of_nonneg_left hr hC1.le
  nlinarith

private def clockBad (μ : PMF ℕ) (n T : ℕ) : Prop :=
  (T : ℝ) < (n : ℝ) / (4 * (μ 0).toReal) ∨ (n : ℝ) / (μ 0).toReal < T

private theorem clock_arith {r : ℝ} (hr : 1 < r) {n M T : ℝ} (hn : 3 ≤ n) (h1 : (n - 1) / 2 ≤ M)
    (h2 : M ≤ (n + 1) / 2) (hM : 0 < M) (hT : |T / M - r| ≤ 1 / 4) :
    n * r / 4 ≤ T ∧ T ≤ n * r := by
  have hb := abs_le.1 hT
  have hTM : T = M * (T / M) := by field_simp
  have hr0 : 0 < r := by linarith
  constructor
  · have e1 : M * (r - 1 / 4) ≤ T := by
      calc M * (r - 1 / 4) ≤ M * (T / M) := mul_le_mul_of_nonneg_left (by linarith) hM.le
        _ = T := hTM.symm
    have e2 : M * (3 * r / 4) ≤ M * (r - 1 / 4) := mul_le_mul_of_nonneg_left (by linarith) hM.le
    have e3 : (n - 1) / 2 * (3 * r / 4) ≤ M * (3 * r / 4) := mul_le_mul_of_nonneg_right h1 (by positivity)
    nlinarith
  · have e1 : T ≤ M * (r + 1 / 4) := by
      calc T = M * (T / M) := hTM
        _ ≤ M * (r + 1 / 4) := mul_le_mul_of_nonneg_left (by linarith) hM.le
    have e2 : M * (r + 1 / 4) ≤ M * (5 * r / 4) := mul_le_mul_of_nonneg_left (by linarith) hM.le
    have e3 : M * (5 * r / 4) ≤ (n + 1) / 2 * (5 * r / 4) := mul_le_mul_of_nonneg_right h2 (by positivity)
    nlinarith

private theorem clock_incl {μ : PMF ℕ} (hm0 : 0 < (μ 0).toReal) (hm1 : (μ 0).toReal < 1) {n M : ℕ} (hn : 3 ≤ n)
    (hM1 : n / 2 ≤ M) (hM2 : M ≤ (n + 1) / 2) (hM256 : 256 ≤ M) {T : ℕ} (hbad : clockBad μ n T) :
    1 / (M : ℝ) ^ (1 / 4 : ℝ) < |(T : ℝ) / M - 1 / (μ 0).toReal| := by
  by_contra hcon
  rw [not_lt] at hcon
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have h4 : (4 : ℝ) ≤ (M : ℝ) ^ (1 / 4 : ℝ) := by
    by_contra hlt
    rw [not_le] at hlt
    have hp : 0 ≤ (M : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_nonneg hMr.le _
    have := pow_lt_pow_left₀ hlt hp (by norm_num : (4 : ℕ) ≠ 0)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hMr.le] at this
    have e : (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 := by norm_num
    rw [e, Real.rpow_one] at this
    have h256 : (256 : ℝ) ≤ M := by exact_mod_cast hM256
    nlinarith
  have hδ : 1 / (M : ℝ) ^ (1 / 4 : ℝ) ≤ 1 / 4 := by
    apply one_div_le_one_div_of_le (by norm_num) h4
  have hr : 1 < 1 / (μ 0).toReal := by rw [lt_div_iff₀ hm0]; linarith
  have hnr : (3 : ℝ) ≤ n := by exact_mod_cast hn
  have h1 : ((n : ℝ) - 1) / 2 ≤ M := by
    have : n ≤ 2 * M + 1 := by omega
    have : (n : ℝ) ≤ 2 * M + 1 := by exact_mod_cast this
    linarith
  have h2 : (M : ℝ) ≤ ((n : ℝ) + 1) / 2 := by
    have : 2 * M ≤ n + 1 := by omega
    have : 2 * (M : ℝ) ≤ n + 1 := by exact_mod_cast this
    linarith
  obtain ⟨hl, hu⟩ := clock_arith hr hnr h1 h2 hMr (hcon.trans hδ)
  rcases hbad with hb | hb
  · have : (n : ℝ) * (1 / (μ 0).toReal) / 4 = (n : ℝ) / (4 * (μ 0).toReal) := by field_simp
    linarith
  · have : (n : ℝ) * (1 / (μ 0).toReal) = (n : ℝ) / (μ 0).toReal := by field_simp
    linarith

private def ΦD (μ : PMF ℕ) (n : ℕ) : ℕ → Set (ℕ → ℕ) := fun T => {_ω | clockBad μ n T}

private def ΦLt (μ : PMF ℕ) (n : ℕ) (p : ℝ) : ℕ → Set (ℕ → ℕ) :=
  fun T => {ω | ¬ clockBad μ n T ∧ StepsLt p (walkWord ω T)}

private def ΦGt (μ : PMF ℕ) (n : ℕ) (q : ℝ) : ℕ → Set (ℕ → ℕ) :=
  fun T => {ω | ¬ clockBad μ n T ∧ StepsGt q (walkWord ω T)}

private theorem walkWord_congr {ω ω' : ℕ → ℕ} {T : ℕ} (h : ∀ i < T, ω i = ω' i) : walkWord ω T = walkWord ω' T := by
  unfold walkWord
  refine List.map_congr_left fun i hi => ?_
  rw [h i (List.mem_range.1 hi)]

private theorem prefDep_ΦD (μ : PMF ℕ) (n : ℕ) : PrefDep (ΦD μ n) := fun _ _ _ _ => Iff.rfl

private theorem prefDep_ΦLt (μ : PMF ℕ) (n : ℕ) (p : ℝ) : PrefDep (ΦLt μ n p) := by
  intro T ω ω' h
  simp only [ΦLt, Set.mem_ofPred_eq, walkWord_congr h]

private theorem prefDep_ΦGt (μ : PMF ℕ) (n : ℕ) (q : ℝ) : PrefDep (ΦGt μ n q) := by
  intro T ω ω' h
  simp only [ΦGt, Set.mem_ofPred_eq, walkWord_congr h]

/-- the common input of `eq_i_lower` and `eq_i_upper` -/
private theorem eq_i_core {μ : PMF ℕ} (h : HypW μ) (hnl : ¬ IsLatticeLaw (etaLaw μ)) {m : ℕ → ℕ}
    (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) :
    ∃ Kc C2 c2 : ℝ, 0 < Kc ∧ 0 < C2 ∧ 0 < c2 ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      3 ≤ n ∧ 1 ≤ m n ∧ m n < n ∧
      (∀ Φ : ℕ → Set (ℕ → ℕ), PrefDep Φ →
        ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (stopEv (m n) Φ) ≤
          Kc * (iidWalk μ).real (stopEv (m n) Φ)) ∧
      (iidWalk μ).real (stopEv (m n) (ΦD μ n)) ≤ C2 * Real.exp (-c2 * Real.sqrt n) := by
  obtain ⟨C1, hC1, hsup⟩ := chi_sup_boundW h hnl
  obtain ⟨c, hc, hlow⟩ := chi_zero_lowerW h hnl
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 hlow
  obtain ⟨hm0, hm1⟩ := mu0_bounds h
  obtain ⟨C2, c2, hC2, hc2, hoe⟩ := BGWLeaves.lem_CVf2_i μ (h.critical.apply_zero_ne_zero h.nondegenerate)
    (mu0_ne_one h.critical h.nondegenerate)
  refine ⟨C1 * Real.sqrt 3 / c, C2, c2 / 2, by positivity, hC2, by positivity, max N0 512, fun n hn => ?_⟩
  have hn512 : 512 ≤ n := le_trans (le_max_right _ _) hn
  have hnN0 : N0 ≤ n := le_trans (le_max_left _ _) hn
  have hk := hm n
  refine ⟨by omega, by omega, by omega, fun Φ hΦ => ?_, ?_⟩
  · have := cond_stopEv_le h hC1 hc hsup (n := n) (k := m n) (by omega) (by omega) (hN0 n hnN0) hΦ
    refine this.trans ?_
    apply mul_le_mul_of_nonneg_right (ratio_le hC1 hc (by omega) (by omega)) measureReal_nonneg
  · -- the clock
    have hsub : stopEv (m n) (ΦD μ n) ⊆ {ω | (¬ ∃ k, IsMarkTime (m n) ω k) ∨
          ∃ k, IsMarkTime (m n) ω k ∧
            1 / ((m n : ℕ) : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / (m n : ℕ) - 1 / (μ 0).toReal|} := by
      rintro ω ⟨T, hT, hbad⟩
      right
      exact ⟨T, hT, clock_incl hm0 hm1 (by omega) hk.1 hk.2 (by omega) hbad⟩
    have h1 : (iidWalk μ).real (stopEv (m n) (ΦD μ n)) ≤ C2 * Real.exp (-c2 * ((m n : ℕ) : ℝ) ^ (1 / 2 : ℝ)) :=
      (measureReal_mono hsub (measure_ne_top _ _)).trans (hoe (m n))
    refine h1.trans ?_
    apply mul_le_mul_of_nonneg_left _ hC2.le
    apply Real.exp_le_exp.2
    rw [← Real.sqrt_eq_rpow]
    have hMr : (n : ℝ) / 4 ≤ (m n : ℝ) := by
      have : n ≤ 4 * m n := by omega
      have : (n : ℝ) ≤ 4 * (m n : ℝ) := by exact_mod_cast this
      linarith
    have hs : Real.sqrt n / 2 ≤ Real.sqrt (m n : ℝ) := by
      have : Real.sqrt ((n : ℝ) / 4) = Real.sqrt n / 2 := by
        rw [Real.sqrt_div (by positivity)]
        have : Real.sqrt 4 = 2 := by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
        rw [this]
      rw [← this]
      exact Real.sqrt_le_sqrt hMr
    nlinarith

theorem eq_i_lowerW {μ : PMF ℕ} (h : HypW μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {m : ℕ → ℕ} (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) {α : ℝ} (_hα : 0 < α) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ,
      (((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (prefixStepsIn (m n) {x | StepsLt p x})) ≤
        ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
            {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} +
          C * (1 - stepTail μ p) ^ ⌊(n : ℝ) / (4 * (μ 0).toReal)⌋₊ + C * Real.exp (-c * Real.sqrt n) := by
  obtain ⟨Kc, C2, c2, hKc, hC2, hc2, N, hN⟩ := eq_i_core h hnl hm
  obtain ⟨hm0, hm1⟩ := mu0_bounds h
  refine ⟨Kc * (1 + C2), c2, by positivity, hc2, N, fun n hn p => ?_⟩
  obtain ⟨h3, hk1, hkn, hQ, hD⟩ := hN n hn
  have hprob : IsProbabilityMeasure (iidWalk μ) := by unfold iidWalk; infer_instance
  set Q := (𝐏w[μ.toMeasure])[|bridgeAtMark n] with hQdef
  have hsub : prefixStepsIn (m n) {x | StepsLt p x} ⊆ stopEv (m n) (ΦD μ n) ∪ stopEv (m n) (ΦLt μ n p) := by
    rintro ω ⟨T, hT, hw⟩
    by_cases hb : clockBad μ n T
    · exact Or.inl ⟨T, hT, hb⟩
    · exact Or.inr ⟨T, hT, hb, hw⟩
  have h1 : Q.real (prefixStepsIn (m n) {x | StepsLt p x}) ≤
      Q.real (stopEv (m n) (ΦD μ n)) + Q.real (stopEv (m n) (ΦLt μ n p)) :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have h2 := hQ _ (prefDep_ΦD μ n)
  have h3' := hQ _ (prefDep_ΦLt μ n p)
  -- the cylinder
  have hcyl : stopEv (m n) (ΦLt μ n p) ⊆
      {ω : ℕ → ℕ | ∀ i < ⌊(n : ℝ) / (4 * (μ 0).toReal)⌋₊, (((ω i : ℤ) - 1 : ℤ) : ℝ) < p} := by
    rintro ω ⟨T, hT, hbad, hw⟩ i hi
    have hT' : (n : ℝ) / (4 * (μ 0).toReal) ≤ T := by
      by_contra hlt
      exact hbad (Or.inl (not_le.1 hlt))
    have hiT : i < T := by
      have h1 : (⌊(n : ℝ) / (4 * (μ 0).toReal)⌋₊ : ℝ) ≤ (n : ℝ) / (4 * (μ 0).toReal) :=
        Nat.floor_le (by positivity)
      have : (i : ℝ) < T := lt_of_lt_of_le (by exact_mod_cast hi) (h1.trans hT')
      exact_mod_cast this
    apply hw
    unfold walkWord
    exact List.mem_map.2 ⟨i, List.mem_range.2 hiT, rfl⟩
  have h4 : (iidWalk μ).real (stopEv (m n) (ΦLt μ n p)) ≤
      (1 - stepTail μ p) ^ ⌊(n : ℝ) / (4 * (μ 0).toReal)⌋₊ := by
    rw [← real_cylLt]
    exact measureReal_mono hcyl (measure_ne_top _ _)
  have hA : 0 ≤ Q.real {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} :=
    measureReal_nonneg
  have hpow : 0 ≤ (1 - stepTail μ p) ^ ⌊(n : ℝ) / (4 * (μ 0).toReal)⌋₊ := by
    have : 0 ≤ 1 - stepTail μ p := by
      rw [stepTail_eq]
      have := measureReal_le_one (μ := μ.toMeasure) (s := {x : ℕ | p ≤ (((x : ℤ) - 1 : ℤ) : ℝ)})
      linarith
    positivity
  have hexp : 0 ≤ Real.exp (-c2 * Real.sqrt n) := (Real.exp_pos _).le
  have e1 : Kc * (iidWalk μ).real (stopEv (m n) (ΦD μ n)) ≤ Kc * (C2 * Real.exp (-c2 * Real.sqrt n)) :=
    mul_le_mul_of_nonneg_left hD hKc.le
  have e2 : Kc * (iidWalk μ).real (stopEv (m n) (ΦLt μ n p)) ≤ Kc * (1 - stepTail μ p) ^ ⌊(n : ℝ) / (4 * (μ 0).toReal)⌋₊ :=
    mul_le_mul_of_nonneg_left h4 hKc.le
  nlinarith [mul_nonneg hKc.le hpow, mul_nonneg (mul_nonneg hKc.le hC2.le) hexp, mul_nonneg hC2.le hexp, mul_nonneg hKc.le hexp]

theorem eq_i_upperW {μ : PMF ℕ} (h : HypW μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {m : ℕ → ℕ} (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) {α : ℝ} (_hα : 0 < α) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ,
      (((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (prefixStepsIn (m n) {x | StepsGt q x})) ≤
        ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
            {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} +
          C * (1 - (1 - stepTail μ q) ^ ⌊(n : ℝ) / (μ 0).toReal⌋₊) + C * Real.exp (-c * Real.sqrt n) := by
  obtain ⟨Kc, C2, c2, hKc, hC2, hc2, N, hN⟩ := eq_i_core h hnl hm
  obtain ⟨hm0, hm1⟩ := mu0_bounds h
  refine ⟨Kc * (1 + C2), c2, by positivity, hc2, N, fun n hn q => ?_⟩
  obtain ⟨h3, hk1, hkn, hQ, hD⟩ := hN n hn
  have hprob : IsProbabilityMeasure (iidWalk μ) := by unfold iidWalk; infer_instance
  set Q := (𝐏w[μ.toMeasure])[|bridgeAtMark n] with hQdef
  have hsub : prefixStepsIn (m n) {x | StepsGt q x} ⊆ stopEv (m n) (ΦD μ n) ∪ stopEv (m n) (ΦGt μ n q) := by
    rintro ω ⟨T, hT, hw⟩
    by_cases hb : clockBad μ n T
    · exact Or.inl ⟨T, hT, hb⟩
    · exact Or.inr ⟨T, hT, hb, hw⟩
  have h1 : Q.real (prefixStepsIn (m n) {x | StepsGt q x}) ≤
      Q.real (stopEv (m n) (ΦD μ n)) + Q.real (stopEv (m n) (ΦGt μ n q)) :=
    (measureReal_mono hsub (measure_ne_top _ _)).trans (measureReal_union_le _ _)
  have h2 := hQ _ (prefDep_ΦD μ n)
  have h3' := hQ _ (prefDep_ΦGt μ n q)
  have hcyl : stopEv (m n) (ΦGt μ n q) ⊆
      {ω : ℕ → ℕ | ∃ i < ⌊(n : ℝ) / (μ 0).toReal⌋₊, q < (((ω i : ℤ) - 1 : ℤ) : ℝ)} := by
    rintro ω ⟨T, hT, hbad, hw⟩
    have hT' : (T : ℝ) ≤ (n : ℝ) / (μ 0).toReal := by
      by_contra hlt
      exact hbad (Or.inr (not_le.1 hlt))
    have hTf : T ≤ ⌊(n : ℝ) / (μ 0).toReal⌋₊ := Nat.le_floor hT'
    obtain ⟨a, ha, hqa⟩ := hw
    unfold walkWord at ha
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 ha
    exact ⟨i, lt_of_lt_of_le (List.mem_range.1 hi) hTf, hqa⟩
  have h4 : (iidWalk μ).real (stopEv (m n) (ΦGt μ n q)) ≤
      1 - (1 - stepTail μ q) ^ ⌊(n : ℝ) / (μ 0).toReal⌋₊ :=
    (measureReal_mono hcyl (measure_ne_top _ _)).trans (real_cylGt_le μ q _)
  have hA : 0 ≤ Q.real {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} :=
    measureReal_nonneg
  have hpow : 0 ≤ 1 - (1 - stepTail μ q) ^ ⌊(n : ℝ) / (μ 0).toReal⌋₊ := by
    have h0 : 0 ≤ 1 - stepTail μ q := by
      rw [stepTail_eq]
      have := measureReal_le_one (μ := μ.toMeasure) (s := {x : ℕ | q ≤ (((x : ℤ) - 1 : ℤ) : ℝ)})
      linarith
    have h1' : 1 - stepTail μ q ≤ 1 := by
      rw [stepTail_eq]
      have := measureReal_nonneg (μ := μ.toMeasure) (s := {x : ℕ | q ≤ (((x : ℤ) - 1 : ℤ) : ℝ)})
      linarith
    have := pow_le_one₀ h0 h1' (n := ⌊(n : ℝ) / (μ 0).toReal⌋₊)
    linarith
  have hexp : 0 ≤ Real.exp (-c2 * Real.sqrt n) := (Real.exp_pos _).le
  have e1 : Kc * (iidWalk μ).real (stopEv (m n) (ΦD μ n)) ≤ Kc * (C2 * Real.exp (-c2 * Real.sqrt n)) :=
    mul_le_mul_of_nonneg_left hD hKc.le
  have e2 : Kc * (iidWalk μ).real (stopEv (m n) (ΦGt μ n q)) ≤
      Kc * (1 - (1 - stepTail μ q) ^ ⌊(n : ℝ) / (μ 0).toReal⌋₊) :=
    mul_le_mul_of_nonneg_left h4 hKc.le
  nlinarith [mul_nonneg hKc.le hpow, mul_nonneg (mul_nonneg hKc.le hC2.le) hexp, mul_nonneg hC2.le hexp, mul_nonneg hKc.le hexp]

/-! ## The reverse half -/

section ReverseHalf

variable (μ : Measure ℕ) [IsProbabilityMeasure μ]

private theorem rh_indep (m : ℕ) : IndepFun (pref m) (shiftSeq m) (𝐏w[μ]) := by
  have hI : iIndepFun (fun (i : ℕ) (ω : ℕ → ℕ) => ω i) (𝐏w[μ]) :=
    iIndepFun_infinitePi (P := fun _ : ℕ => μ) (X := fun _ x => x) (fun _ => measurable_id)
  have h := hI.indepFun_set (Set.Iio m) (Set.Ici m)
    (Set.disjoint_left.2 fun x hx hx' => by simp only [Set.mem_Iio, Set.mem_Ici] at hx hx'; omega) (fun i => measurable_pi_apply i)
  have h2 := h.comp (φ := fun (s : Set.Iio m → ℕ) (i : Fin m) => s ⟨i, i.2⟩)
    (ψ := fun (s : Set.Ici m → ℕ) (i : ℕ) => s ⟨m + i, by simp⟩)
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
    (measurable_pi_iff.2 fun _ => measurable_pi_apply _)
  exact h2

private theorem rh_map_shift (m : ℕ) : (𝐏w[μ]).map (shiftSeq m) = 𝐏w[μ] :=
  Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ) (f := fun i : ℕ => m + i) (add_right_injective m)

/-- the last coordinate is independent of the prefix -/
private theorem rh_inter_coord (m' : ℕ) {S : Set (ℕ → ℕ)} (hS : ∀ ω ω' : ℕ → ℕ, (∀ i < m', ω i = ω' i) → (ω ∈ S ↔ ω' ∈ S))
    (A : Set ℕ) :
    (𝐏w[μ]) ({ω | ω m' ∈ A} ∩ S) = μ A * (𝐏w[μ]) S := by
  have hSe : S = pref m' ⁻¹' {y | extendZ m' y ∈ S} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    exact hS _ _ (extendZ_pref_agree m' ω)
  have hA : {ω : ℕ → ℕ | ω m' ∈ A} = shiftSeq m' ⁻¹' {s : ℕ → ℕ | s 0 ∈ A} := by
    ext ω; simp [shiftSeq]
  have hAt : MeasurableSet {s : ℕ → ℕ | s 0 ∈ A} := (measurable_pi_apply 0) (MeasurableSet.of_discrete)
  have hind := (rh_indep μ m').measure_inter_preimage_eq_mul {y | extendZ m' y ∈ S} {s : ℕ → ℕ | s 0 ∈ A}
    (Set.to_countable _).measurableSet hAt
  have h1 : (𝐏w[μ]) (shiftSeq m' ⁻¹' {s : ℕ → ℕ | s 0 ∈ A}) = μ A := by
    rw [← Measure.map_apply (measurable_shiftSeq m') hAt, rh_map_shift]
    have h2 : (𝐏w[μ]).map (fun x : ℕ → ℕ => x 0) = μ := Measure.infinitePi_map_eval (fun _ : ℕ => μ) 0
    rw [show {s : ℕ → ℕ | s 0 ∈ A} = (fun x : ℕ → ℕ => x 0) ⁻¹' A from rfl,
      ← Measure.map_apply (measurable_pi_apply 0) MeasurableSet.of_discrete, h2]
  have hSe' : S = pref m' ⁻¹' {y | extendZ m' y ∈ S} := hSe
  calc (𝐏w[μ]) ({ω | ω m' ∈ A} ∩ S)
      = (𝐏w[μ]) (shiftSeq m' ⁻¹' {s : ℕ → ℕ | s 0 ∈ A} ∩ pref m' ⁻¹' {y | extendZ m' y ∈ S}) := by
        rw [← hA, ← hSe']
    _ = (𝐏w[μ]) (pref m' ⁻¹' {y | extendZ m' y ∈ S}) * (𝐏w[μ]) (shiftSeq m' ⁻¹' {s : ℕ → ℕ | s 0 ∈ A}) := by
        rw [Set.inter_comm]; exact hind
    _ = μ A * (𝐏w[μ]) S := by rw [h1, ← hSe', mul_comm]

end ReverseHalf

private theorem rh_mark_last {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (ω : ℕ → ℕ) :
    IsMarkTime n ω k ↔ ω (k - 1) = 0 ∧ walkLeafCount ω (k - 1) = n - 1 := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨h1, h2⟩
    have h3 := h2 j (by omega)
    rw [wlc_succ] at h1
    by_cases hj : ω j = 0
    · simp [hj] at h1; exact ⟨hj, by omega⟩
    · simp [hj] at h1; omega
  · rintro ⟨h1, h2⟩
    refine ⟨by rw [wlc_succ, h1, h2]; simp; omega, fun q hq => ?_⟩
    have := wlc_mono ω (show q ≤ j by omega)
    omega

private theorem rh_walkSum_succ (ω : ℕ → ℕ) (j : ℕ) : walkSum ω (j + 1) = walkSum ω j + ((ω j : ℤ) - 1) := by
  unfold walkSum; rw [Finset.sum_range_succ]

private theorem rh_mark_lt_iff {m T : ℕ} {ω : ℕ → ℕ} (hT : IsMarkTime m ω T) (i : ℕ) :
    (i < T ↔ walkLeafCount ω i < m) ∧ (T ≤ i ↔ m ≤ walkLeafCount ω i) := by
  have h1 : i < T ↔ walkLeafCount ω i < m := by
    constructor
    · exact hT.2 i
    · intro h
      by_contra hc
      have := wlc_mono ω (not_lt.1 hc)
      rw [hT.1] at this; omega
  refine ⟨h1, ?_⟩
  rw [← not_lt, h1, not_lt]

private theorem rh_mem_drop {ω : ℕ → ℕ} {k k' : ℕ} (a : ℤ) :
    a ∈ (walkWord ω k).drop k' ↔ ∃ i, k' ≤ i ∧ i < k ∧ a = (ω i : ℤ) - 1 := by
  rw [List.mem_iff_getElem?]
  constructor
  · rintro ⟨j, hj⟩
    rw [List.getElem?_drop] at hj
    unfold walkWord at hj
    rw [List.getElem?_map] at hj
    by_cases hlt : k' + j < k
    · rw [List.getElem?_range hlt] at hj
      simp only [Option.map_some, Option.some.injEq] at hj
      exact ⟨k' + j, by omega, hlt, hj.symm⟩
    · rw [List.getElem?_eq_none (by simp; omega)] at hj
      simp at hj
  · rintro ⟨i, h1, h2, rfl⟩
    refine ⟨i - k', ?_⟩
    rw [List.getElem?_drop]
    unfold walkWord
    rw [List.getElem?_map, show k' + (i - k') = i by omega, List.getElem?_range h2]
    rfl

private theorem rh_mem_word {ω : ℕ → ℕ} {k : ℕ} (a : ℤ) :
    a ∈ walkWord ω k ↔ ∃ i, i < k ∧ a = (ω i : ℤ) - 1 := by
  have := rh_mem_drop (ω := ω) (k := k) (k' := 0) a
  simpa using this

private def Bk (n k : ℕ) : Set (ℕ → ℕ) := {ω | IsMarkTime n ω k ∧ walkSum ω k = -1}

private def HL (m' m : ℕ) (q : ℝ) (ω : ℕ → ℕ) : Prop :=
  q < -1 ∨ ∃ i < m', m ≤ walkLeafCount ω i ∧ q < (((ω i : ℤ) - 1 : ℤ) : ℝ)

private def HR (m' r : ℕ) (q : ℝ) (ω : ℕ → ℕ) : Prop :=
  ∃ i < m', walkLeafCount ω i < r ∧ q < (((ω i : ℤ) - 1 : ℤ) : ℝ)

private def LHSk (m k : ℕ) (q : ℝ) : Set (ℕ → ℕ) :=
  {ω | ∃ k', IsMarkTime m ω k' ∧ StepsGt q ((walkWord ω k).drop k')}

private theorem rh_bk_iff {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) (ω : ℕ → ℕ) :
    ω ∈ Bk n k ↔ ω (k - 1) = 0 ∧ ω ∈ timeReversalEvent (k - 1) (n - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  simp only [Bk, timeReversalEvent, Set.mem_ofPred_eq, Nat.add_sub_cancel]
  rw [rh_mark_last hn hk, rh_walkSum_succ]
  simp only [Nat.add_sub_cancel]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    refine ⟨h1, ?_, h2⟩
    rw [h1] at h3; simp at h3; linarith
  · rintro ⟨h1, h2, h3⟩
    refine ⟨⟨h1, h3⟩, ?_⟩
    rw [h1]; simp; linarith

private theorem Bk_inter_L {n m k : ℕ} (hm : 1 ≤ m) (hmn : m < n) (hk : 1 ≤ k) (q : ℝ) :
    Bk n k ∩ LHSk m k q =
      {ω | ω (k - 1) ∈ ({0} : Set ℕ)} ∩ (timeReversalEvent (k - 1) (n - 1) ∩ {ω | HL (k - 1) m q ω}) := by
  ext ω
  constructor
  · rintro ⟨hB, k', hk', hS⟩
    have hbk := (rh_bk_iff (by omega) hk ω).1 hB
    refine ⟨hbk.1, hbk.2, ?_⟩
    obtain ⟨a, ha, hqa⟩ := hS
    obtain ⟨i, hi1, hi2, rfl⟩ := (rh_mem_drop a).1 ha
    by_cases hik : i = k - 1
    · left
      subst hik
      rw [hbk.1] at hqa
      simpa using hqa
    · right
      refine ⟨i, by omega, ?_, hqa⟩
      exact ((rh_mark_lt_iff hk' i).2).1 hi1
  · rintro ⟨h1, h2, h3⟩
    have hB : ω ∈ Bk n k := (rh_bk_iff (by omega) hk ω).2 ⟨h1, h2⟩
    refine ⟨hB, ?_⟩
    obtain ⟨k', hk'le, hk'⟩ := BGWLeaves.MaxDegree.Transfer.exists_isMarkTime_of_le hB.1 hmn.le
    have hk'ne : k' ≠ k := by
      rintro rfl
      have := hB.1.1; have := hk'.1; omega
    refine ⟨k', hk', ?_⟩
    rcases h3 with hq | ⟨i, hi, hmi, hq⟩
    · refine ⟨-1, (rh_mem_drop (-1)).2 ⟨k - 1, by omega, by omega, ?_⟩, by simpa using hq⟩
      have : ω (k - 1) = 0 := h1
      rw [this]; simp
    · refine ⟨(ω i : ℤ) - 1, (rh_mem_drop _).2 ⟨i, ?_, by omega, rfl⟩, hq⟩
      exact ((rh_mark_lt_iff hk' i).2).2 hmi

private theorem Bk_inter_R {n m k : ℕ} (hm : 1 ≤ m) (hmn : m < n) (hk : 1 ≤ k) (q : ℝ) :
    Bk n k ∩ prefixStepsIn (n - m) {x | StepsGt q x} =
      {ω | ω (k - 1) ∈ ({0} : Set ℕ)} ∩ (timeReversalEvent (k - 1) (n - 1) ∩ {ω | HR (k - 1) (n - m) q ω}) := by
  ext ω
  constructor
  · rintro ⟨hB, T, hT, hS⟩
    have hbk := (rh_bk_iff (by omega) hk ω).1 hB
    refine ⟨hbk.1, hbk.2, ?_⟩
    obtain ⟨a, ha, hqa⟩ := hS
    obtain ⟨i, hi, rfl⟩ := (rh_mem_word a).1 ha
    have hiL : walkLeafCount ω i < n - m := ((rh_mark_lt_iff hT i).1).1 hi
    refine ⟨i, ?_, hiL, hqa⟩
    by_contra hcon
    have := wlc_mono ω (show k - 1 ≤ i by omega)
    have h2 : walkLeafCount ω (k - 1) = n - 1 := hbk.2.2
    omega
  · rintro ⟨h1, h2, i, hi, hiL, hq⟩
    have hB : ω ∈ Bk n k := (rh_bk_iff (by omega) hk ω).2 ⟨h1, h2⟩
    refine ⟨hB, ?_⟩
    obtain ⟨T, hTle, hT⟩ := BGWLeaves.MaxDegree.Transfer.exists_isMarkTime_of_le hB.1 (Nat.sub_le n m)
    refine ⟨T, hT, (ω i : ℤ) - 1, ?_, hq⟩
    exact (rh_mem_word _).2 ⟨i, ((rh_mark_lt_iff hT i).1).2 hiL, rfl⟩

/-! ### Path-level formulation -/

private def pe {m' : ℕ} (p : Fin (m' + 1) → ℤ) : ℕ → ℤ := fun i => if h : i < m' + 1 then p ⟨i, h⟩ else 0

private def stp {m' : ℕ} (p : Fin (m' + 1) → ℤ) (j : ℕ) : ℤ := pe p (j + 1) - pe p j

private def cnt {m' : ℕ} (p : Fin (m' + 1) → ℤ) (i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => stp p j = -1).card

private def Ψ {m' : ℕ} (r : ℕ) (q : ℝ) (p : Fin (m' + 1) → ℤ) : Prop :=
  ∃ i < m', cnt p i < r ∧ q < ((stp p i : ℤ) : ℝ)

private theorem pe_walkPath (m' : ℕ) (ω : ℕ → ℕ) {j : ℕ} (hj : j ≤ m') : pe (walkPath m' ω) j = walkSum ω j := by
  unfold pe walkPath
  rw [dite_eq_left (by omega)]

private theorem stp_walkPath (m' : ℕ) (ω : ℕ → ℕ) {j : ℕ} (hj : j < m') :
    stp (walkPath m' ω) j = (ω j : ℤ) - 1 := by
  unfold stp
  rw [pe_walkPath m' ω (by omega), pe_walkPath m' ω hj.le, rh_walkSum_succ]; ring

private theorem cnt_walkPath (m' : ℕ) (ω : ℕ → ℕ) {i : ℕ} (hi : i ≤ m') : cnt (walkPath m' ω) i = walkLeafCount ω i := by
  unfold cnt walkLeafCount
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [stp_walkPath m' ω (by have := Finset.mem_range.1 hj; omega)]

private theorem rh_HR_iff (m' r : ℕ) (q : ℝ) (ω : ℕ → ℕ) : HR m' r q ω ↔ Ψ r q (walkPath m' ω) := by
  unfold HR Ψ
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, hi, by rw [cnt_walkPath m' ω hi.le]; exact h1, by rw [stp_walkPath m' ω hi]; exact h2⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, hi, by rw [cnt_walkPath m' ω hi.le] at h1; exact h1, by rw [stp_walkPath m' ω hi] at h2; exact h2⟩

private theorem pe_rev (m' : ℕ) (ω : ℕ → ℕ) {j : ℕ} (hj : j ≤ m') :
    pe (reversedPath m' ω) j = walkSum ω m' - walkSum ω (m' - j) := by
  unfold pe reversedPath
  rw [dite_eq_left (by omega)]

private theorem stp_rev (m' : ℕ) (ω : ℕ → ℕ) {j : ℕ} (hj : j < m') :
    stp (reversedPath m' ω) j = (ω (m' - 1 - j) : ℤ) - 1 := by
  unfold stp
  rw [pe_rev m' ω (by omega), pe_rev m' ω hj.le]
  have : m' - j = (m' - 1 - j) + 1 := by omega
  rw [show m' - (j + 1) = m' - 1 - j by omega, this, rh_walkSum_succ]; ring

private theorem cnt_rev_add (m' : ℕ) (ω : ℕ → ℕ) {i : ℕ} (hi : i ≤ m') :
    cnt (reversedPath m' ω) i + walkLeafCount ω (m' - i) = walkLeafCount ω m' := by
  induction i with
  | zero => simp [cnt]
  | succ i ih =>
    have hi' : i ≤ m' := by omega
    have h1 := ih hi'
    have hs : cnt (reversedPath m' ω) (i + 1) =
        cnt (reversedPath m' ω) i + if ω (m' - 1 - i) = 0 then 1 else 0 := by
      unfold cnt
      rw [Finset.range_add_one, Finset.filter_insert]
      have : (stp (reversedPath m' ω) i = -1) ↔ ω (m' - 1 - i) = 0 := by
        rw [stp_rev m' ω (by omega)]
        constructor
        · intro h; omega
        · intro h; rw [h]; simp
      by_cases hz : ω (m' - 1 - i) = 0
      · rw [ite_eq_left (this.2 hz), ite_eq_left hz, Finset.card_insert_of_notMem (by simp)]
      · rw [ite_eq_right (fun h => hz (this.1 h)), ite_eq_right hz]; simp
    have hw : walkLeafCount ω (m' - i) = walkLeafCount ω (m' - (i + 1)) + if ω (m' - 1 - i) = 0 then 1 else 0 := by
      rw [show m' - i = (m' - (i + 1)) + 1 by omega, wlc_succ, show m' - (i + 1) = m' - 1 - i by omega]
    omega

private theorem rh_HL_iff {m' m n : ℕ} (hm : 1 ≤ m) (hmn : m < n) (q : ℝ) {ω : ℕ → ℕ}
    (hω : ω ∈ timeReversalEvent m' (n - 1)) :
    HL m' m q ω ↔ Ψ (n - m) q (reversedPath m' ω) := by
  have hΛ : walkLeafCount ω m' = n - 1 := hω.2
  have hΛle : walkLeafCount ω m' ≤ m' := wlc_le ω m'
  have hm'pos : 1 ≤ m' := by omega
  -- the reindexed form
  have key : Ψ (n - m) q (reversedPath m' ω) ↔
      ∃ i < m', m ≤ walkLeafCount ω (i + 1) ∧ q < (((ω i : ℤ) - 1 : ℤ) : ℝ) := by
    unfold Ψ
    constructor
    · rintro ⟨j, hj, h1, h2⟩
      refine ⟨m' - 1 - j, by omega, ?_, ?_⟩
      · have := cnt_rev_add m' ω hj.le
        have e : m' - j = (m' - 1 - j) + 1 := by omega
        rw [e] at this
        omega
      · rw [stp_rev m' ω hj] at h2; exact h2
    · rintro ⟨i, hi, h1, h2⟩
      refine ⟨m' - 1 - i, by omega, ?_, ?_⟩
      · have := cnt_rev_add m' ω (show m' - 1 - i ≤ m' by omega)
        have e : m' - (m' - 1 - i) = i + 1 := by omega
        rw [e] at this
        omega
      · rw [stp_rev m' ω (by omega), show m' - 1 - (m' - 1 - i) = i by omega]; exact h2
  rw [key]
  unfold HL
  constructor
  · rintro (hq | ⟨i, hi, h1, h2⟩)
    · refine ⟨m' - 1, by omega, ?_, ?_⟩
      · rw [show m' - 1 + 1 = m' by omega, hΛ]; omega
      · have : (0 : ℝ) ≤ (ω (m' - 1) : ℝ) := Nat.cast_nonneg _
        push_cast
        linarith
    · exact ⟨i, hi, h1.trans (wlc_mono ω (Nat.le_succ i)), h2⟩
  · rintro ⟨i, hi, h1, h2⟩
    by_cases hq : q < -1
    · exact Or.inl hq
    · right
      refine ⟨i, hi, ?_, h2⟩
      rw [not_lt] at hq
      have hne : ω i ≠ 0 := by
        intro h0
        rw [h0] at h2
        push_cast at h2
        linarith
      have := wlc_succ ω i
      rw [ite_eq_right hne] at this
      omega

/-! ### Prefix dependence and measurability -/

private theorem rh_meas {m' : ℕ} {S : Set (ℕ → ℕ)} (hS : ∀ ω ω' : ℕ → ℕ, (∀ i < m', ω i = ω' i) → (ω ∈ S ↔ ω' ∈ S)) :
    MeasurableSet S := by
  have hSe : S = pref m' ⁻¹' {y | extendZ m' y ∈ S} := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    exact hS _ _ (extendZ_pref_agree m' ω)
  rw [hSe]
  exact measurable_pref m' (Set.to_countable _).measurableSet

private theorem rh_dep_TRE (m' n' : ℕ) {ω ω' : ℕ → ℕ} (h : ∀ i < m', ω i = ω' i) :
    ω ∈ timeReversalEvent m' n' ↔ ω' ∈ timeReversalEvent m' n' := by
  simp only [timeReversalEvent, Set.mem_ofPred_eq, walkSum_congr h, wlc_congr h]

private theorem rh_dep_HL (m' m : ℕ) (q : ℝ) {ω ω' : ℕ → ℕ} (h : ∀ i < m', ω i = ω' i) :
    HL m' m q ω ↔ HL m' m q ω' := by
  unfold HL
  constructor
  · rintro (hq | ⟨i, hi, h1, h2⟩)
    · exact Or.inl hq
    · exact Or.inr ⟨i, hi, by rwa [← wlc_congr (fun j hj => h j (by omega))], by rwa [← h i hi]⟩
  · rintro (hq | ⟨i, hi, h1, h2⟩)
    · exact Or.inl hq
    · exact Or.inr ⟨i, hi, by rwa [wlc_congr (fun j hj => h j (by omega))], by rwa [h i hi]⟩

private theorem rh_dep_HR (m' r : ℕ) (q : ℝ) {ω ω' : ℕ → ℕ} (h : ∀ i < m', ω i = ω' i) :
    HR m' r q ω ↔ HR m' r q ω' := by
  unfold HR
  constructor
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, hi, by rwa [← wlc_congr (fun j hj => h j (by omega))], by rwa [← h i hi]⟩
  · rintro ⟨i, hi, h1, h2⟩
    exact ⟨i, hi, by rwa [wlc_congr (fun j hj => h j (by omega))], by rwa [h i hi]⟩

/-! ### The reversal on atoms of paths -/

private theorem rh_rev_measure (μ : Measure ℕ) [IsProbabilityMeasure μ] (m' n' : ℕ) (S : Set (Fin (m' + 1) → ℤ)) :
    (𝐏w[μ]) (timeReversalEvent m' n' ∩ walkPath m' ⁻¹' S) =
      (𝐏w[μ]) (timeReversalEvent m' n' ∩ reversedPath m' ⁻¹' S) := by
  have hS : MeasurableSet S := (Set.to_countable S).measurableSet
  have hT := measurableSet_timeReversalEvent m' n'
  have hmap := BGWLeaves.timeReversal_map μ m' n'
  have h1 := congrArg (fun ν : Measure (Fin (m' + 1) → ℤ) => ν S) hmap
  simp only [Measure.map_apply (measurable_walkPath m') hS, Measure.map_apply (measurable_reversedPath m') hS] at h1
  rw [cond_apply hT, cond_apply hT] at h1
  by_cases h0 : (𝐏w[μ]) (timeReversalEvent m' n') = 0
  · have a1 : (𝐏w[μ]) (timeReversalEvent m' n' ∩ walkPath m' ⁻¹' S) = 0 :=
      measure_mono_null Set.inter_subset_left h0
    have a2 : (𝐏w[μ]) (timeReversalEvent m' n' ∩ reversedPath m' ⁻¹' S) = 0 :=
      measure_mono_null Set.inter_subset_left h0
    rw [a1, a2]
  · exact (ENNReal.mul_right_inj (ENNReal.inv_ne_zero.2 (measure_ne_top _ _)) (ENNReal.inv_ne_top.2 h0)).1 h1

/-! ### The identity of masses for a fixed `k` -/

private theorem rh_piece (μ : Measure ℕ) [IsProbabilityMeasure μ] {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) (q : ℝ) (k : ℕ) :
    (𝐏w[μ]) (Bk n k ∩ LHSk m k q) = (𝐏w[μ]) (Bk n k ∩ prefixStepsIn (n - m) {x | StepsGt q x}) := by
  by_cases hk : k = 0
  · subst hk
    have : Bk n 0 = ∅ := by
      ext ω
      simp only [Bk, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, -⟩
      have := h1.1
      simp [walkLeafCount] at this
      omega
    rw [this]; simp
  · have hk1 : 1 ≤ k := by omega
    rw [Bk_inter_L hm hmn hk1 q, Bk_inter_R hm hmn hk1 q]
    have hdL : ∀ ω ω' : ℕ → ℕ, (∀ i < k - 1, ω i = ω' i) →
        (ω ∈ timeReversalEvent (k - 1) (n - 1) ∩ {ω | HL (k - 1) m q ω} ↔
          ω' ∈ timeReversalEvent (k - 1) (n - 1) ∩ {ω | HL (k - 1) m q ω}) := by
      intro ω ω' h
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, rh_dep_TRE _ _ h, rh_dep_HL _ _ _ h]
    have hdR : ∀ ω ω' : ℕ → ℕ, (∀ i < k - 1, ω i = ω' i) →
        (ω ∈ timeReversalEvent (k - 1) (n - 1) ∩ {ω | HR (k - 1) (n - m) q ω} ↔
          ω' ∈ timeReversalEvent (k - 1) (n - 1) ∩ {ω | HR (k - 1) (n - m) q ω}) := by
      intro ω ω' h
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, rh_dep_TRE _ _ h, rh_dep_HR _ _ _ h]
    rw [rh_inter_coord μ (k - 1) hdL, rh_inter_coord μ (k - 1) hdR]
    congr 1
    -- reversal
    set S : Set (Fin (k - 1 + 1) → ℤ) := {p | Ψ (n - m) q p} with hSdef
    have e1 : timeReversalEvent (k - 1) (n - 1) ∩ {ω | HL (k - 1) m q ω} =
        timeReversalEvent (k - 1) (n - 1) ∩ reversedPath (k - 1) ⁻¹' S := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, hSdef]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨h1, (rh_HL_iff hm hmn q h1).1 h2⟩
      · rintro ⟨h1, h2⟩; exact ⟨h1, (rh_HL_iff hm hmn q h1).2 h2⟩
    have e2 : timeReversalEvent (k - 1) (n - 1) ∩ {ω | HR (k - 1) (n - m) q ω} =
        timeReversalEvent (k - 1) (n - 1) ∩ walkPath (k - 1) ⁻¹' S := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_preimage, hSdef]
      rw [rh_HR_iff]
    rw [e1, e2, rh_rev_measure]

private theorem rh_Bk_meas {n : ℕ} (hn : 1 ≤ n) (k : ℕ) : MeasurableSet (Bk n k) := by
  by_cases hk : k = 0
  · subst hk
    have : Bk n 0 = ∅ := by
      ext ω
      simp only [Bk, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨h1, -⟩
      have := h1.1
      simp [walkLeafCount] at this
      omega
    rw [this]; exact MeasurableSet.empty
  · have hk1 : 1 ≤ k := by omega
    have : Bk n k = {ω | ω (k - 1) ∈ ({0} : Set ℕ)} ∩ timeReversalEvent (k - 1) (n - 1) := by
      ext ω
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact rh_bk_iff hn hk1 ω
    rw [this]
    exact ((measurable_pi_apply (k - 1)) (MeasurableSet.of_discrete)).inter (measurableSet_timeReversalEvent _ _)

private theorem rh_Bk_disjoint {n : ℕ} : Pairwise (Function.onFun Disjoint (Bk n)) := by
  intro k k' hkk'
  rw [Function.onFun, Set.disjoint_left]
  intro ω h1 h2
  exact hkk' (BGWLeaves.IsMarkTime.unique h1.1 h2.1)

theorem bridge_reverse_half (μ : Measure ℕ) [IsProbabilityMeasure μ] {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n)
    (q : ℝ) :
    ((𝐏w[μ])[|bridgeAtMark n])
        {ω | ∃ k, IsMarkTime n ω k ∧ walkSum ω k = -1 ∧ ∃ k', IsMarkTime m ω k' ∧
          StepsGt q ((walkWord ω k).drop k')} =
      ((𝐏w[μ])[|bridgeAtMark n]) (prefixStepsIn (n - m) {x | StepsGt q x}) := by
  have hn : 1 ≤ n := by omega
  have hBeq : bridgeAtMark n = ⋃ k, Bk n k := by
    ext ω; simp [bridgeAtMark, Bk]
  have hBm : MeasurableSet (bridgeAtMark n) := by
    rw [hBeq]; exact MeasurableSet.iUnion (rh_Bk_meas hn)
  rw [cond_apply hBm, cond_apply hBm]
  congr 1
  -- both intersections are disjoint unions over `k`
  have hL : bridgeAtMark n ∩ {ω | ∃ k, IsMarkTime n ω k ∧ walkSum ω k = -1 ∧ ∃ k', IsMarkTime m ω k' ∧
          StepsGt q ((walkWord ω k).drop k')} = ⋃ k, (Bk n k ∩ LHSk m k q) := by
    ext ω
    simp only [bridgeAtMark, Bk, LHSk, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨-, k, h1, h2, h3⟩; exact ⟨k, ⟨h1, h2⟩, h3⟩
    · rintro ⟨k, ⟨h1, h2⟩, h3⟩; exact ⟨⟨k, h1, h2⟩, k, h1, h2, h3⟩
  have hR : bridgeAtMark n ∩ prefixStepsIn (n - m) {x | StepsGt q x} =
      ⋃ k, (Bk n k ∩ prefixStepsIn (n - m) {x | StepsGt q x}) := by
    rw [hBeq, Set.iUnion_inter]
  have hmeasL : ∀ k, MeasurableSet (Bk n k ∩ LHSk m k q) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have : Bk n 0 ∩ LHSk m 0 q = ∅ := by
        have : Bk n 0 = ∅ := by
          ext ω
          simp only [Bk, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨h1, -⟩
          have := h1.1
          simp [walkLeafCount] at this
          omega
        rw [this]; simp
      rw [this]; exact MeasurableSet.empty
    · rw [Bk_inter_L hm hmn (by omega) q]
      refine ((measurable_pi_apply (k - 1)) (MeasurableSet.of_discrete)).inter (rh_meas (m' := k - 1) ?_)
      intro ω ω' h
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, rh_dep_TRE _ _ h, rh_dep_HL _ _ _ h]
  have hmeasR : ∀ k, MeasurableSet (Bk n k ∩ prefixStepsIn (n - m) {x | StepsGt q x}) := by
    intro k
    by_cases hk : k = 0
    · subst hk
      have : Bk n 0 ∩ prefixStepsIn (n - m) {x | StepsGt q x} = ∅ := by
        have : Bk n 0 = ∅ := by
          ext ω
          simp only [Bk, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
          rintro ⟨h1, -⟩
          have := h1.1
          simp [walkLeafCount] at this
          omega
        rw [this]; simp
      rw [this]; exact MeasurableSet.empty
    · rw [Bk_inter_R hm hmn (by omega) q]
      refine ((measurable_pi_apply (k - 1)) (MeasurableSet.of_discrete)).inter (rh_meas (m' := k - 1) ?_)
      intro ω ω' h
      simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, rh_dep_TRE _ _ h, rh_dep_HR _ _ _ h]
  have hdisjL : Pairwise (Function.onFun Disjoint fun k => Bk n k ∩ LHSk m k q) := fun k k' hkk' =>
    (rh_Bk_disjoint hkk').mono Set.inter_subset_left Set.inter_subset_left
  have hdisjR : Pairwise (Function.onFun Disjoint fun k => Bk n k ∩ prefixStepsIn (n - m) {x | StepsGt q x}) :=
    fun k k' hkk' => (rh_Bk_disjoint hkk').mono Set.inter_subset_left Set.inter_subset_left
  rw [hL, hR, measure_iUnion hdisjL hmeasL, measure_iUnion hdisjR hmeasR]
  exact tsum_congr (rh_piece μ hm hmn q)

/-! ## The exported statements (types with `h : HypH μ`) -/

theorem eq_i_lower {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {m : ℕ → ℕ} (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) {α : ℝ} (hα : 0 < α) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ p : ℝ,
      (((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (prefixStepsIn (m n) {x | StepsLt p x})) ≤
        ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
            {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} +
          C * (1 - stepTail μ p) ^ ⌊(n : ℝ) / (4 * (μ 0).toReal)⌋₊ + C * Real.exp (-c * Real.sqrt n) :=
  eq_i_lowerW h.toW hnl hm hα

theorem eq_i_upper {μ : PMF ℕ} (h : HypH μ) (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {m : ℕ → ℕ} (hm : ∀ n, n / 2 ≤ m n ∧ m n ≤ (n + 1) / 2) {α : ℝ} (hα : 0 < α) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ q : ℝ,
      (((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real (prefixStepsIn (m n) {x | StepsGt q x})) ≤
        ((𝐏w[μ.toMeasure])[|bridgeAtMark n]).real
            {ω | ∃ k, IsMarkTime (m n) ω k ∧ α * Real.sqrt n ≤ |(walkSum ω k : ℝ)|} +
          C * (1 - (1 - stepTail μ q) ^ ⌊(n : ℝ) / (μ 0).toReal⌋₊) + C * Real.exp (-c * Real.sqrt n) :=
  eq_i_upperW h.toW hnl hm hα

end BGWLeaves.MaxDegree.Bridge
