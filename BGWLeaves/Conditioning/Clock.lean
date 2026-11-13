module

public import BGWLeaves.Conditioning.Defs
import BGWLeaves.Conditioning.LeafTail
import BGWLeaves.LeafConcentration.WalkDeviation
import BGWLeaves.LeafConcentration.OeLemmas
import BGWLeaves.Vervaat.Discrete

/-!
# M6 provider `Clock`

Provider for Lemma 5.6: `clock_unconditioned_oe`, `clock_leafConditioned_oe`, `lem_CVf_i`, `lem_CVf_ii`.  The theorems proved here are the registered holes of
`BGWLeaves.Conditioning`; they are exported in namespace `BGWLeaves.Conditioning.Clock` with exactly the types of the
statements file.

Proof outline.  A deterministic inversion lemma (`clock_gen`) turns the two-sided control
`|c(m) - ρ (m - 1)| ≤ E` of an integer counter `c` on a window `[m1, m2]` into the control of the first index
`i0` with `k ≤ c (i0 + 1)`.  For the tree clock `T_k = treeLeafTime` the counter is
`c m = #{leaves among the first m vertices}`.  Unconditioned (5.6(i)): the window is `m ≤ n ≤ ζ`, the counter is
the walk counter of the first `n` steps, and the deviation is Lemma 2.5(i) (`lem_GdesDev_walk`) through
`tree_law_eq_walk_law`.  Leaf-conditioned (5.6(ii)): Corollary 3.3 gives the control for the counter at the scale
`ζ ≈ n / μ₀`.
-/

@[expose] public section

namespace BGWLeaves.Conditioning.Clock

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

/-! ## The generic inversion -/

/-- First index `i` with `k ≤ c (i + 1)`. -/
private noncomputable def clockOf (c : ℕ → ℕ) (k : ℕ) : ℕ∞ := ⨅ (i : ℕ) (_ : k ≤ c (i + 1)), (i : ℕ∞)

private theorem clockOf_eq {c : ℕ → ℕ} {k i0 : ℕ} (h1 : k ≤ c (i0 + 1))
    (h2 : ∀ i < i0, ¬ k ≤ c (i + 1)) : clockOf c k = (i0 : ℕ∞) := by
  unfold clockOf
  apply le_antisymm
  · exact iInf₂_le i0 h1
  · refine le_iInf₂ fun i hi => ?_
    have : i0 ≤ i := by
      by_contra hlt
      exact h2 i (not_le.1 hlt) hi
    exact_mod_cast this

private theorem treeLeafTime_eq_clockOf (t : PlaneTree) (k : ℕ) :
    treeLeafTime t k = clockOf (fun m => (t.degrees.take m).count 0) k := rfl

private theorem clock_gen {c : ℕ → ℕ} (hmono : Monotone c) {ρ E : ℝ} (hρ : 0 < ρ) (hE : 0 ≤ E)
    {k m1 m2 : ℕ}
    (hD : ∀ m : ℕ, m1 ≤ m → m ≤ m2 → |(c m : ℝ) - ρ * ((m : ℝ) - 1)| ≤ E)
    (hU : ((k : ℝ) + E) / ρ + 2 ≤ m2) (hU1 : (m1 : ℝ) ≤ ((k : ℝ) + E) / ρ)
    (hL : (m1 : ℝ) - 1 < ((k : ℝ) - E) / ρ) :
    ∃ i0 : ℕ, k ≤ c (i0 + 1) ∧ (∀ i < i0, ¬ k ≤ c (i + 1)) ∧ i0 + 1 ≤ m2 ∧
      ((k : ℝ) - E) / ρ ≤ i0 ∧ (i0 : ℝ) ≤ ((k : ℝ) + E) / ρ + 1 := by
  classical
  set x : ℝ := ((k : ℝ) + E) / ρ with hx
  have hx0 : 0 ≤ x := by positivity
  have hceil1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hceil2 : x ≤ ⌈x⌉₊ := Nat.le_ceil x
  have hm1c : m1 ≤ ⌈x⌉₊ := by exact_mod_cast hU1.trans hceil2
  have hm0 : ⌈x⌉₊ + 1 ≤ m2 := by
    have : ((⌈x⌉₊ + 1 : ℕ) : ℝ) ≤ m2 := by push_cast; linarith
    exact_mod_cast this
  have hex : ∃ i : ℕ, k ≤ c (i + 1) := by
    refine ⟨⌈x⌉₊, ?_⟩
    have h := hD (⌈x⌉₊ + 1) (by omega) hm0
    have h' := (abs_le.1 h).1
    have : (k : ℝ) ≤ c (⌈x⌉₊ + 1) := by
      push_cast at h'
      have : ρ * x = k + E := by rw [hx]; field_simp
      nlinarith
    exact_mod_cast this
  let i0 := Nat.find hex
  have hi0 : k ≤ c (i0 + 1) := Nat.find_spec hex
  have hi0min : ∀ i < i0, ¬ k ≤ c (i + 1) := fun i hi => Nat.find_min hex hi
  have hle : i0 ≤ ⌈x⌉₊ := Nat.find_min' hex (by
    -- the witness used above
    have h := hD (⌈x⌉₊ + 1) (by omega) hm0
    have h' := (abs_le.1 h).1
    have : (k : ℝ) ≤ c (⌈x⌉₊ + 1) := by
      push_cast at h'
      have : ρ * x = k + E := by rw [hx]; field_simp
      nlinarith
    exact_mod_cast this)
  refine ⟨i0, hi0, hi0min, by omega, ?_, ?_⟩
  · -- lower bound
    by_cases hlt : i0 + 1 < m1
    · exfalso
      have hm1m2 : m1 ≤ m2 := by omega
      have h1 : c (i0 + 1) ≤ c m1 := hmono hlt.le
      have h2 := (abs_le.1 (hD m1 le_rfl hm1m2)).2
      have h3 : (k : ℝ) ≤ c m1 := by exact_mod_cast hi0.trans h1
      have : ρ * ((m1 : ℝ) - 1) < k - E := by
        have := (lt_div_iff₀ hρ).1 hL
        linarith
      linarith
    · have h := (abs_le.1 (hD (i0 + 1) (not_lt.1 hlt) (by omega))).2
      have hk : (k : ℝ) ≤ c (i0 + 1) := by exact_mod_cast hi0
      push_cast at h
      rw [div_le_iff₀ hρ]
      linarith
  · have : (i0 : ℝ) ≤ ⌈x⌉₊ := by exact_mod_cast hle
    linarith

/-! ## Real-analysis helpers -/

private theorem rp34 {n : ℕ} (hn : 0 < n) : (n : ℝ) ^ (3 / 4 : ℝ) = n * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  calc (n : ℝ) ^ (3 / 4 : ℝ) = (n : ℝ) ^ ((1 : ℝ) + -(1 / 4 : ℝ)) := by norm_num
    _ = n * (n : ℝ) ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_add hn', Real.rpow_one]

private theorem eventually_rpow34_le {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ (3 / 4 : ℝ) ≤ ε * n := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [h1.eventually (ge_mem_nhds hε), eventually_ge_atTop 1] with n hn hn1
  rw [rp34 (by omega)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  nlinarith

private theorem eventually_rpow34_ge (K : ℝ) : ∀ᶠ n : ℕ in atTop, K ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
  have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (3 / 4 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 4)).comp tendsto_natCast_atTop_atTop
  exact h1.eventually (eventually_ge_atTop K)

private theorem eventually_nat_ge (K : ℝ) : ∀ᶠ n : ℕ in atTop, K ≤ (n : ℝ) := by
  exact tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop K)

private theorem not_clockDev {n : ℕ} (hn : 0 < n) {β : ℝ} {i0 : ℕ} {T : ℕ∞} (hT : T = (i0 : ℕ∞))
    (h : |(i0 : ℝ) - β * n| ≤ (n : ℝ) ^ (3 / 4 : ℝ)) : ¬ ClockDev n β T := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  unfold ClockDev
  rintro (h1 | h1)
  · rw [hT] at h1
    exact ENat.natCast_ne_top _ h1
  · rw [hT, ENat.toNat_natCast] at h1
    have e : (i0 : ℝ) / n - β = ((i0 : ℝ) - β * n) / n := by field_simp
    rw [e, abs_div, abs_of_pos hn', lt_div_iff₀ hn'] at h1
    rw [rp34 hn] at h
    have : (n : ℝ) ^ (-(1 / 4 : ℝ)) * n ≤ |(i0 : ℝ) - β * n| := h1.le
    nlinarith

private theorem count_take_mono (l : List ℕ) : Monotone (fun m => (l.take m).count 0) := by
  intro a b hab
  have : l.take a = (l.take b).take a := by rw [List.take_take, min_eq_left hab]
  show (l.take a).count 0 ≤ (l.take b).count 0
  rw [this]
  exact (List.take_sublist _ _).count_le _

private theorem count_take_eq_walk {t : PlaneTree} {ω : ℕ → ℕ}
    (hω : ω ∈ stoppedWordEvent 1 t.increments) {m : ℕ} (hm : m ≤ t.size) :
    (t.degrees.take m).count 0 = walkLeafCount ω m := by
  rw [walkLeafCount_eq_sum t ω hω hm, count_zero_eq_sum]
  have hlen : (t.degrees.take m).length = m := by simp [PlaneTree.length_degrees, hm]
  rw [hlen]
  refine Finset.sum_congr rfl fun j hj => ?_
  have : j < m := Finset.mem_range.1 hj
  unfold childCountAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt this]

private theorem critical_zero_ne_one {μ : PMF ℕ} (hc : IsCritical μ) : μ 0 ≠ 1 := by
  intro h
  have hsupp := (PMF.apply_eq_one_iff μ 0).1 h
  have hz : ∀ j : ℕ, j ≠ 0 → μ j = 0 := fun j hj => by
    by_contra hne
    have : j ∈ μ.support := (PMF.mem_support_iff μ j).2 hne
    rw [hsupp] at this
    exact hj (by simpa using this)
  have hsum : ∑' j : ℕ, (j : ℝ≥0∞) * μ j = 0 := by
    have hh : ∀ j : ℕ, (j : ℝ≥0∞) * μ j = 0 := by
      intro j
      by_cases hj : j = 0
      · simp [hj]
      · simp [hz j hj]
    simp [hh]
  exact zero_ne_one (hsum.symm.trans hc)

private theorem toReal_zero_pos {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    0 < (μ 0).toReal ∧ (μ 0).toReal < 1 := by
  refine ⟨ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (PMF.apply_ne_top _ _), ?_⟩
  have : μ 0 < 1 := lt_of_le_of_ne (PMF.coe_le_one μ 0) (critical_zero_ne_one hc)
  have := (ENNReal.toReal_lt_toReal (PMF.apply_ne_top _ _) ENNReal.one_ne_top).2 this
  simpa using this

/-! ## 5.6(i): the unconditioned clock -/

/-- The large-`n` conditions of the unconditioned inversion (`x = n^{3/4}`). -/
private theorem eventually_good_unc {a p : ℝ} (ha1 : a < 1) (ha : 0 < a) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (3 / 4 : ℝ) / 2 + 2 ≤ (1 - a) / 2 * n ∧
      2 * p + 1 + p * (n : ℝ) ^ (3 / 4 : ℝ) / 2 ≤ p * a * n / 4 ∧
      2 ≤ (n : ℝ) ^ (3 / 4 : ℝ) ∧ 2 ≤ p * (n : ℝ) ^ (3 / 4 : ℝ) ∧ 1 ≤ n := by
  have hε : 0 < min ((1 - a) / 2) (a / 4) := lt_min (by linarith) (by linarith)
  filter_upwards [eventually_rpow34_le hε,
    eventually_rpow34_ge (2 / p + 2),
    eventually_nat_ge (8 / (1 - a) + 8 * (2 * p + 1) / (p * a) + 1), eventually_ge_atTop 1]
    with n h1 h2 h3 h4
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hxa : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (1 - a) / 2 * n :=
    h1.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  have hxb : (n : ℝ) ^ (3 / 4 : ℝ) ≤ a / 4 * n :=
    h1.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  have hpos1 : 0 < 1 - a := by linarith
  have hpos2 : 0 < p * a := mul_pos hp ha
  have e1 : 8 / (1 - a) ≤ n := by
    have : 0 ≤ 8 * (2 * p + 1) / (p * a) := by positivity
    have : 0 ≤ 8 / (1 - a) := by positivity
    linarith
  have e2 : 8 * (2 * p + 1) / (p * a) ≤ n := by
    have : 0 ≤ 8 * (2 * p + 1) / (p * a) := by positivity
    have : 0 ≤ 8 / (1 - a) := by positivity
    linarith
  rw [div_le_iff₀ hpos1] at e1
  rw [div_le_iff₀ hpos2] at e2
  have hx2 : 2 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
    have : 0 ≤ 2 / p := by positivity
    linarith
  have hpx : 2 ≤ p * (n : ℝ) ^ (3 / 4 : ℝ) := by
    have : 2 / p ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by linarith
    rw [div_le_iff₀ hp] at this
    linarith
  refine ⟨?_, ?_, hx2, hpx, h4⟩
  · nlinarith
  · have : p * (n : ℝ) ^ (3 / 4 : ℝ) ≤ p * (a / 4 * n) := mul_le_mul_of_nonneg_left hxb hp.le
    nlinarith

private theorem unc_main {p : ℝ} (hp0 : 0 < p) {a α : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hα : α < min (a / 2) ((1 - a) / 2)) {n : ℕ}
    (hR1 : (n : ℝ) ^ (3 / 4 : ℝ) / 2 + 2 ≤ (1 - a) / 2 * n)
    (hR2 : 2 * p + 1 + p * (n : ℝ) ^ (3 / 4 : ℝ) / 2 ≤ p * a * n / 4)
    (hR3 : 2 ≤ (n : ℝ) ^ (3 / 4 : ℝ)) (hR4 : 2 ≤ p * (n : ℝ) ^ (3 / 4 : ℝ)) (hn1 : 1 ≤ n)
    {t : PlaneTree} {ω : ℕ → ℕ} (hω : ω ∈ stoppedWordEvent 1 t.increments) (hnt : n ≤ t.size)
    (hgood : ∀ s ∈ Set.Icc (a / 4) 1,
      |walkLeafDev p ω n s| ≤ (p / 2) / (n : ℝ) ^ (1 / 4 : ℝ))
    {b : ℝ} (hb : b ∈ Set.Ioo (a - α) (a + α)) :
    ¬ ClockDev n b (treeLeafTime t ⌊p * b * n⌋₊) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨ha0, ha1⟩ := ha
  have hα1 := lt_of_lt_of_le hα (min_le_left _ _)
  have hα2 := lt_of_lt_of_le hα (min_le_right _ _)
  have hb1 : a / 2 < b := by linarith [hb.1]
  have hb2 : b < (1 + a) / 2 := by linarith [hb.2]
  have hb0 : 0 < b := by linarith
  set x := (n : ℝ) ^ (3 / 4 : ℝ) with hx
  have hr : 0 < (n : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hn0 _
  have hxr : x = n * ((n : ℝ) ^ (1 / 4 : ℝ))⁻¹ := by
    rw [hx, rp34 hn1, Real.rpow_neg hn0.le]
  have hD : ∀ m : ℕ, ⌈a / 4 * n⌉₊ + 1 ≤ m → m ≤ n →
      |(((t.degrees.take m).count 0 : ℕ) : ℝ) - p * ((m : ℝ) - 1)| ≤ p * x / 2 := by
    intro m hm1 hm2
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hjc : ⌈a / 4 * n⌉₊ ≤ j := by omega
    have hj : a / 4 * n ≤ j := (Nat.le_ceil _).trans (by exact_mod_cast hjc)
    have hjn : (j : ℝ) ≤ n := by exact_mod_cast (by omega : j ≤ n)
    have hjpos : 0 < (j : ℝ) := by nlinarith
    have hs := hgood ((j : ℝ) / n) ⟨(le_div_iff₀ hn0).2 (by linarith), (div_le_one hn0).2 hjn⟩
    unfold walkLeafDev at hs
    have e1 : (n : ℝ) * ((j : ℝ) / n) = j := by field_simp
    rw [e1, Nat.floor_natCast] at hs
    rw [count_take_eq_walk hω (by omega)]
    have e : (walkLeafCount ω (j + 1) : ℝ) / j - p = ((walkLeafCount ω (j + 1) : ℝ) - p * j) / j := by
      field_simp
    rw [e, abs_div, abs_of_pos hjpos, div_le_iff₀ hjpos] at hs
    have e2 : (p / 2) / (n : ℝ) ^ (1 / 4 : ℝ) * n = p * x / 2 := by
      rw [hxr]; field_simp
    have : (p / 2) / (n : ℝ) ^ (1 / 4 : ℝ) * j ≤ (p / 2) / (n : ℝ) ^ (1 / 4 : ℝ) * n :=
      mul_le_mul_of_nonneg_left hjn (by positivity)
    push_cast
    rw [e2] at this
    have e3 : (j : ℝ) + 1 - 1 = j := by ring
    rw [e3]
    linarith
  set k := ⌊p * b * n⌋₊ with hk
  have hk1 : (k : ℝ) ≤ p * b * n := Nat.floor_le (by positivity)
  have hk2 : p * b * n < k + 1 := Nat.lt_floor_add_one _
  have hbn1 : p * (a / 2) * n ≤ p * b * n := by
    have := mul_le_mul_of_nonneg_left hb1.le (by positivity : 0 ≤ p * n)
    nlinarith
  have hxpos : 0 < x := by linarith
  have hcm : (k + p * x / 2) / p ≤ b * n + x / 2 := by
    rw [div_le_iff₀ hp0]; nlinarith
  have hcl := Nat.ceil_lt_add_one (by positivity : 0 ≤ a / 4 * (n : ℝ))
  obtain ⟨i0, h1, h2, h3, h4, h5⟩ := clock_gen (c := fun m => (t.degrees.take m).count 0)
    (count_take_mono _) hp0 (by positivity : 0 ≤ p * x / 2) (k := k) (m1 := ⌈a / 4 * n⌉₊ + 1)
    (m2 := n) hD
    (by
      have : b * n ≤ (1 + a) / 2 * n := by nlinarith
      linarith)
    (by
      rw [le_div_iff₀ hp0]; push_cast
      have : (⌈a / 4 * (n : ℝ)⌉₊ + 1 : ℝ) * p ≤ (a / 4 * n + 2) * p :=
        mul_le_mul_of_nonneg_right (by linarith) hp0.le
      nlinarith)
    (by
      rw [lt_div_iff₀ hp0]; push_cast
      have : (⌈a / 4 * (n : ℝ)⌉₊ : ℝ) * p ≤ (a / 4 * n + 1) * p :=
        mul_le_mul_of_nonneg_right (by linarith) hp0.le
      nlinarith)
  have hT : treeLeafTime t k = (i0 : ℕ∞) := by
    rw [treeLeafTime_eq_clockOf]
    exact clockOf_eq h1 h2
  refine not_clockDev hn1 hT (abs_le.2 ⟨?_, ?_⟩)
  · by_contra hlt
    have hlt := not_le.1 hlt
    rw [div_le_iff₀ hp0] at h4
    have := mul_lt_mul_of_pos_right (show (i0 : ℝ) < b * n - x by linarith) hp0
    nlinarith
  · linarith

theorem clock_unconditioned_oe {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {a α : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hα : α < min (a / 2) ((1 - a) / 2)) :
    IsOe (1 / 2) fun n : ℕ =>
      (bienaymeLaw μ.toMeasure).real
        (finiteTreeEvent fun t => n ≤ t.size ∧
          ∃ b ∈ Set.Ioo (a - α) (a + α),
            ClockDev n b (treeLeafTime t ⌊(μ 0).toReal * b * n⌋₊)) := by
  have h0 := hc.apply_zero_ne_zero hne
  have h1 := critical_zero_ne_one hc
  obtain ⟨hp0, hp1⟩ := toReal_zero_pos hc hne
  obtain ⟨C, c, hC, hcc, hb⟩ := BGWLeaves.lem_GdesDev_walk μ h0 h1 (η := a / 4) (δ := (μ 0).toReal / 2)
    (by linarith [ha.1]) (by linarith [ha.2]) (by linarith)
  apply LeafConcentration.WalkDeviation.isOe_of_eventually_bound (by norm_num)
    (fun n => measureReal_le_one) hC hcc
  filter_upwards [eventually_good_unc ha.2 ha.1 hp0] with n hn
  obtain ⟨hR1, hR2, hR3, hR4, hn1⟩ := hn
  have hlaw := congrArg ENNReal.toReal (tree_law_eq_walk_law μ (fun t : PlaneTree => n ≤ t.size ∧
    ∃ b ∈ Set.Ioo (a - α) (a + α), ClockDev n b (treeLeafTime t ⌊(μ 0).toReal * b * n⌋₊)))
  change (bienaymeLaw μ.toMeasure).real _ = _ at hlaw
  rw [hlaw]
  refine le_trans (measureReal_mono ?_ (measure_ne_top _ _)) (hb n)
  rintro ω ⟨t, ⟨hnt, b, hbI, hdev⟩, hω⟩
  by_contra hbad
  have hgood : ∀ s ∈ Set.Icc (a / 4) 1, |walkLeafDev (μ 0).toReal ω n s| ≤
      ((μ 0).toReal / 2) / (n : ℝ) ^ (1 / 4 : ℝ) := by
    intro s hs
    by_contra hlt
    have hlt := not_le.1 hlt
    exact hbad ((lt_supDev_iff (by positivity) _).2 ⟨s, hs, hlt⟩)
  exact unc_main hp0 ha hα hR1 hR2 hR3 hR4 hn1 hω hnt hgood hbI hdev

/-! ## 5.6(ii): the clock under `λ = n` -/

private theorem count_take_eq_sum (t : PlaneTree) {m : ℕ} (hm : m ≤ t.size) :
    (t.degrees.take m).count 0 = ∑ j ∈ Finset.range m, if childCountAt t j = 0 then 1 else 0 := by
  rw [count_zero_eq_sum]
  have hlen : (t.degrees.take m).length = m := by simp [PlaneTree.length_degrees, hm]
  rw [hlen]
  refine Finset.sum_congr rfl fun j hj => ?_
  have : j < m := Finset.mem_range.1 hj
  unfold childCountAt
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_take_of_lt this]

/-- The large-`n` conditions of the leaf-conditioned inversion (`x = n^{3/4}`). -/
private theorem eventually_good_cond {a p : ℝ} (ha1 : a < 1) (ha : 0 < a) (hp : 0 < p) :
    ∀ᶠ n : ℕ in atTop,
      p * ((n : ℝ) ^ (3 / 4 : ℝ) / 2 + 2) ≤ (1 - a) / 2 * n ∧
      a * p * (n : ℝ) ^ (3 / 4 : ℝ) / 16 + 2 * p + 1 + p * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ≤ a * n / 4 ∧
      2 ≤ (n : ℝ) ^ (3 / 4 : ℝ) ∧ 2 ≤ p * (n : ℝ) ^ (3 / 4 : ℝ) ∧ 1 ≤ n := by
  filter_upwards [eventually_rpow34_le (ε := min ((1 - a) / (4 * p)) (a / (8 * (1 + p)))) (by
      refine lt_min ?_ ?_
      · have : 0 < 1 - a := by linarith
        positivity
      · positivity),
    eventually_rpow34_ge (2 / p + 2),
    eventually_nat_ge (8 * p / (1 - a) * 2 + 16 * (2 * p + 1) / a + 1), eventually_ge_atTop 1]
    with n h1 h2 h3 h4
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hxa : (n : ℝ) ^ (3 / 4 : ℝ) ≤ (1 - a) / (4 * p) * n :=
    h1.trans (mul_le_mul_of_nonneg_right (min_le_left _ _) hn0)
  have hxb : (n : ℝ) ^ (3 / 4 : ℝ) ≤ a / (8 * (1 + p)) * n :=
    h1.trans (mul_le_mul_of_nonneg_right (min_le_right _ _) hn0)
  have hpos1 : 0 < 1 - a := by linarith
  have hx2 : 2 ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by
    have : 0 ≤ 2 / p := by positivity
    linarith
  have hpx : 2 ≤ p * (n : ℝ) ^ (3 / 4 : ℝ) := by
    have : 2 / p ≤ (n : ℝ) ^ (3 / 4 : ℝ) := by linarith
    rw [div_le_iff₀ hp] at this
    linarith
  have e1 : 8 * p / (1 - a) * 2 ≤ n := by
    have : 0 ≤ 16 * (2 * p + 1) / a := by positivity
    have : 0 ≤ 8 * p / (1 - a) * 2 := by positivity
    linarith
  have e2 : 16 * (2 * p + 1) / a ≤ n := by
    have : 0 ≤ 16 * (2 * p + 1) / a := by positivity
    have : 0 ≤ 8 * p / (1 - a) * 2 := by positivity
    linarith
  have e1' : 8 * p / (1 - a) * 2 = 16 * p / (1 - a) := by ring
  rw [e1', div_le_iff₀ hpos1] at e1
  rw [div_le_iff₀ ha] at e2
  have hx4 : p * (n : ℝ) ^ (3 / 4 : ℝ) ≤ (1 - a) / 4 * n := by
    have := mul_le_mul_of_nonneg_left hxa hp.le
    have e : p * ((1 - a) / (4 * p) * n) = (1 - a) / 4 * n := by field_simp
    linarith
  refine ⟨?_, ?_, hx2, hpx, h4⟩
  · nlinarith
  · have hxc : (n : ℝ) ^ (3 / 4 : ℝ) * (1 + p) ≤ a / 8 * n := by
      have := mul_le_mul_of_nonneg_right hxb (by positivity : (0 : ℝ) ≤ 1 + p)
      have e : a / (8 * (1 + p)) * n * (1 + p) = a / 8 * n := by field_simp
      linarith
    nlinarith

private theorem cond_main {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) {a α : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hα : α < min (a / 2) ((1 - a) / 2)) {n : ℕ}
    (hR1 : p * ((n : ℝ) ^ (3 / 4 : ℝ) / 2 + 2) ≤ (1 - a) / 2 * n)
    (hR2 : a * p * (n : ℝ) ^ (3 / 4 : ℝ) / 16 + 2 * p + 1 + p * (n : ℝ) ^ (3 / 4 : ℝ) / 4 ≤ a * n / 4)
    (hR3 : 2 ≤ (n : ℝ) ^ (3 / 4 : ℝ)) (hR4 : 2 ≤ p * (n : ℝ) ^ (3 / 4 : ℝ)) (hn1 : 1 ≤ n)
    {t : PlaneTree} (hlam : t.degreeCount 0 = n)
    (hgood : ∀ s ∈ Set.Icc (a / 4) 1,
      |treeLeafDev p t (t.size : ℝ) s| < (p ^ 2 / 8) / (n : ℝ) ^ (1 / 4 : ℝ))
    {b : ℝ} (hb : b ∈ Set.Ioo (a - α) (a + α)) :
    ¬ ClockDev n (b / p) (treeLeafTime t ⌊b * n⌋₊) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨ha0, ha1⟩ := ha
  have hα1 := lt_of_lt_of_le hα (min_le_left _ _)
  have hα2 := lt_of_lt_of_le hα (min_le_right _ _)
  have hb1 : a / 2 < b := by linarith [hb.1]
  have hb2 : b < (1 + a) / 2 := by linarith [hb.2]
  have hb0 : 0 < b := by linarith
  set x := (n : ℝ) ^ (3 / 4 : ℝ) with hx
  set r := (n : ℝ) ^ (1 / 4 : ℝ) with hr
  have hr1 : 1 ≤ r := Real.one_le_rpow (by exact_mod_cast hn1) (by norm_num)
  have hrpos : 0 < r := by linarith
  have hxr : x = n * r⁻¹ := by
    rw [hx, rp34 hn1, Real.rpow_neg hn0.le]
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (p ^ 2 / 8) / r := ⟨_, rfl⟩
  rw [← hε] at hgood
  have hε0 : 0 < ε := by rw [hε]; positivity
  have hεp : ε ≤ p / 8 := by
    rw [hε, div_le_iff₀ hrpos]
    nlinarith
  have hεx : ε * n = p ^ 2 / 8 * x := by
    rw [hε, hxr]; field_simp
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (t.size : ℝ) := ⟨_, rfl⟩
  rw [← hX] at hgood
  have hXpos : 0 < X := by
    have : (0 : ℝ) < (t.size : ℝ) := by exact_mod_cast t.size_pos
    rw [hX]; exact this
  -- size control from the deviation at s = 1
  have hs1 := hgood 1 ⟨by linarith, le_rfl⟩
  unfold treeLeafDev at hs1
  have hLam : Lambda t (X * 1) = n := by
    unfold Lambda
    rw [mul_one, hX]
    simp [hlam]
  rw [hLam, mul_one] at hs1
  obtain ⟨hs1a, hs1b⟩ := abs_lt.1 hs1
  have hA : (p - ε) * X < n := by
    have : p - ε < (n : ℝ) / X := by linarith
    rwa [lt_div_iff₀ hXpos] at this
  have hB : (n : ℝ) < (p + ε) * X := by
    have : (n : ℝ) / X < p + ε := by linarith
    rwa [div_lt_iff₀ hXpos] at this
  have hpX : p * X < 2 * n := by nlinarith only [hA, hεp, hXpos, hp0]
  have hεX : ε * X < p * x / 4 := by
    have h1 : p * (ε * X) < p * (p * x / 4) := by
      have e1 : p * (ε * X) = ε * (p * X) := by ring
      have e2 : ε * (2 * n) = p * (p * x / 4) := by
        have : ε * (2 * n) = 2 * (ε * n) := by ring
        rw [this, hεx]; ring
      rw [e1, ← e2]
      exact mul_lt_mul_of_pos_left hpX hε0
    exact lt_of_mul_lt_mul_left h1 hp0.le
  have hXlo : n - p * x / 4 < p * X := by nlinarith only [hB, hεX]
  have hXhi : p * X < n + p * x / 4 := by nlinarith only [hA, hεX]
  -- the counter control
  have hD : ∀ m : ℕ, ⌈a / 4 * X⌉₊ + 1 ≤ m → m ≤ t.size →
      |(((t.degrees.take m).count 0 : ℕ) : ℝ) - p * ((m : ℝ) - 1)| ≤ p * x / 4 := by
    intro m hm1 hm2
    obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    have hjc : ⌈a / 4 * X⌉₊ ≤ j := by omega
    have hj : a / 4 * X ≤ j := (Nat.le_ceil _).trans (by exact_mod_cast hjc)
    have hjX : (j : ℝ) < X := by
      have : (j : ℝ) < (t.size : ℝ) := by exact_mod_cast (by omega : j < t.size)
      rw [hX]; exact this
    have hjpos : 0 < (j : ℝ) := by nlinarith only [hj, hXpos, ha0]
    have hs := hgood ((j : ℝ) / X) ⟨(le_div_iff₀ hXpos).2 (by linarith),
      ((div_lt_one hXpos).2 hjX).le⟩
    unfold treeLeafDev at hs
    have e1 : X * ((j : ℝ) / X) = j := by field_simp
    rw [e1] at hs
    have hLam' : Lambda t (j : ℝ) = (t.degrees.take (j + 1)).count 0 := by
      unfold Lambda
      have : ¬ ((t.size : ℝ) ≤ j) := by rw [← hX]; exact not_le.2 hjX
      simp only [this, ↓reduceIte, Nat.floor_natCast]
      rw [count_take_eq_sum t (by omega)]
    rw [hLam'] at hs
    have e : (((t.degrees.take (j + 1)).count 0 : ℕ) : ℝ) / j - p =
        ((((t.degrees.take (j + 1)).count 0 : ℕ) : ℝ) - p * j) / j := by field_simp
    rw [e, abs_div, abs_of_pos hjpos, div_lt_iff₀ hjpos] at hs
    have : ε * j ≤ ε * X := mul_le_mul_of_nonneg_left hjX.le hε0.le
    have e3 : (((j + 1 : ℕ) : ℝ)) - 1 = j := by push_cast; ring
    rw [e3]
    linarith
  obtain ⟨k, hk⟩ : ∃ k : ℕ, k = ⌊b * n⌋₊ := ⟨_, rfl⟩
  rw [← hk]
  have hk1 : (k : ℝ) ≤ b * n := by rw [hk]; exact Nat.floor_le (by positivity)
  have hk2 : b * n < k + 1 := by rw [hk]; exact Nat.lt_floor_add_one _
  have hbn1 : (a / 2) * n ≤ b * n := by
    have := mul_le_mul_of_nonneg_right hb1.le hn0.le
    linarith
  have hbn2 : b * n ≤ (1 + a) / 2 * n := by
    have := mul_le_mul_of_nonneg_right hb2.le hn0.le
    linarith
  have hcl := Nat.ceil_lt_add_one (by positivity : 0 ≤ a / 4 * X)
  have hX1 : a / 4 * (p * X) < a / 4 * (n + p * x / 4) :=
    mul_lt_mul_of_pos_left hXhi (by linarith)
  have hX0 : 0 ≤ (X : ℝ) := hXpos.le
  obtain ⟨i0, h1, h2, h3, h4, h5⟩ := clock_gen (c := fun m => (t.degrees.take m).count 0)
    (count_take_mono _) hp0 (by positivity : 0 ≤ p * x / 4) (k := k) (m1 := ⌈a / 4 * X⌉₊ + 1)
    (m2 := t.size) hD
    (by
      have : ((k : ℝ) + p * x / 4) / p ≤ X - 2 := by
        rw [div_le_iff₀ hp0]; linarith
      rw [← hX]
      linarith)
    (by
      rw [le_div_iff₀ hp0]; push_cast
      have : (⌈a / 4 * X⌉₊ + 1 : ℝ) * p ≤ (a / 4 * X + 2) * p :=
        mul_le_mul_of_nonneg_right (by linarith) hp0.le
      linarith)
    (by
      rw [lt_div_iff₀ hp0]; push_cast
      have : (⌈a / 4 * X⌉₊ : ℝ) * p ≤ (a / 4 * X + 1) * p :=
        mul_le_mul_of_nonneg_right (by linarith) hp0.le
      linarith)
  have hT : treeLeafTime t k = (i0 : ℕ∞) := by
    rw [treeLeafTime_eq_clockOf]
    exact clockOf_eq h1 h2
  refine not_clockDev hn1 hT (abs_le.2 ⟨?_, ?_⟩)
  · by_contra hlt
    have hlt := not_le.1 hlt
    rw [div_le_iff₀ hp0] at h4
    have h6 : (i0 : ℝ) * p < (b / p * n - x) * p := mul_lt_mul_of_pos_right (by linarith) hp0
    have e : (b / p * n - x) * p = b * n - x * p := by field_simp
    rw [e] at h6
    linarith
  · have h6 : (i0 : ℝ) * p ≤ ((k : ℝ) + p * x / 4) / p * p + p := by
      have := mul_le_mul_of_nonneg_right (show (i0 : ℝ) ≤ ((k : ℝ) + p * x / 4) / p + 1 from h5) hp0.le
      linarith
    rw [div_mul_cancel₀ _ hp0.ne'] at h6
    have e : (b / p * n + x) * p = b * n + x * p := by field_simp
    by_contra hlt
    have hlt := not_le.1 hlt
    have h7 := mul_lt_mul_of_pos_right (show b / p * n + x < i0 - 0 by linarith) hp0
    rw [e] at h7
    linarith

/-- Extend an eventual exponential estimate on a set `S` across a finite initial segment. -/
private theorem isOeOn_of_bound {S : Set ℕ} {x : ℕ → ℝ} (hx : ∀ n, x n ≤ 1) {C c : ℝ} (hC : 0 < C)
    (hc : 0 < c) (N : ℕ) (h : ∀ n ∈ S, N ≤ n → x n ≤ C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) :
    IsOeOn S (1 / 2) x := by
  refine ⟨C + Real.exp (c * (N : ℝ) ^ (1 / 2 : ℝ)), c, by positivity, hc, fun n hnS => ?_⟩
  by_cases hn : N ≤ n
  · exact (h n hnS hn).trans (mul_le_mul_of_nonneg_right
      (by linarith [Real.exp_pos (c * (N : ℝ) ^ (1 / 2 : ℝ))]) (Real.exp_pos _).le)
  · have hpow : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (Nat.le_of_lt (not_le.1 hn)))
        (by norm_num)
    have he : 1 ≤ Real.exp (c * (N : ℝ) ^ (1 / 2 : ℝ)) * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    exact (hx n).trans (he.trans (by nlinarith [Real.exp_pos (-c * (n : ℝ) ^ (1 / 2 : ℝ))]))

private theorem cond_real_le_one' (P : Measure LocallyFinite.Tree) [IsProbabilityMeasure P]
    (s A : Set LocallyFinite.Tree) : (P[|s]).real A ≤ 1 := by
  by_cases hs : P s = 0
  · simp [cond_eq_zero_of_meas_eq_zero hs]
  · have := cond_isProbabilityMeasure (μ := P) hs
    exact measureReal_le_one

theorem clock_leafConditioned_oe {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {a α : ℝ}
    (ha : a ∈ Set.Ioo (0 : ℝ) 1) (hα : α < min (a / 2) ((1 - a) / 2)) :
    IsOeOn {n : ℕ | 1 ≤ n ∧ arithFactor μ {0} ∣ n - 1} (1 / 2) fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          ∃ b ∈ Set.Ioo (a - α) (a + α),
            ClockDev n (b / (μ 0).toReal) (treeLeafTime t ⌊b * n⌋₊))) := by
  obtain ⟨hp0, hp1⟩ := toReal_zero_pos hc hne
  obtain ⟨C, c, hC, hcc, hb⟩ := BGWLeaves.cor_Lambda_arith hc hne hap hDA (η := a / 4)
    (δ := (μ 0).toReal ^ 2 / 8) (by linarith [ha.1]) (by linarith [ha.2]) (by positivity)
  obtain ⟨N, hN⟩ := eventually_atTop.1 (eventually_good_cond ha.2 ha.1 hp0)
  refine isOeOn_of_bound (fun n => cond_real_le_one' _ _ _) hC hcc N fun n hnS hnN => ?_
  obtain ⟨hR1, hR2, hR3, hR4, hn1⟩ := hN n hnN
  refine le_trans ?_ (hb n hnS)
  set P := bienaymeLaw μ.toMeasure with hP
  set s := leafCountEvent n with hs
  have hEm := BGWLeaves.Vervaat.Discrete.measurableSet_finiteTreeEvent' (fun t : PlaneTree =>
    ∃ b ∈ Set.Ioo (a - α) (a + α), ClockDev n (b / (μ 0).toReal) (treeLeafTime t ⌊b * n⌋₊))
  have hBm := BGWLeaves.Vervaat.Discrete.measurableSet_finiteTreeEvent' (fun t : PlaneTree =>
    ENNReal.ofReal ((μ 0).toReal ^ 2 / 8 / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
      supDev (a / 4) (treeLeafDev (μ 0).toReal t (t.size : ℝ)))
  have key : (P[|s]) (finiteTreeEvent fun t =>
      ∃ b ∈ Set.Ioo (a - α) (a + α), ClockDev n (b / (μ 0).toReal) (treeLeafTime t ⌊b * n⌋₊)) ≤
      (P[|s]) (finiteTreeEvent fun t => ENNReal.ofReal ((μ 0).toReal ^ 2 / 8 / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
        supDev (a / 4) (treeLeafDev (μ 0).toReal t (t.size : ℝ))) := by
    rw [cond_apply' hEm P, cond_apply' hBm P]
    refine mul_le_mul_right (measure_mono ?_) _
    rintro T ⟨hsT, t, rfl, b, hbI, hdev⟩
    refine ⟨hsT, t, rfl, ?_⟩
    by_contra hbad
    have hbad := not_le.1 hbad
    obtain ⟨t', ht', hlam⟩ := hsT
    have htt : t' = t := PlaneTree.toLocallyFinite_injective ht'
    subst htt
    have hε0 : 0 < (μ 0).toReal ^ 2 / 8 / (n : ℝ) ^ (1 / 4 : ℝ) := by
      have : (0 : ℝ) < n := by exact_mod_cast hn1
      positivity
    have hgood : ∀ s' ∈ Set.Icc (a / 4) 1,
        |treeLeafDev (μ 0).toReal t' (t'.size : ℝ) s'| < (μ 0).toReal ^ 2 / 8 / (n : ℝ) ^ (1 / 4 : ℝ) := by
      intro s' hs'
      have hle : ENNReal.ofReal |treeLeafDev (μ 0).toReal t' (t'.size : ℝ) s'| ≤
          supDev (a / 4) (treeLeafDev (μ 0).toReal t' (t'.size : ℝ)) := by
        unfold supDev
        exact le_iSup₂ (f := fun u (_ : u ∈ Set.Icc (a / 4) 1) =>
          ENNReal.ofReal |treeLeafDev (μ 0).toReal t' (t'.size : ℝ) u|) s' hs'
      exact (ENNReal.ofReal_lt_ofReal_iff hε0).1 (lt_of_le_of_lt hle hbad)
    exact cond_main hp0 hp1 ha hα hR1 hR2 hR3 hR4 hn1 hlam hgood hbI hdev
  exact ENNReal.toReal_mono (measure_ne_top _ _) key

/-! ## Lemma 5.6 -/

private theorem cond_real_eq_mul_inv (P : Measure LocallyFinite.Tree) [IsFiniteMeasure P]
    (s : Set LocallyFinite.Tree) {A : Set LocallyFinite.Tree} (hA : MeasurableSet A) :
    (P[|s]).real A = (P.real s)⁻¹ * P.real (s ∩ A) := by
  simp only [measureReal_def, cond_apply' hA, ENNReal.toReal_mul, ENNReal.toReal_inv]

private theorem sizeGe_inter_finiteTreeEvent (n : ℕ) (Q : PlaneTree → Prop) :
    sizeGeEvent n ∩ finiteTreeEvent Q = finiteTreeEvent fun t => n ≤ t.size ∧ Q t := by
  ext T
  constructor
  · rintro ⟨hs, t, rfl, ht⟩
    have hsize : n ≤ t.size := by
      rcases hs with hinf | hsize
      · exact False.elim (hinf t.finiteVertices_toLocallyFinite)
      · simpa [ncard_present_toLocallyFinite] using hsize
    exact ⟨t, rfl, hsize, ht⟩
  · rintro ⟨t, rfl, hsize, ht⟩
    refine ⟨Or.inr ?_, t, rfl, ht⟩
    simpa [ncard_present_toLocallyFinite] using hsize

theorem lem_CVf_i {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) {a α : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hα : α < min (a / 2) ((1 - a) / 2)) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|sizeGeEvent n]).real
        (finiteTreeEvent fun t =>
          ∃ b ∈ Set.Ioo (a - α) (a + α),
            ClockDev n b (treeLeafTime t ⌊(μ 0).toReal * b * n⌋₊)))) atTop (𝓝 0) := by
  have hOe := clock_unconditioned_oe hc hne ha hα
  obtain ⟨c3, hc3, N, hN⟩ := LeafTail.sizeGe_poly_lower hc hne hap hDA (η := 1) one_pos
  obtain ⟨C, c, hC, hcc, hb⟩ := LeafConcentration.OeLemmas.IsOe.poly_mul (by norm_num) hOe (1 / θ + 1)
  have hlim : Tendsto (fun n : ℕ => C / c3 * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul_atTop_of_neg (by linarith : -c < 0)
    have h3 := Real.tendsto_exp_atBot.comp h2
    simpa using h3.const_mul (C / c3)
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop (max N 1)] with n hn
  have hn1 : 1 ≤ n := (le_max_right _ _).trans hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  set P := bienaymeLaw μ.toMeasure with hP
  have hEm := BGWLeaves.Vervaat.Discrete.measurableSet_finiteTreeEvent' (fun t : PlaneTree =>
    ∃ b ∈ Set.Ioo (a - α) (a + α), ClockDev n b (treeLeafTime t ⌊(μ 0).toReal * b * n⌋₊))
  rw [cond_real_eq_mul_inv P _ hEm, sizeGe_inter_finiteTreeEvent]
  have hlow := hN n ((le_max_left _ _).trans hn)
  have hq : (n : ℝ) ^ (-(1 / θ) - 1) = ((n : ℝ) ^ (1 / θ + 1))⁻¹ := by
    rw [← Real.rpow_neg hn0.le]; congr 1; ring
  rw [hq] at hlow
  have hpos : 0 < c3 * ((n : ℝ) ^ (1 / θ + 1))⁻¹ := by positivity
  have hx := hb n
  set xn := P.real (finiteTreeEvent fun t : PlaneTree => n ≤ t.size ∧
    ∃ b ∈ Set.Ioo (a - α) (a + α), ClockDev n b (treeLeafTime t ⌊(μ 0).toReal * b * n⌋₊)) with hxn
  have hxn0 : 0 ≤ xn := measureReal_nonneg
  calc (P.real (sizeGeEvent n))⁻¹ * xn ≤ (c3 * ((n : ℝ) ^ (1 / θ + 1))⁻¹)⁻¹ * xn :=
        mul_le_mul_of_nonneg_right (inv_anti₀ hpos hlow) hxn0
    _ = ((n : ℝ) ^ (1 / θ + 1) * xn) / c3 := by field_simp
    _ ≤ (C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) / c3 :=
        div_le_div_of_nonneg_right hx hc3.le
    _ = C / c3 * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by ring

theorem lem_CVf_ii {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
    (hDA : ∃ a, StableDomain μ θ a) {a α : ℝ} (ha : a ∈ Set.Ioo (0 : ℝ) 1)
    (hα : α < min (a / 2) ((1 - a) / 2)) :
    Tendsto (fun n : ℕ =>
      (((bienaymeLaw μ.toMeasure)[|leafCountEvent n]).real
        (finiteTreeEvent fun t =>
          ∃ b ∈ Set.Ioo (a - α) (a + α),
            ClockDev n (b / (μ 0).toReal) (treeLeafTime t ⌊b * n⌋₊)))) atTop (𝓝 0) := by
  obtain ⟨C, c, hC, hcc, hb⟩ := clock_leafConditioned_oe hc hne hap hDA ha hα
  have hlim : Tendsto (fun n : ℕ => C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop
    have h2 := h1.const_mul_atTop_of_neg (by linarith : -c < 0)
    have h3 := Real.tendsto_exp_atBot.comp h2
    simpa using h3.const_mul C
  refine squeeze_zero' (Eventually.of_forall fun n => measureReal_nonneg) ?_ hlim
  filter_upwards [eventually_ge_atTop 1] with n hn1
  by_cases hnS : n ∈ {n : ℕ | 1 ≤ n ∧ arithFactor μ {0} ∣ n - 1}
  · exact hb n hnS
  · have hndvd : ¬ arithFactor μ {0} ∣ n - 1 := fun h => hnS ⟨hn1, h⟩
    have h0 := BGWLeaves.leafProb_eq_zero_of_not_dvd hc hne hndvd
    have hn' : n - 1 + 1 = n := by omega
    rw [hn'] at h0
    have h1 : bienaymeLaw μ.toMeasure (leafCountEvent n) = 0 :=
      (measureReal_eq_zero_iff).1 h0
    rw [cond_eq_zero_of_meas_eq_zero h1]
    simp only [measureReal_def, Measure.coe_zero, Pi.zero_apply, ENNReal.toReal_zero]
    positivity

end BGWLeaves.Conditioning.Clock
