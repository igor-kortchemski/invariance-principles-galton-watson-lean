module

public import BGWLeaves.LeafMass.Defs
public import BGWLeaves.GeneralA.Defs
import BGWLeaves.ForestLaw
import BGWLeaves.Passage
public import Mathlib.NumberTheory.FrobeniusNumber

/-!
# Exact leaf counts: arithmetic

Proofs of `int_gcd_eq_arithFactor`, `exists_isSuppSpan`, `leafProb_eq_zero_of_not_dvd` and
`ltn_i_arith` (with exactly the types stated in `BGWLeaves.LeafMass`), together with the
public helpers they need: `arithFactor_zero_eq_setGcd` (`arithFactor μ {0}` is the
gcd of the nonnegative steps `{k - 1 : k ∈ supp μ, k ≥ 1}` of `Y`), `leafProb_pos_iff_mem_leafMonoid`
(`P[λ = n + 1] > 0` iff `n` is a sum of steps of `Y`), `leafMonoid_dvd`, `leafMonoid_eventually`,
`pi_eta_real_eq_intWalkProb` and `leafProb_series` (`P[λ = m] = ∑_p P[ζ = p, λ = m]`, each term
given by `eq_f`).

The support statement is proved from `eq_f` (Proposition 1.6 with `j = 1`, summed over the number of
vertices `p`): `{λ = m} = ⋃_p {ζ = p, λ = m}` and `P[ζ = p, λ = m]` is a product of nonzero factors
times `P[W'_{p-m} = m - 1]`, which is positive iff `m - 1` is a `(p-m)`-fold sum of atoms of `Y`.
Only `μ 0 > 0` and criticality are used, no aperiodicity.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory BGW.LocallyFinite BGW.StableTrees BGWLeaves
  BGWLeaves.StableAnalysis
open scoped ENNReal

namespace BGWLeaves.LeafMass.Arithmetic

theorem exists_two_le {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ k : ℕ, 2 ≤ k ∧ μ k ≠ 0 := by
  by_contra h
  push Not at h
  apply hne
  have : ∑' j : ℕ, (j : ℝ≥0∞) * μ j = μ 1 := by
    rw [tsum_eq_single 1]
    · simp
    · intro b hb
      rcases Nat.lt_or_ge b 2 with h2 | h2
      · have : b = 0 := by omega
        simp [this]
      · simp [h b h2]
  rw [← this]; exact hc

theorem mu_zero_ne_zero {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) : μ 0 ≠ 0 := by
  intro h0
  obtain ⟨k, hk2, hk⟩ := exists_two_le hc hne
  have hlt : ∑' j : ℕ, μ j < ∑' j : ℕ, (j : ℝ≥0∞) * μ j := by
    refine ENNReal.tsum_lt_tsum (i := k) (by rw [PMF.tsum_coe]; exact ENNReal.one_ne_top) ?_ ?_
    · intro j
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · simp [h0]
      · calc μ j = 1 * μ j := (one_mul _).symm
          _ ≤ (j : ℝ≥0∞) * μ j := by gcongr; exact_mod_cast hj
    · calc μ k < μ k + μ k := ENNReal.lt_add_right (PMF.apply_ne_top μ k) hk
        _ = 2 * μ k := (two_mul _).symm
        _ ≤ (k : ℝ≥0∞) * μ k := by gcongr; exact_mod_cast hk2
  rw [PMF.tsum_coe, hc] at hlt
  exact lt_irrefl _ hlt


/-! ## The gcd of the steps of `Y` -/

theorem arithFactor_isGreatest_of_two_le {μ : PMF ℕ} (h : ∃ k : ℕ, 2 ≤ k ∧ μ k ≠ 0) :
    IsGreatest {e : ℕ | 1 ≤ e ∧ ∀ s ∈ arithSet μ {0}, (e : ℤ) ∣ s}
      (Nat.setGcd {i : ℕ | μ (i + 1) ≠ 0}) := by
  obtain ⟨k, hk2, hk⟩ := h
  have hG : Nat.setGcd {i : ℕ | μ (i + 1) ≠ 0} ≠ 0 := by
    intro h0
    rw [Nat.setGcd_eq_zero_iff] at h0
    have : k - 1 ∈ {i : ℕ | μ (i + 1) ≠ 0} := by
      show μ (k - 1 + 1) ≠ 0
      rwa [Nat.sub_add_cancel (by omega)]
    have := h0 this
    simp at this
    omega
  refine ⟨⟨Nat.one_le_iff_ne_zero.2 hG, ?_⟩, ?_⟩
  · rintro s ⟨j, hj, ⟨hj0, rfl⟩ | ⟨hj0, rfl⟩⟩
    · simp only [Set.mem_singleton_iff] at hj0
      simp [hj0]
    · simp only [Set.mem_singleton_iff] at hj0
      obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have : (Nat.setGcd {i : ℕ | μ (i + 1) ≠ 0}) ∣ i := Nat.setGcd_dvd_of_mem hj
      have h2 := Int.natCast_dvd_natCast.2 this
      simpa using h2
  · rintro e ⟨he1, he⟩
    apply Nat.le_of_dvd (Nat.pos_of_ne_zero hG)
    rw [Nat.dvd_setGcd_iff]
    intro m hm
    have := he (m : ℤ) ⟨m + 1, hm, Or.inr ⟨by simp, by simp⟩⟩
    exact Int.natCast_dvd_natCast.1 this

theorem arithFactor_zero_eq_setGcd_of_two_le {μ : PMF ℕ} (h : ∃ k : ℕ, 2 ≤ k ∧ μ k ≠ 0) :
    arithFactor μ {0} = Nat.setGcd {i : ℕ | μ (i + 1) ≠ 0} :=
  (arithFactor_isGreatest_of_two_le h).csSup_eq

theorem arithFactor_zero_eq_setGcd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    arithFactor μ {0} = Nat.setGcd {i : ℕ | μ (i + 1) ≠ 0} :=
  arithFactor_zero_eq_setGcd_of_two_le (exists_two_le hc hne)

theorem two_le_of_isSuppSpan {μ : PMF ℕ} {d b : ℕ} (h : IsSuppSpan μ d b) :
    ∃ k : ℕ, 2 ≤ k ∧ μ k ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hd1, hdv, hdmax, hbmin⟩ := h
  have := hdmax (d + 1) (by omega) ⟨1, fun k hk hk0 => by
    have : k = 1 := by
      by_contra hk1
      exact hk (hcon k (by omega))
    subst this
    simp⟩
  omega

theorem int_gcd_eq_arithFactor {μ : PMF ℕ} {d b : ℕ} (h : IsSuppSpan μ d b) :
    Int.gcd ((b : ℤ) - 1) (d : ℤ) = arithFactor μ {0} := by
  have h2 := two_le_of_isSuppSpan h
  obtain ⟨k0, hk02, hk0⟩ := h2
  obtain ⟨hd1, hdv, hdmax, hbmin⟩ := h
  rw [arithFactor_zero_eq_setGcd_of_two_le ⟨k0, hk02, hk0⟩]
  set G := Nat.setGcd {i : ℕ | μ (i + 1) ≠ 0} with hGdef
  have hG1 : ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (G : ℤ) ∣ (k : ℤ) - 1 := by
    intro k hk hk0'
    have : G ∣ k - 1 := Nat.setGcd_dvd_of_mem (by
      show μ (k - 1 + 1) ≠ 0
      rwa [Nat.sub_add_cancel (by omega)])
    have h2 := Int.natCast_dvd_natCast.2 this
    have h3 : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by omega
    rwa [h3] at h2
  have hGpos : 1 ≤ G := (arithFactor_isGreatest_of_two_le ⟨k0, hk02, hk0⟩).1.1
  have hGd : G ∣ d := by
    have hL1 : 1 ≤ Nat.lcm d G := Nat.pos_of_ne_zero (Nat.lcm_ne_zero (by omega) (by omega))
    have hLadm : ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → ((Nat.lcm d G : ℕ) : ℤ) ∣ (k : ℤ) - k0 := by
      intro k hk hk0'
      rw [Int.natCast_dvd]
      apply Nat.lcm_dvd
      · rw [← Int.natCast_dvd]
        have := dvd_sub (hdv k hk hk0') (hdv k0 hk0 (by omega))
        have e : ((k : ℤ) - b) - ((k0 : ℤ) - b) = (k : ℤ) - k0 := by ring
        rwa [e] at this
      · rw [← Int.natCast_dvd]
        have := dvd_sub (hG1 k hk hk0') (hG1 k0 hk0 (by omega))
        have e : ((k : ℤ) - 1) - ((k0 : ℤ) - 1) = (k : ℤ) - k0 := by ring
        rwa [e] at this
    have hle := hdmax _ hL1 ⟨k0, hLadm⟩
    have hge : d ≤ Nat.lcm d G := Nat.le_of_dvd hL1 (Nat.dvd_lcm_left d G)
    have heq : Nat.lcm d G = d := le_antisymm hle hge
    rw [← heq]
    exact Nat.dvd_lcm_right d G
  have hGb : (G : ℤ) ∣ (b : ℤ) - 1 := by
    have h1 : (G : ℤ) ∣ (k0 : ℤ) - b :=
      (Int.natCast_dvd_natCast.2 hGd).trans (hdv k0 hk0 (by omega))
    have := dvd_sub (hG1 k0 hk0 (by omega)) h1
    have e : ((k0 : ℤ) - 1) - ((k0 : ℤ) - b) = (b : ℤ) - 1 := by ring
    rwa [e] at this
  apply Nat.dvd_antisymm
  · rw [Nat.dvd_setGcd_iff]
    intro i hi
    have hi' : μ (i + 1) ≠ 0 := hi
    have h1 := hdv (i + 1) hi' (by omega)
    have h2 : (Int.gcd ((b : ℤ) - 1) (d : ℤ) : ℤ) ∣ (i : ℤ) := by
      have := dvd_add (dvd_trans (Int.gcd_dvd_right (a := (b : ℤ) - 1) (b := (d : ℤ))) h1)
        (Int.gcd_dvd_left (a := (b : ℤ) - 1) (b := (d : ℤ)))
      have e : (((i + 1 : ℕ) : ℤ) - b) + ((b : ℤ) - 1) = (i : ℤ) := by push_cast; ring
      rwa [e] at this
    exact Int.natCast_dvd_natCast.1 h2
  · exact Int.dvd_gcd hGb (Int.natCast_dvd_natCast.2 hGd)

theorem exists_isSuppSpan {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ) :
    ∃ d b : ℕ, IsSuppSpan μ d b := by
  classical
  obtain ⟨k2, hk22, hk2⟩ := exists_two_le hc hne
  have hk1 : ∃ k1 : ℕ, μ k1 ≠ 0 ∧ k1 ≠ 0 ∧ k1 ≠ k2 := by
    by_contra hcon
    push Not at hcon
    have hle : AddSubgroup.closure (((↑) : ℕ → ℤ) '' {j : ℕ | μ j ≠ 0}) ≤
        AddSubgroup.zmultiples (k2 : ℤ) := by
      rw [AddSubgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      by_cases hj0 : j = 0
      · simp [hj0]
      · rw [hcon j hj hj0]; exact AddSubgroup.mem_zmultiples _
    rw [hap] at hle
    have h1 : (1 : ℤ) ∈ AddSubgroup.zmultiples (k2 : ℤ) := hle trivial
    obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 h1
    have : (k2 : ℤ) ∣ 1 := ⟨n, by rw [← hn]; simp [mul_comm]⟩
    have := Int.eq_one_of_dvd_one (by positivity) this
    omega
  obtain ⟨k1, hk1μ, hk10, hk12⟩ := hk1
  let D : Set ℕ := {d | 1 ≤ d ∧ ∃ b' : ℕ, ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → (d : ℤ) ∣ (k : ℤ) - b'}
  have hD1 : 1 ∈ D := ⟨le_rfl, 0, fun k _ _ => by simp⟩
  have hbdd : BddAbove D := by
    refine ⟨((k1 : ℤ) - k2).natAbs, ?_⟩
    rintro d ⟨hd1, b', hb'⟩
    have h := dvd_sub (hb' k1 hk1μ hk10) (hb' k2 hk2 (by omega))
    have e : ((k1 : ℤ) - b') - ((k2 : ℤ) - b') = (k1 : ℤ) - k2 := by ring
    rw [e, Int.natCast_dvd] at h
    exact Nat.le_of_dvd (by
      rw [Int.natAbs_pos]; omega) h
  obtain ⟨hd1, b', hb'⟩ := Nat.sSup_mem ⟨1, hD1⟩ hbdd
  have hex : ∃ b'' : ℕ, ∀ k : ℕ, μ k ≠ 0 → k ≠ 0 → ((sSup D : ℕ) : ℤ) ∣ (k : ℤ) - b'' := ⟨b', hb'⟩
  refine ⟨sSup D, Nat.find hex, hd1, Nat.find_spec hex, ?_, ?_⟩
  · intro d' hd' hd'ex
    exact le_csSup hbdd ⟨hd', hd'ex⟩
  · intro b'' hb''
    exact Nat.find_min' hex hb''


/-! ## The support of the number of leaves -/

theorem mu_zero_ne_one {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) : μ 0 ≠ 1 := by
  intro h0
  obtain ⟨k, hk2, hk⟩ := exists_two_le hc hne
  have hle : ∑ i ∈ ({0, k} : Finset ℕ), μ i ≤ ∑' i, μ i := ENNReal.sum_le_tsum _
  rw [PMF.tsum_coe, Finset.sum_pair (by omega), h0] at hle
  apply hk
  have : (1 : ℝ≥0∞) + μ k ≤ 1 + 0 := by simpa using hle
  exact (ENNReal.add_le_add_iff_left ENNReal.one_ne_top |>.1 this) |> le_zero_iff.1

theorem mem_closure_iff_exists_fin {S : Set ℕ} {n : ℕ} :
    n ∈ AddSubmonoid.closure S ↔
      ∃ q : ℕ, ∃ ω : Fin q → ℕ, (∀ i, ω i ∈ S) ∧ ∑ i, ω i = n := by
  constructor
  · intro h
    obtain ⟨l, hl, rfl⟩ := AddSubmonoid.exists_list_of_mem_closure h
    refine ⟨l.length, fun i => l.get i, fun i => hl _ (List.get_mem _ _), ?_⟩
    rw [← List.sum_ofFn, List.ofFn_get]
  · rintro ⟨q, ω, hω, rfl⟩
    exact AddSubmonoid.sum_mem _ fun i _ => AddSubmonoid.subset_closure (hω i)

theorem pi_ne_zero_iff (ν : Measure ℕ) [IsProbabilityMeasure ν] (k n : ℕ) :
    Measure.pi (fun _ : Fin k => ν) {ω | ∑ i, ω i + 1 = n + 1} ≠ 0 ↔
      ∃ ω : Fin k → ℕ, ∑ i, ω i = n ∧ ∀ i, ν {ω i} ≠ 0 := by
  rw [BGW.pi_eq_tsum_indicator, Ne, ENNReal.tsum_eq_zero]
  push Not
  simp only [Set.indicator_apply_ne_zero, Set.mem_inter_iff, Function.mem_support,
    Set.mem_ofPred_eq, Nat.add_right_cancel_iff]
  refine exists_congr fun ω => and_congr Iff.rfl ?_
  rw [Finset.prod_ne_zero_iff]
  simp

theorem eta_singleton_ne_zero_iff (μ : PMF ℕ) (r : ℕ) :
    eta μ.toMeasure {r} ≠ 0 ↔ μ (r + 1) ≠ 0 := by
  have hpre : Set.Ici 1 ∩ (fun k : ℕ => id k - 1) ⁻¹' ({r} : Set ℕ) = {r + 1} := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hk, hr⟩
      change k - 1 = r at hr
      omega
    · intro h
      constructor
      · omega
      · change k - 1 = r
        simp [h]
  have : eta μ.toMeasure {r} = (μ.toMeasure (Set.Ici 1))⁻¹ * μ (r + 1) := by
    change (Measure.map (fun k : ℕ => id k - 1) (μ.toMeasure[|Set.Ici 1])) {r} = _
    rw [Measure.map_apply (by fun_prop : Measurable (fun k : ℕ => id k - 1))
      (measurableSet_singleton r), ProbabilityTheory.cond_apply measurableSet_Ici, hpre,
      PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [this]
  simp [ENNReal.inv_eq_zero, measure_ne_top]


theorem eta_isProbabilityMeasure {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    IsProbabilityMeasure (eta μ.toMeasure) := by
  obtain ⟨k, hk2, hk⟩ := exists_two_le hc hne
  have hcond : μ.toMeasure (Set.Ici 1) ≠ 0 := by
    intro hz
    have : μ.toMeasure {k} ≤ μ.toMeasure (Set.Ici 1) :=
      measure_mono (by simpa using (by omega : 1 ≤ k))
    rw [hz, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] at this
    exact hk (le_zero_iff.1 this)
  have : IsProbabilityMeasure (μ.toMeasure[|Set.Ici 1]) := cond_isProbabilityMeasure hcond
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_id.sub_const 1).aemeasurable).2 inferInstance

theorem treeSizeLeaves_ne_zero_iff {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n p : ℕ}
    (hp : n + 1 ≤ p) :
    bienaymeLaw μ.toMeasure (treeSizeLeavesEvent p (n + 1)) ≠ 0 ↔
      ∃ ω : Fin (p - (n + 1)) → ℕ, ∑ i, ω i = n ∧ ∀ i, μ (ω i + 1) ≠ 0 := by
  have := eta_isProbabilityMeasure hc hne
  have hμ0 := mu_zero_ne_zero hc hne
  have hμ01 := mu_zero_ne_one hc hne
  have h0 : μ.toMeasure {0} ≠ 1 := by
    rwa [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  rw [eq_f μ.toMeasure h0 (by omega) hp]
  have hμ0' : μ.toMeasure {0} ≠ 0 := by
    rwa [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  have hf1 : (1 : ℝ≥0∞) / (p : ℝ≥0∞) ≠ 0 := by simp
  have hf2 : ((p.choose (n + 1) : ℕ) : ℝ≥0∞) ≠ 0 := by
    simpa using (Nat.choose_pos hp).ne'
  have hf3 : μ.toMeasure {0} ^ (n + 1) ≠ 0 := pow_ne_zero _ hμ0'
  have hf4 : (1 - μ.toMeasure {0}) ^ (p - (n + 1)) ≠ 0 := by
    refine pow_ne_zero _ ?_
    exact (tsub_pos_iff_lt.2 (lt_of_le_of_ne prob_le_one h0)).ne'
  have hpre := pi_ne_zero_iff (eta μ.toMeasure) (p - (n + 1)) n
  constructor
  · intro h
    obtain ⟨ω, h1, h2⟩ := hpre.1 (right_ne_zero_of_mul h)
    exact ⟨ω, h1, fun i => (eta_singleton_ne_zero_iff μ (ω i)).1 (h2 i)⟩
  · rintro ⟨ω, h1, h2⟩
    exact mul_ne_zero (mul_ne_zero hf1 (mul_ne_zero (mul_ne_zero hf2 hf3) hf4))
      (hpre.2 ⟨ω, h1, fun i => (eta_singleton_ne_zero_iff μ (ω i)).2 (h2 i)⟩)

theorem leafProb_pos_iff_ne_zero (μ : PMF ℕ) (m : ℕ) :
    0 < leafProb μ m ↔ bienaymeLaw μ.toMeasure (leafCountEvent m) ≠ 0 := by
  unfold leafProb
  rw [Measure.real, ENNReal.toReal_pos_iff]
  simp [pos_iff_ne_zero, measure_lt_top]

theorem leafCountEvent_eq_iUnion (m : ℕ) :
    leafCountEvent m = ⋃ p : ℕ, treeSizeLeavesEvent p m := by
  ext T
  simp only [leafCountEvent, finiteTreeEvent, treeSizeLeavesEvent, Set.mem_iUnion,
    Set.mem_ofPred_eq]
  constructor
  · rintro ⟨t, rfl, ht⟩
    exact ⟨t.size, t, rfl, ht, rfl⟩
  · rintro ⟨p, t, _, ht, rfl⟩
    exact ⟨t, rfl, ht⟩

theorem leafCount_ne_zero_iff (μ : PMF ℕ) (m : ℕ) :
    bienaymeLaw μ.toMeasure (leafCountEvent m) ≠ 0 ↔
      ∃ p, bienaymeLaw μ.toMeasure (treeSizeLeavesEvent p m) ≠ 0 := by
  rw [leafCountEvent_eq_iUnion]
  constructor
  · intro h
    by_contra hcon
    push Not at hcon
    exact h (measure_iUnion_null hcon)
  · rintro ⟨p, hp⟩ h
    exact hp (measure_mono_null (Set.subset_iUnion (fun p => treeSizeLeavesEvent p m) p) h)

theorem leafProb_pos_iff_mem_leafMonoid {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (n : ℕ) :
    0 < leafProb μ (n + 1) ↔ n ∈ leafMonoid μ := by
  rw [leafProb_pos_iff_ne_zero, leafCount_ne_zero_iff, leafMonoid, mem_closure_iff_exists_fin]
  constructor
  · rintro ⟨p, hp⟩
    have hne' : (treeSizeLeavesEvent p (n + 1)).Nonempty := by
      by_contra hemp
      rw [Set.not_nonempty_iff_eq_empty] at hemp
      exact hp (by rw [hemp]; simp)
    obtain ⟨T, t, hts, hdeg, -⟩ := hne'
    have hle : n + 1 ≤ p := by
      rw [← hts, ← hdeg]; exact t.degreeCount_le_size 0
    obtain ⟨ω, h1, h2⟩ := (treeSizeLeaves_ne_zero_iff hc hne hle).1 hp
    exact ⟨_, ω, h2, h1⟩
  · rintro ⟨q, ω, hω, hsum⟩
    obtain ⟨p, hpq, hnp⟩ : ∃ p, p - (n + 1) = q ∧ n + 1 ≤ p :=
      ⟨q + (n + 1), by omega, by omega⟩
    subst hpq
    exact ⟨p, (treeSizeLeaves_ne_zero_iff hc hne hnp).2 ⟨ω, hsum, hω⟩⟩

theorem leafMonoid_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n : ℕ}
    (hn : n ∈ leafMonoid μ) : arithFactor μ {0} ∣ n := by
  rw [arithFactor_zero_eq_setGcd hc hne]
  exact Nat.setGcd_dvd_of_mem_closure hn

theorem leafMonoid_eventually {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → arithFactor μ {0} ∣ n → n ∈ leafMonoid μ := by
  rw [arithFactor_zero_eq_setGcd hc hne]
  exact Nat.exists_mem_closure_of_ge _

theorem leafProb_eq_zero_of_not_dvd {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {n : ℕ}
    (hn : ¬ arithFactor μ {0} ∣ n) : leafProb μ (n + 1) = 0 := by
  refine le_antisymm (not_lt.1 fun h => hn ?_) measureReal_nonneg
  exact leafMonoid_dvd hc hne ((leafProb_pos_iff_mem_leafMonoid hc hne n).1 h)

theorem ltn_i_arith {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → (0 < leafProb μ (n + 1) ↔ arithFactor μ {0} ∣ n) := by
  obtain ⟨N, hN⟩ := leafMonoid_eventually hc hne
  exact ⟨N, fun n hn => by
    rw [leafProb_pos_iff_mem_leafMonoid hc hne]
    exact ⟨leafMonoid_dvd hc hne, hN n hn⟩⟩


/-! ## The series for `P[λ = m]` (Proposition 1.6 with `j = 1`, summed over the sizes) -/

theorem intWalk_eq_map_sum (ν : Measure ℤ) [IsProbabilityMeasure ν] (m : ℕ) :
    intWalk ν m = (Measure.pi (fun _ : Fin m => ν)).map (fun ω => ∑ i, ω i) := by
  induction m with
  | zero =>
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rw [Measure.map_const, measure_univ, one_smul]
    rfl
  | succ m ih =>
    rw [intWalk, Measure.conv, ih]
    have hpres := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => ν) 0
    have hW : Measure.pi (fun _ : Fin (m + 1) => ν) =
        (ν.prod (Measure.pi (fun _ : Fin m => ν))).map
          (MeasurableEquiv.piFinSuccAbove (fun _ => ℤ) 0).symm := by
      rw [← hpres.symm.map_eq]
    have hprod : ((Measure.pi (fun _ : Fin m => ν)).map (fun ω => ∑ i, ω i)).prod ν =
        ((Measure.pi (fun _ : Fin m => ν)).prod ν).map (Prod.map (fun ω => ∑ i, ω i) id) := by
      rw [← Measure.map_prod_map _ _ (measurable_of_countable _) measurable_id, Measure.map_id]
    rw [hW, Measure.map_map (measurable_of_countable _) (measurable_of_countable _), hprod,
      Measure.map_map (measurable_of_countable _) (measurable_of_countable _),
      ← Measure.prod_swap, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
    congr 1
    funext p
    simp only [Function.comp_apply, MeasurableEquiv.piFinSuccAbove_symm_apply, Prod.map,
      Prod.fst_swap, Prod.snd_swap, id]
    rw [Fin.sum_univ_succAbove _ 0]
    simp [Fin.insertNthEquiv, add_comm]


theorem eta_map_cast_eq_etaLaw (μ : PMF ℕ) :
    (eta μ.toMeasure).map (fun k : ℕ => (k : ℤ)) = etaLaw μ := by
  rw [eta, etaLaw, Measure.map_map (measurable_of_countable _) (measurable_of_countable _)]
  refine Measure.map_congr ?_
  have hae : ∀ᵐ k ∂(μ.toMeasure[|Set.Ici 1]), k ∈ Set.Ici 1 := ProbabilityTheory.ae_cond_mem measurableSet_Ici
  filter_upwards [hae] with k hk
  simp only [Set.mem_Ici] at hk
  simp only [Function.comp_apply]
  omega

theorem pi_eta_real_eq_intWalkProb {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (k n : ℕ) :
    (Measure.pi (fun _ : Fin k => eta μ.toMeasure)).real {ω | ∑ i, ω i + 1 = n + 1} =
      intWalkProb (etaLaw μ) k (n : ℤ) := by
  have := eta_isProbabilityMeasure hc hne
  have hY : IsProbabilityMeasure (etaLaw μ) := by
    rw [← eta_map_cast_eq_etaLaw]
    exact (Measure.isProbabilityMeasure_map_iff (measurable_of_countable _).aemeasurable).2 this
  rw [intWalkProb, intWalk_eq_map_sum, ← eta_map_cast_eq_etaLaw, measureReal_def, measureReal_def,
    ← Measure.pi_map_pi (μ := fun _ : Fin k => eta μ.toMeasure)
      (f := fun _ : Fin k => fun k : ℕ => (k : ℤ))
      (fun _ => (measurable_of_countable _).aemeasurable),
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff]
  constructor
  · intro h; exact_mod_cast (by omega : ∑ i, ω i = n)
  · intro h; have : ∑ i, ω i = n := by exact_mod_cast h
    omega


theorem treeSizeLeavesEvent_measurableSet (p n : ℕ) : MeasurableSet (treeSizeLeavesEvent p n) := by
  have : treeSizeLeavesEvent p n =
      (fun t : BGW.PlaneTree => t.toLocallyFinite) '' {t | t.size = p ∧ t.degreeCount 0 = n} := by
    ext T
    simp only [treeSizeLeavesEvent, Set.mem_image, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨t, h1, h2, rfl⟩
      exact ⟨t, ⟨h1, h2⟩, rfl⟩
    · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
      exact ⟨t, h1, h2, rfl⟩
  rw [this]
  exact (Set.to_countable _).image _ |>.measurableSet

theorem bienaymeLaw_leafCountEvent_eq_tsum (μ : PMF ℕ) (m : ℕ) :
    bienaymeLaw μ.toMeasure (leafCountEvent m) =
      ∑' p : ℕ, bienaymeLaw μ.toMeasure (treeSizeLeavesEvent p m) := by
  rw [leafCountEvent_eq_iUnion, measure_iUnion _ (fun p => treeSizeLeavesEvent_measurableSet p m)]
  intro p q hpq
  rw [Function.onFun, Set.disjoint_left]
  rintro T ⟨t, hp, -, rfl⟩ ⟨t', hq, -, h⟩
  have := BGW.PlaneTree.toLocallyFinite_injective h
  subst this
  exact hpq (hp.symm.trans hq)

theorem leafProb_series {μ : PMF ℕ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) {m : ℕ} (hm : 1 ≤ m) :
    leafProb μ m =
      ∑' p : ℕ, (1 / (p : ℝ)) *
        ((p.choose m : ℝ) * (μ 0).toReal ^ m * (1 - (μ 0).toReal) ^ (p - m)) *
          intWalkProb (etaLaw μ) (p - m) ((m : ℤ) - 1) := by
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have := eta_isProbabilityMeasure hc hne
  have h0 : μ.toMeasure {0} ≠ 1 := by
    rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
    exact mu_zero_ne_one hc hne
  unfold leafProb
  rw [Measure.real, bienaymeLaw_leafCountEvent_eq_tsum,
    ENNReal.tsum_toReal_eq (fun p => measure_ne_top _ _)]
  refine tsum_congr fun p => ?_
  by_cases hp : n + 1 ≤ p
  · rw [eq_f μ.toMeasure h0 (by omega) hp]
    have h1 := pi_eta_real_eq_intWalkProb hc hne (p - (n + 1)) n
    have h2 : (((n + 1 : ℕ) : ℤ) - 1) = (n : ℤ) := by push_cast; ring
    rw [h2, ← h1, Measure.real]
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top, ENNReal.toReal_div]
    simp [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)]
  · have hemp : treeSizeLeavesEvent p (n + 1) = ∅ := by
      ext T
      simp only [treeSizeLeavesEvent, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨t, h1, h2, -⟩
      exact hp (by rw [← h1, ← h2]; exact t.degreeCount_le_size 0)
    rw [hemp, Nat.choose_eq_zero_of_lt (by omega)]
    simp

end BGWLeaves.LeafMass.Arithmetic
