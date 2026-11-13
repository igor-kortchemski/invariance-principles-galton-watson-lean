module

public import BGWLeaves.ForestLaw.Defs

/-!
# Binomial and jump-law factorization

Source: arXiv:1110.2163v4, Section 1.3, equation `eq:LambdaUtile`.
-/

@[expose] public section

namespace BGWLeaves.ForestLaw.Factorization

open MeasureTheory ProbabilityTheory BGW
open scoped ENNReal

private theorem mu_zero_add_mu_Ici_one (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    μ {0} + μ (Set.Ici 1) = 1 := by
  have hd : Disjoint ({0} : Set ℕ) (Set.Ici 1) := by
    rw [Set.disjoint_left]
    intro k hk hle
    simp only [Set.mem_singleton_iff] at hk
    simp only [Set.mem_Ici] at hle
    subst k
    omega
  have hu : ({0} : Set ℕ) ∪ Set.Ici 1 = Set.univ := by
    ext k
    by_cases hk : k = 0
    · simp [hk]
    · simp [Nat.one_le_iff_ne_zero, hk]
  calc
    μ {0} + μ (Set.Ici 1) = μ ({0} ∪ Set.Ici 1) :=
      (measure_union hd measurableSet_Ici).symm
    _ = 1 := by rw [hu, measure_univ]

private theorem mu_Ici_one (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    μ (Set.Ici 1) = 1 - μ {0} := by
  have hsum := mu_zero_add_mu_Ici_one μ
  exact ENNReal.eq_sub_of_add_eq (by simp) (by simpa [add_comm] using hsum)

private theorem eta_isProbabilityMeasure (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h0 : μ {0} ≠ 1) : IsProbabilityMeasure (eta μ) := by
  have hcond : μ (Set.Ici 1) ≠ 0 := by
    intro hzero
    apply h0
    have hsum := mu_zero_add_mu_Ici_one μ
    simpa [hzero] using hsum
  have : IsProbabilityMeasure (μ[|Set.Ici 1]) := cond_isProbabilityMeasure hcond
  exact (Measure.isProbabilityMeasure_map_iff
    (measurable_id.sub_const 1).aemeasurable).2 inferInstance

private theorem eta_singleton (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (_h0 : μ {0} ≠ 1) (r : ℕ) :
    eta μ {r} = μ {r + 1} / (1 - μ {0}) := by
  have hpre : Set.Ici 1 ∩ (fun k : ℕ => id k - 1) ⁻¹' ({r} : Set ℕ) = {r + 1} := by
    ext k
    simp only [Set.mem_inter_iff, Set.mem_Ici, Set.mem_preimage,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hk, hr⟩
      change k - 1 = r at hr
      omega
    · intro h
      constructor
      · omega
      · change k - 1 = r
        simp [h]
  change (Measure.map (fun k : ℕ => id k - 1) (μ[|Set.Ici 1])) {r} = _
  rw [Measure.map_apply (by fun_prop : Measurable (fun k : ℕ => id k - 1))
      (measurableSet_singleton r),
    ProbabilityTheory.cond_apply measurableSet_Ici, hpre, mu_Ici_one μ,
    ENNReal.div_eq_inv_mul]

private def bridgeSum {p : ℕ} (ω : Fin p → ℕ) : ℤ := ∑ i, (ω i : ℤ)

private def zeroCount {p : ℕ} (ω : Fin p → ℕ) : ℕ :=
  (Finset.univ.filter fun i => ω i = 0).card

private def bridgePredicate (p n : ℕ) (j : ℤ) (ω : Fin p → ℕ) : Prop :=
  bridgeSum ω + j = p ∧ zeroCount ω = n

private noncomputable def bridgeMass (μ : Measure ℕ) (p n : ℕ) (j : ℤ) : ℝ≥0∞ :=
  ∑' ω : Fin p → ℕ,
    Set.indicator {ω | bridgePredicate p n j ω} (fun ω => ∏ i, μ {ω i}) ω

private noncomputable def etaBridgeMass (ν : Measure ℕ) (p n : ℕ) (j : ℤ) : ℝ≥0∞ :=
  ∑' ω : Fin p → ℕ,
    Set.indicator {ω | bridgeSum ω + j = n} (fun ω => ∏ i, ν {ω i}) ω

private def finConsEquiv (m : ℕ) : (ℕ × (Fin m → ℕ)) ≃ (Fin (m + 1) → ℕ) where
  toFun x := Fin.cons x.1 x.2
  invFun ω := (ω 0, fun i => ω i.succ)
  left_inv x := by
    rcases x with ⟨a, ω⟩
    rfl
  right_inv ω := by
    apply funext
    intro i
    refine Fin.cases ?_ ?_ i
    · simp
    · intro i
      simp

private theorem bridgeSum_cons {m : ℕ} (a : ℕ) (ω : Fin m → ℕ) :
    bridgeSum (Fin.cons a ω) = (a : ℤ) + bridgeSum ω := by
  simp [bridgeSum, Fin.sum_univ_succ]

private theorem zeroCount_cons {m : ℕ} (a : ℕ) (ω : Fin m → ℕ) :
    zeroCount (Fin.cons a ω) = (if a = 0 then 1 else 0) + zeroCount ω := by
  classical
  unfold zeroCount
  rw [Finset.card_filter]
  change (∑ i : Fin (m + 1), if (@Fin.cons m (fun _ => ℕ) a ω) i = 0 then 1 else 0) = _
  rw [Fin.sum_univ_succ]
  simp [Fin.cons_zero, Fin.cons_succ]

private theorem etaBridgeMass_succ (ν : Measure ℕ) (q n : ℕ) (j : ℤ) :
    etaBridgeMass ν (q + 1) n j =
      ∑' k : ℕ, ν {k} * etaBridgeMass ν q n (j + k) := by
  classical
  unfold etaBridgeMass
  rw [← (finConsEquiv q).tsum_eq, ENNReal.tsum_prod']
  change (∑' k : ℕ, ∑' ω : Fin q → ℕ,
      Set.indicator {x | bridgeSum (Fin.cons k ω) + j = n}
        (fun x => ∏ i, ν {x i}) (Fin.cons k ω)) = _
  congr 1
  funext k
  rw [← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro ω
  have hsum : bridgeSum ω + (j + (k : ℤ)) = n ↔
      bridgeSum (Fin.cons k ω) + j = n := by
    rw [bridgeSum_cons]
    omega
  simp [Set.indicator, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
    hsum, mul_comm]

private theorem bridgePredicate_cons_zero (m n : ℕ) (j : ℤ)
    (hn : 1 ≤ n) (ω : Fin m → ℕ) :
    bridgePredicate (m + 1) n j (Fin.cons 0 ω) ↔
      bridgePredicate m (n - 1) (j - 1) ω := by
  have hz : zeroCount (Fin.cons 0 ω) = 1 + zeroCount ω := by
    simpa using zeroCount_cons 0 ω
  unfold bridgePredicate
  rw [bridgeSum_cons, hz]
  constructor <;> rintro ⟨hs, hc⟩ <;> constructor <;> omega

private theorem bridgePredicate_cons_succ (m n k : ℕ) (j : ℤ)
    (ω : Fin m → ℕ) :
    bridgePredicate (m + 1) n j (Fin.cons (k + 1) ω) ↔
      bridgePredicate m n (j + (k : ℕ)) ω := by
  have hz : zeroCount (Fin.cons (k + 1) ω) = zeroCount ω := by
    simpa using zeroCount_cons (k + 1) ω
  unfold bridgePredicate
  rw [bridgeSum_cons, hz]
  constructor <;> rintro ⟨hs, hc⟩ <;> constructor <;> omega

private theorem bridgeMass_succ (μ : Measure ℕ) (m n : ℕ) (hn : n ≤ m)
    (j : ℤ) :
    bridgeMass μ (m + 1) n j =
      (if n = 0 then 0 else μ {0} * bridgeMass μ m (n - 1) (j - 1)) +
        ∑' k : ℕ, μ {k + 1} * bridgeMass μ m n (j + (k : ℕ)) := by
  classical
  unfold bridgeMass
  rw [← (finConsEquiv m).tsum_eq, ENNReal.tsum_prod']
  change (∑' a : ℕ, ∑' ω : Fin m → ℕ,
      Set.indicator {x | bridgePredicate (m + 1) n j x}
        (fun x => ∏ i, μ {x i}) (Fin.cons a ω)) = _
  rw [tsum_eq_zero_add' ENNReal.summable]
  have hzero :
      (∑' ω : Fin m → ℕ,
        Set.indicator {x | bridgePredicate (m + 1) n j x}
          (fun x => ∏ i, μ {x i}) (Fin.cons 0 ω)) =
        if n = 0 then 0 else μ {0} * bridgeMass μ m (n - 1) (j - 1) := by
    by_cases hn0 : n = 0
    · subst n
      have hnot (ω : Fin m → ℕ) :
          ¬ (Fin.cons 0 ω ∈ {x | bridgePredicate (m + 1) 0 j x}) := by
        intro h
        have hc : zeroCount (Fin.cons 0 ω) = 0 := h.2
        have hc' : 1 + zeroCount ω = 0 := by
          simp [zeroCount_cons] at hc
        omega
      apply ENNReal.tsum_eq_zero.mpr
      intro ω
      exact Set.indicator_of_notMem (hnot ω) _
    · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
      rw [ite_eq_right hn0]
      unfold bridgeMass
      rw [← ENNReal.tsum_mul_left]
      apply tsum_congr
      intro ω
      simp [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
        bridgePredicate_cons_zero m n j hnpos ω, Set.indicator,
        mul_comm]
  have hsucc (k : ℕ) :
      (∑' ω : Fin m → ℕ,
        Set.indicator {x | bridgePredicate (m + 1) n j x}
          (fun x => ∏ i, μ {x i}) (Fin.cons (k + 1) ω)) =
        μ {k + 1} * bridgeMass μ m n (j + (k : ℕ)) := by
    unfold bridgeMass
    rw [← ENNReal.tsum_mul_left]
    apply tsum_congr
    intro ω
    simp [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,
      bridgePredicate_cons_succ m n k j ω, Set.indicator,
      mul_comm]
  rw [hzero]
  congr 1
  apply tsum_congr
  intro k
  exact hsucc k

private theorem etaBridgeMass_shift (ν : Measure ℕ) (q n : ℕ) (j : ℤ)
    (hn : 1 ≤ n) :
    etaBridgeMass ν q (n - 1) (j - 1) = etaBridgeMass ν q n j := by
  unfold etaBridgeMass
  apply tsum_congr
  intro ω
  have hcast : ((n - 1 : ℕ) : ℤ) = (n : ℤ) - 1 := by omega
  have heq : bridgeSum ω + (j - 1) = ((n - 1 : ℕ) : ℤ) ↔
      bridgeSum ω + j = n := by
    rw [hcast]
    omega
  simp only [Set.indicator, Set.mem_ofPred_eq]
  exact if_congr heq rfl rfl

private theorem mu_succ_eq_d_mul_eta (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h0 : μ {0} ≠ 1) (k : ℕ) :
    μ {k + 1} = (1 - μ {0}) * eta μ {k} := by
  have hcond : μ (Set.Ici 1) ≠ 0 := by
    intro hz
    apply h0
    have hsum := mu_zero_add_mu_Ici_one μ
    simpa [hz] using hsum
  have hd0 : (1 - μ {0}) ≠ 0 := by
    rw [← mu_Ici_one μ]
    exact hcond
  have hdt : (1 - μ {0}) ≠ ∞ := by
    rw [← mu_Ici_one μ]
    exact measure_ne_top μ (Set.Ici 1)
  have hmul := (ENNReal.eq_div_iff hd0 hdt).mp (eta_singleton μ h0 k)
  exact hmul.symm

private theorem eq_zero_of_zeroCount_eq_card {p : ℕ} (ω : Fin p → ℕ)
    (h : zeroCount ω = p) : ω = 0 := by
  have hc : (Finset.univ.filter fun i : Fin p => ω i = 0).card =
      (Finset.univ : Finset (Fin p)).card := by
    simpa [zeroCount] using h
  have hall := (Finset.card_filter_eq_iff.mp hc)
  funext i
  exact hall i (Finset.mem_univ i)

private theorem bridgeMass_factorization (μ : Measure ℕ) [IsProbabilityMeasure μ]
    (h0 : μ {0} ≠ 1) {p n : ℕ} (hn : n ≤ p) (j : ℤ) :
    bridgeMass μ p n j =
      (p.choose n : ℝ≥0∞) * μ {0} ^ n * (1 - μ {0}) ^ (p - n) *
        etaBridgeMass (eta μ) (p - n) n j := by
  induction p generalizing n j with
  | zero =>
      have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
      subst n
      simp [bridgeMass, etaBridgeMass, bridgePredicate, bridgeSum, zeroCount]
  | succ p ih =>
      by_cases hnp : n = p + 1
      · subst n
        have hleft : bridgeMass μ (p + 1) (p + 1) j =
            (if j = (p + 1 : ℕ) then μ {0} ^ (p + 1) else 0) := by
          unfold bridgeMass
          rw [tsum_eq_single (0 : Fin (p + 1) → ℕ)]
          · have hsum0 : bridgeSum (0 : Fin (p + 1) → ℕ) = 0 := by
              simp [bridgeSum]
            have hcount0 : zeroCount (0 : Fin (p + 1) → ℕ) = p + 1 := by
              simp [zeroCount]
            simp [Set.indicator, bridgePredicate, hsum0, hcount0]
          · intro ω hω
            by_cases hp : bridgePredicate (p + 1) (p + 1) j ω
            · have hw : ω = 0 := eq_zero_of_zeroCount_eq_card ω hp.2
              exact (hω hw).elim
            · have hnot : ω ∉ {x | bridgePredicate (p + 1) (p + 1) j x} := hp
              exact Set.indicator_of_notMem hnot _
        have hright :
            ((p + 1).choose (p + 1) : ℝ≥0∞) * μ {0} ^ (p + 1) *
                (1 - μ {0}) ^ ((p + 1) - (p + 1)) *
                etaBridgeMass (eta μ) ((p + 1) - (p + 1)) (p + 1) j =
              if j = (p + 1 : ℕ) then μ {0} ^ (p + 1) else 0 := by
          have hdim : (p + 1) - (p + 1) = 0 := Nat.sub_self _
          simp_rw [hdim]
          unfold etaBridgeMass
          by_cases hj : j = (p + 1 : ℤ)
          · simp [hj, bridgeSum]
          · simp [hj, bridgeSum]
        exact hleft.trans hright.symm
      · have hnm : n ≤ p := by omega
        by_cases hn0 : n = 0
        · subst n
          rw [bridgeMass_succ μ p 0 (by omega) j]
          simp
          have hrec := etaBridgeMass_succ (eta μ) p 0 j
          rw [hrec]
          have hpos (k : ℕ) := ih (n := 0) (by omega) (j + (k : ℕ))
          simp_rw [hpos, mu_succ_eq_d_mul_eta μ h0]
          have hsum :
              (∑' k : ℕ, etaBridgeMass (eta μ) p 0 (j + (k : ℕ)) *
                ((eta μ) {k} * ((1 - μ {0}) * (1 - μ {0}) ^ p))) =
              (1 - μ {0}) * ((1 - μ {0}) ^ p *
                ∑' k : ℕ, etaBridgeMass (eta μ) p 0 (j + (k : ℕ)) * (eta μ) {k}) := by
            calc
              _ = ∑' k : ℕ, (etaBridgeMass (eta μ) p 0 (j + (k : ℕ)) *
                  (eta μ) {k}) * ((1 - μ {0}) * (1 - μ {0}) ^ p) := by
                apply tsum_congr
                intro k
                ac_rfl
              _ = _ := by rw [ENNReal.tsum_mul_right]; ac_rfl
          have hcomm :
              (∑' k : ℕ, etaBridgeMass (eta μ) p 0 (j + (k : ℕ)) * (eta μ) {k}) =
                ∑' k : ℕ, (eta μ) {k} * etaBridgeMass (eta μ) p 0 (j + (k : ℕ)) := by
            apply tsum_congr
            intro k
            ac_rfl
          simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, Nat.sub_zero, one_mul]
          calc
            _ = ∑' k : ℕ, etaBridgeMass (eta μ) p 0 (j + (k : ℕ)) *
                ((eta μ) {k} * ((1 - μ {0}) * (1 - μ {0}) ^ p)) := by
              apply tsum_congr
              intro k
              ac_rfl
            _ = (1 - μ {0}) * ((1 - μ {0}) ^ p *
                ∑' k : ℕ, etaBridgeMass (eta μ) p 0 (j + (k : ℕ)) * (eta μ) {k}) := hsum
            _ = (1 - μ {0}) ^ (p + 1) *
                ∑' k : ℕ, (eta μ) {k} * etaBridgeMass (eta μ) p 0 (j + (k : ℕ)) := by
              rw [hcomm, pow_succ]
              ac_rfl
        · have hnpos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn0
          rw [bridgeMass_succ μ p n hnm j]
          simp only [ite_eq_right hn0]
          have hzero := ih (n := n - 1) (by omega) (j - 1)
          have hpos (k : ℕ) := ih (n := n) hnm (j + (k : ℕ))
          have hq : p - (n - 1) = p + 1 - n := by omega
          rw [hq] at hzero
          simp_rw [hzero, hpos, mu_succ_eq_d_mul_eta μ h0]
          have hq' : p + 1 - n = (p - n) + 1 := by omega
          rw [hq']
          have hrec := etaBridgeMass_succ (eta μ) (p - n) n j
          rw [hrec]
          have hshift := etaBridgeMass_shift (eta μ) ((p - n) + 1) n j hnpos
          -- The zero branch has the same jump-law event after shifting both parameters.
          rw [hshift]
          have hrec' : etaBridgeMass (eta μ) ((p - n) + 1) n j =
              ∑' k : ℕ, etaBridgeMass (eta μ) (p - n) n (j + (k : ℕ)) * (eta μ) {k} := by
            rw [hrec]
            apply tsum_congr
            intro k
            ac_rfl
          rw [hrec']
          have hchoose : (p + 1).choose n = p.choose (n - 1) + p.choose n := by
            obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn0
            simpa using Nat.choose_succ_succ p r
          rw [hchoose]
          have hsumPos :
              (∑' k : ℕ, etaBridgeMass (eta μ) (p - n) n (j + (k : ℕ)) *
                ((eta μ) {k} * (μ {0} ^ n * ((1 - μ {0}) * (1 - μ {0}) ^ (p - n))))) =
                (μ {0} ^ n * ((1 - μ {0}) * (1 - μ {0}) ^ (p - n))) *
                  ∑' k : ℕ, etaBridgeMass (eta μ) (p - n) n (j + (k : ℕ)) * (eta μ) {k} := by
            calc
              _ = ∑' k : ℕ, (etaBridgeMass (eta μ) (p - n) n (j + (k : ℕ)) *
                  (eta μ) {k}) * (μ {0} ^ n * ((1 - μ {0}) * (1 - μ {0}) ^ (p - n))) := by
                apply tsum_congr
                intro k
                ac_rfl
              _ = _ := by rw [ENNReal.tsum_mul_right]; ac_rfl
          have haPow : μ {0} * μ {0} ^ (n - 1) = μ {0} ^ n := by
            calc
              _ = μ {0} ^ ((n - 1) + 1) := by rw [pow_succ]; ac_rfl
              _ = _ := by rw [Nat.sub_add_cancel hnpos]
          have hdPow : (1 - μ {0}) ^ ((p - n) + 1) =
              (1 - μ {0}) * (1 - μ {0}) ^ (p - n) := by
            rw [pow_succ]
            ac_rfl
          let S : ℝ≥0∞ :=
            ∑' k : ℕ, etaBridgeMass (eta μ) (p - n) n (j + (k : ℕ)) * (eta μ) {k}
          have hzeroAlg :
              μ {0} * ((p.choose (n - 1) : ℝ≥0∞) * μ {0} ^ (n - 1) *
                (1 - μ {0}) ^ ((p - n) + 1) * S) =
              (p.choose (n - 1) : ℝ≥0∞) *
                (μ {0} ^ n * ((1 - μ {0}) ^ ((p - n) + 1) * S)) := by
            calc
              _ = (p.choose (n - 1) : ℝ≥0∞) *
                  (μ {0} * μ {0} ^ (n - 1)) *
                    ((1 - μ {0}) ^ ((p - n) + 1) * S) := by ac_rfl
              _ = _ := by rw [haPow]; ac_rfl
          have hposAlg :
              (∑' k : ℕ, (p.choose n : ℝ≥0∞) *
                (etaBridgeMass (eta μ) (p - n) n (j + (k : ℕ)) *
                  ((eta μ) {k} * (μ {0} ^ n *
                    ((1 - μ {0}) ^ (p - n) * (1 - μ {0})))))) =
                (p.choose n : ℝ≥0∞) *
                  (μ {0} ^ n * ((1 - μ {0}) ^ ((p - n) + 1) * S)) := by
            calc
              _ = (p.choose n : ℝ≥0∞) *
                  ∑' k : ℕ, etaBridgeMass (eta μ) (p - n) n (j + (k : ℕ)) *
                    ((eta μ) {k} *
                      (μ {0} ^ n * ((1 - μ {0}) * (1 - μ {0}) ^ (p - n)))) := by
                rw [ENNReal.tsum_mul_left]
                apply congrArg
                apply tsum_congr
                intro k
                ac_rfl
              _ = (p.choose n : ℝ≥0∞) *
                  ((μ {0} ^ n * ((1 - μ {0}) * (1 - μ {0}) ^ (p - n))) * S) := by
                rw [hsumPos]
              _ = _ := by
                rw [← hdPow]
                simp [S, mul_assoc]
          have hposAlg' :
              (∑' k : ℕ, (1 - μ {0}) * (eta μ) {k} *
                ((p.choose n : ℝ≥0∞) * μ {0} ^ n * (1 - μ {0}) ^ (p - n) *
                  etaBridgeMass (eta μ) (p - n) n (j + (k : ℕ)))) =
                (p.choose n : ℝ≥0∞) *
                  (μ {0} ^ n * ((1 - μ {0}) ^ ((p - n) + 1) * S)) := by
            calc
              (∑' k : ℕ, (1 - μ {0}) * (eta μ) {k} *
                ((p.choose n : ℝ≥0∞) * μ {0} ^ n * (1 - μ {0}) ^ (p - n) *
                  etaBridgeMass (eta μ) (p - n) n (j + (k : ℕ)))) =
                ∑' k : ℕ, (p.choose n : ℝ≥0∞) *
                  (etaBridgeMass (eta μ) (p - n) n (j + (k : ℕ)) *
                    ((eta μ) {k} * (μ {0} ^ n *
                      ((1 - μ {0}) ^ (p - n) * (1 - μ {0}))))) := by
                apply tsum_congr
                intro k
                ac_rfl
              _ = _ := hposAlg
          calc
            _ = (p.choose (n - 1) : ℝ≥0∞) *
                  (μ {0} ^ n * ((1 - μ {0}) ^ ((p - n) + 1) * S)) +
                (p.choose n : ℝ≥0∞) *
                  (μ {0} ^ n * ((1 - μ {0}) ^ ((p - n) + 1) * S)) := by
              rw [hzeroAlg, hposAlg']
            _ = ((p.choose (n - 1) : ℝ≥0∞) + (p.choose n : ℝ≥0∞)) *
                  (μ {0} ^ n * ((1 - μ {0}) ^ ((p - n) + 1) * S)) := by
              rw [← add_mul]
            _ = ((p.choose (n - 1) + p.choose n : ℕ) : ℝ≥0∞) *
                  (μ {0} ^ n * ((1 - μ {0}) ^ ((p - n) + 1) * S)) := by
              simp
          have hcast : ((p.choose (n - 1) + p.choose n : ℕ) : ℝ≥0∞) =
              ((p + 1).choose n : ℝ≥0∞) := by exact_mod_cast hchoose.symm
          rw [hcast]
          simp only [S]
          rw [← hrec', ← hrec]
          ac_rfl

private theorem bridgeSum_add_eq_iff {p : ℕ} (ω : Fin p → ℕ) (a b : ℕ) :
    bridgeSum ω + (a : ℤ) = (b : ℤ) ↔ ∑ i : Fin p, ω i + a = b := by
  have hc : ((∑ i : Fin p, ω i + a : ℕ) : ℤ) =
      bridgeSum ω + (a : ℤ) := by
    simp [bridgeSum, Nat.cast_sum, Nat.cast_add]
  rw [← hc]
  constructor <;> intro h <;> exact_mod_cast h

/-- Bernoulli-by-`η` factorization of the leaf-marked forest bridge set under `Measure.pi`: with `n` leaves among `p` coordinates, the mass is `C(p,n) μ₀ⁿ (1-μ₀)^{p-n}` times the `η`-bridge mass. The binder `_hj : 1 ≤ j` is part of the frozen statement and unused. -/
theorem pi_leafMarkedBridges (μ : Measure ℕ) [IsProbabilityMeasure μ] (h0 : μ {0} ≠ 1)
    {j p n : ℕ} (_hj : 1 ≤ j) (hn : n ≤ p) :
    Measure.pi (fun _ : Fin p => μ) (leafMarkedForestBridges j p n) =
      (p.choose n : ℝ≥0∞) * μ {0} ^ n * (1 - μ {0}) ^ (p - n) *
        Measure.pi (fun _ : Fin (p - n) => eta μ) {ω | ∑ i, ω i + j = n} := by
  classical
  let : IsProbabilityMeasure (eta μ) := eta_isProbabilityMeasure μ h0
  have hleft : Measure.pi (fun _ : Fin p => μ) (leafMarkedForestBridges j p n) =
      bridgeMass μ p n (j : ℤ) := by
    rw [BGW.pi_eq_tsum_indicator μ (leafMarkedForestBridges j p n)]
    unfold bridgeMass
    apply tsum_congr
    intro ω
    have hmem : ω ∈ leafMarkedForestBridges j p n ↔
        bridgePredicate p n (j : ℤ) ω := by
      unfold leafMarkedForestBridges bridgePredicate zeroCount
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hs, hc⟩
        exact ⟨(bridgeSum_add_eq_iff ω j p).2 hs, hc⟩
      · rintro ⟨hs, hc⟩
        exact ⟨(bridgeSum_add_eq_iff ω j p).1 hs, hc⟩
    simp only [Set.indicator, Set.mem_ofPred_eq]
    exact if_congr hmem rfl rfl
  have hright :
      Measure.pi (fun _ : Fin (p - n) => eta μ) {ω | ∑ i, ω i + j = n} =
        etaBridgeMass (eta μ) (p - n) n (j : ℤ) := by
    rw [BGW.pi_eq_tsum_indicator (eta μ) {ω | ∑ i, ω i + j = n}]
    unfold etaBridgeMass
    apply tsum_congr
    intro ω
    have hmem : (∑ i : Fin (p - n), ω i + j = n) ↔
        bridgeSum ω + (j : ℤ) = (n : ℤ) :=
      (bridgeSum_add_eq_iff ω j n).symm
    simp only [Set.indicator, Set.mem_ofPred_eq]
    exact if_congr hmem rfl rfl
  rw [hleft, hright]
  exact bridgeMass_factorization μ h0 hn (j : ℤ)

end BGWLeaves.ForestLaw.Factorization
