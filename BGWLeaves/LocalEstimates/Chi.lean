module

public import BGWLeaves.LocalEstimates.Defs
public import BGWLeaves.Vervaat
import BGWLeaves.Vervaat.MarkTime
import BGWLeaves.Vervaat.Discrete
import BGWLeaves.Vervaat.Cyclic
import BGWLeaves.Vervaat.TimeReversal
import BGWLeaves.LocalEstimates.Technique
import BGWLeaves.LocalEstimates.NormRatios
import BGWLeaves.LeafMass.Arithmetic
import BGWLeaves.LeafMass.YLaw
import BGWLeaves.LeafConcentration.OeLemmas
import BGW.StableTrees.RegularVariation.Consequences
import BGWLeaves.StableAnalysis.TransformConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import BGWLeaves.StableAnalysis.EtaTransfer
import Mathlib.Probability.Independence.InfinitePi

/-! # M7 provider `Chi`: the signed stopped-walk estimates of Lemma 6.11. -/

@[expose] public section

namespace BGWLeaves.LocalEstimates.Chi

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW BGW.StableTrees
open BGWLeaves.StableAnalysis
open scoped ENNReal NNReal Topology

set_option linter.unusedSectionVars false

/- The finite Bernoulli–η factorization below is restated privately for signed endpoints.
The sealed forest version restricts its endpoint parameter to natural numbers. -/
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


private theorem isMarkTime_walkLeafTime {n : ℕ} {ω : ℕ → ℕ} {m : ℕ} (h : IsMarkTime n ω m) :
    walkLeafTime ω n = (m : ℕ∞) := by
  unfold walkLeafTime
  apply le_antisymm
  · exact iInf₂_le m h.1
  · refine le_iInf₂ fun q hq => ?_
    have : m ≤ q := by
      by_contra hlt
      have := h.2 q (not_le.1 hlt)
      omega
    exact_mod_cast this

private theorem walkLeafTime_ne_top_iff {n : ℕ} {ω : ℕ → ℕ} :
    walkLeafTime ω n ≠ ⊤ ↔ ∃ m, IsMarkTime n ω m := by
  constructor
  · intro h
    by_contra hne
    apply h
    have : ¬ ∃ m, walkLeafCount ω m = n := by
      rw [← BGWLeaves.Vervaat.MarkTime.exists_isMarkTime_iff]; exact hne
    unfold walkLeafTime
    simp only [iInf_eq_top]
    intro m hm
    exact absurd ⟨m, hm⟩ this
  · rintro ⟨m, hm⟩
    rw [isMarkTime_walkLeafTime hm]
    exact ENat.natCast_ne_top m

private theorem walkLeafTime_eq_coe_iff {n : ℕ} {ω : ℕ → ℕ} {m : ℕ} :
    walkLeafTime ω n = (m : ℕ∞) ↔ IsMarkTime n ω m := by
  constructor
  · intro h
    have hne : walkLeafTime ω n ≠ ⊤ := by rw [h]; exact ENat.natCast_ne_top m
    obtain ⟨m', hm'⟩ := walkLeafTime_ne_top_iff.1 hne
    have := isMarkTime_walkLeafTime hm'
    rw [h] at this
    have : m = m' := by exact_mod_cast this
    subst this
    exact hm'
  · exact isMarkTime_walkLeafTime


private theorem floor_cell (p : ℕ) {x : ℝ} (hx : x ∈ Set.Ioo (p : ℝ) (p + 1)) : ⌊x⌋₊ = p := by
  exact (Nat.floor_eq_iff ((Nat.cast_nonneg p).trans hx.1.le)).mpr ⟨hx.1.le, hx.2⟩

private theorem floor_step_integrable (f : ℕ → ℝ) (p : ℕ) :
    IntervalIntegrable (fun x : ℝ => f ⌊x⌋₊) volume p (p + 1) := by
  apply (intervalIntegrable_congr_uIoo (g := fun _ => f p) ?_).mpr intervalIntegrable_const
  rw [Set.uIoo_of_le (by linarith : (p : ℝ) ≤ p + 1)]
  intro x hx
  change f ⌊x⌋₊ = f p
  rw [floor_cell p hx]

private theorem floor_step_integral (f : ℕ → ℝ) (p : ℕ) :
    (∫ x in (p : ℝ)..(p + 1), f ⌊x⌋₊) = f p := by
  rw [intervalIntegral.integral_congr_Ioo_of_le (g := fun _ => f p)
    (by linarith : (p : ℝ) ≤ p + 1) (fun x hx => by rw [floor_cell p hx])]
  simp

private theorem floor_quad_nat (f : ℕ → ℝ) {l r : ℕ} (hlr : l ≤ r + 1) :
    (∫ x in (l : ℝ)..(r + 1), f ⌊x⌋₊) = ∑ p ∈ Finset.Icc l r, f p := by
  have hh := intervalIntegral.sum_integral_adjacent_intervals_Ico
    (a := fun p : ℕ => (p : ℝ)) (m := l) (n := r + 1) (f := fun x : ℝ => f ⌊x⌋₊) hlr
    (fun p _ => by simpa only [Nat.cast_add, Nat.cast_one] using floor_step_integrable f p)
  simp only [Nat.cast_add, Nat.cast_one] at hh
  rw [← hh]
  simp only [floor_step_integral]
  rw [Finset.Ico_add_one_right_eq_Icc]




private theorem last_mark_iff {n : ℕ} (hn : 1 ≤ n) (ω : ℕ → ℕ) (p : ℕ) :
    IsMarkTime n ω (p + 1) ↔ walkLeafCount ω p = n - 1 ∧ ω p = 0 := by
  rw [IsMarkTime]
  constructor
  · rintro ⟨hc, hmin⟩
    have hh := hmin p (by omega)
    rw [Vervaat.Discrete.walkLeafCount_succ'] at hc
    split_ifs at hc with h
    · exact ⟨by omega, h⟩
    · omega
  · rintro ⟨hp, hz⟩
    refine ⟨by rw [Vervaat.Discrete.walkLeafCount_succ', hp, ite_eq_left hz]; omega, ?_⟩
    intro q hq
    have hh := Vervaat.Discrete.walkLeafCount_mono' ω (show q ≤ p by omega)
    omega

private theorem walk_sum_succ (ω : ℕ → ℕ) (p : ℕ) : walkSum ω (p + 1) = walkSum ω p + ((ω p : ℤ) - 1) := by
  unfold walkSum
  rw [Finset.sum_range_succ]

private theorem prefix_count (ω : ℕ → ℕ) (p : ℕ) :
    zeroCount (fun i : Fin p => ω i) = walkLeafCount ω p := by
  classical
  simp only [zeroCount, walkLeafCount, Finset.card_filter]
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  have he : ((ω i : ℤ) - 1 = -1) ↔ ω i = 0 := by omega
  simp only [he]

private theorem prefix_sum (ω : ℕ → ℕ) (p : ℕ) :
    bridgeSum (fun i : Fin p => ω i) = walkSum ω p + p := by
  unfold bridgeSum walkSum
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul, mul_one]
  rw [Finset.sum_range]
  ring

private def lastMarkEvent (n : ℕ) (j : ℤ) (p : ℕ) : Set (ℕ → ℕ) :=
  {ω | walkLeafCount ω p = n - 1 ∧ ω p = 0 ∧ walkSum ω p = -j}

private theorem lastMarkEvent_iff {n : ℕ} (hn : 1 ≤ n) (j : ℤ) (p : ℕ) (ω : ℕ → ℕ) :
    ω ∈ lastMarkEvent n j p ↔ IsMarkTime n ω (p + 1) ∧ walkSum ω (p + 1) = -1 - j := by
  rw [last_mark_iff hn, walk_sum_succ]
  simp only [lastMarkEvent, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hc, hz, hs⟩
    exact ⟨⟨hc, hz⟩, by rw [hz, hs]; simp; ring⟩
  · rintro ⟨⟨hc, hz⟩, hs⟩
    refine ⟨hc, hz, ?_⟩
    rw [hz] at hs
    omega

private theorem prefix_pair_law (μ : PMF ℕ) (p : ℕ) :
    (iidWalk μ).map (fun ω => (ω p, fun i : Fin p => ω i)) =
      μ.toMeasure.prod (Measure.pi (fun _ : Fin p => μ.toMeasure)) := by
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (p + 1) => ℕ) (Fin.last p)
  have hp : (iidWalk μ).map (fun ω => fun i : Fin (p + 1) => ω i) = Measure.pi (fun _ : Fin (p + 1) => μ.toMeasure) := by
    rw [iidWalk, Measure.map_infinitePi_infinitePi_of_inj (P := fun _ : ℕ => μ.toMeasure) Fin.val_injective,
      Measure.infinitePi_eq_pi]
  have he := (measurePreserving_piFinSuccAbove (fun _ : Fin (p + 1) => μ.toMeasure) (Fin.last p)).map_eq
  rw [← hp, Measure.map_map e.measurable (by fun_prop)] at he
  convert he using 1
  congr 1
  funext ω
  apply Prod.ext
  · rfl
  · funext i
    change ω i = ω ((Fin.last p).succAbove i)
    rw [Fin.succAbove_last]
    rfl

private theorem lastMarkEvent_mass (μ : PMF ℕ) (n : ℕ) (j : ℤ) (p : ℕ) :
    iidWalk μ (lastMarkEvent n j p) = μ 0 * bridgeMass μ.toMeasure p (n - 1) j := by
  let B : Set (Fin p → ℕ) := {ω | bridgePredicate p (n - 1) j ω}
  have hm : Measurable (fun ω : ℕ → ℕ => (ω p, fun i : Fin p => ω i)) := by fun_prop
  have hB : MeasurableSet B := (Set.to_countable _).measurableSet
  have hpre : (fun ω : ℕ → ℕ => (ω p, fun i : Fin p => ω i)) ⁻¹' ({0} ×ˢ B) = lastMarkEvent n j p := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_prod, Set.mem_singleton_iff, B, bridgePredicate,
      Set.mem_ofPred_eq, lastMarkEvent, prefix_count, prefix_sum]
    constructor <;> intro h <;> omega
  have hh := congrArg (fun P : Measure (ℕ × (Fin p → ℕ)) => P ({0} ×ˢ B)) (prefix_pair_law μ p)
  rw [Measure.map_apply hm ((measurableSet_singleton 0).prod hB), hpre,
    Measure.prod_prod, PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0)] at hh
  rw [hh, BGW.pi_eq_tsum_indicator μ.toMeasure B]
  rfl

private theorem lastMarkEvent_measurable (n : ℕ) (j : ℤ) (p : ℕ) : MeasurableSet (lastMarkEvent n j p) := by
  exact (measurableSet_eq_fun (Vervaat.TimeReversal.measurable_walkLeafCount p) measurable_const).inter
    (((measurable_pi_apply p) (measurableSet_singleton 0)).inter
      (Vervaat.Cyclic.measurable_walkSum p (measurableSet_singleton (-j))))

private noncomputable def supZ (S : Finset ℤ) (f : ℤ → ℝ) : ℝ := ⨆ j ∈ S, f j

private noncomputable def signedRange (μ : PMF ℕ) (θ α : ℝ) (n : ℕ) : Finset ℤ :=
  Finset.Icc (-(⌊α * normB μ θ n⌋₊ : ℤ)) (⌊α * normB μ θ n⌋₊ : ℤ)

private theorem signedRange_bound {μ : PMF ℕ} {θ α : ℝ} {n : ℕ}
    (hB : 0 ≤ α * normB μ θ n) {j : ℤ} (hj : j ∈ signedRange μ θ α n) : |(j : ℝ)| ≤ α * normB μ θ n := by
  have hh : |j| ≤ (⌊α * normB μ θ n⌋₊ : ℤ) := abs_le.mpr (Finset.mem_Icc.mp hj)
  have hr : |(j : ℝ)| ≤ (⌊α * normB μ θ n⌋₊ : ℝ) := by exact_mod_cast hh
  exact hr.trans (Nat.floor_le hB)

private theorem signedRange_mem {μ : PMF ℕ} {θ α : ℝ} {n : ℕ} {j : ℤ}
    (hj : |(j : ℝ)| ≤ α * normB μ θ n) : j ∈ signedRange μ θ α n := by
  have hh : (j.natAbs : ℝ) ≤ α * normB μ θ n := by simpa only [Nat.cast_natAbs, Int.cast_abs] using hj
  have hi : |j| ≤ (⌊α * normB μ θ n⌋₊ : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast Nat.le_floor hh
  exact Finset.mem_Icc.mpr (abs_le.mp hi)

private theorem supZ_bounds {S : Finset ℤ} {f : ℤ → ℝ} {C : ℝ}
    (hC : 0 ≤ C) (hf : ∀ j ∈ S, 0 ≤ f j ∧ f j ≤ C) :
    0 ≤ supZ S f ∧ supZ S f ≤ C ∧ ∀ j ∈ S, f j ≤ supZ S f := by
  classical
  have hi (j : ℤ) : (⨆ _ : j ∈ S, f j) = if j ∈ S then f j else 0 := by
    by_cases hj : j ∈ S <;> simp [hj]
  have hb (j : ℤ) : (⨆ _ : j ∈ S, f j) ≤ C := by
    rw [hi]
    split_ifs with hj
    · exact (hf j hj).2
    · exact hC
  have hB : BddAbove (Set.range (fun j : ℤ => ⨆ _ : j ∈ S, f j)) := by
    refine ⟨C, ?_⟩
    rintro x ⟨j, rfl⟩
    exact hb j
  have h0 : 0 ≤ (⨆ _ : (0 : ℤ) ∈ S, f 0) := by
    rw [hi]
    split_ifs with hj
    · exact (hf 0 hj).1
    · exact le_rfl
  refine ⟨h0.trans (le_ciSup hB 0), ciSup_le hb, ?_⟩
  intro j hj
  have hh := le_ciSup hB j
  simpa only [supZ, hi, ite_eq_left hj] using hh

private theorem supZ_measurable {S : Finset ℤ} {f : ℤ → ℝ → ℝ}
    (hf : ∀ j, Measurable (f j)) : Measurable (fun u => supZ S (fun j => f j u)) := by
  exact Measurable.iSup (fun j => Measurable.iSup (fun _ : j ∈ S => hf j))

private noncomputable def aWindow (μ : PMF ℕ) (ε : ℝ) (n : ℕ) : ℝ → ℝ :=
  (Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)).indicator (aN μ n)

private noncomputable def chiError (μ : PMF ℕ) (θ α ε : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  supZ (signedRange μ θ α n) fun j =>
    |aWindow μ ε n u * bN μ θ n u (j + 1) -
      F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)|

private theorem aN_nonneg (μ : PMF ℕ) (n : ℕ) (u : ℝ) : 0 ≤ aN μ n u := by
  have hm : (μ 0).toReal ≤ 1 := by
    simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
  have hq : 0 ≤ 1 - (μ 0).toReal := sub_nonneg.mpr hm
  unfold aN binomProb
  positivity

private theorem aN_measurable (μ : PMF ℕ) (n : ℕ) : Measurable (aN μ n) := by
  have hp : Measurable (rN μ n) :=
    Nat.measurable_floor.comp (measurable_const.add (measurable_id.mul_const _))
  exact ((measurable_of_countable (fun p : ℕ => binomProb (μ 0).toReal p n)).comp hp).const_mul _

private theorem bN_measurable (μ : PMF ℕ) (θ : ℝ) (n : ℕ) (j : ℤ) : Measurable (bN μ θ n · j) := by
  have hp : Measurable (rN μ n) :=
    Nat.measurable_floor.comp (measurable_const.add (measurable_id.mul_const _))
  exact ((measurable_of_countable (fun p : ℕ => intWalkProb (etaLaw μ) (p - n) ((n : ℤ) - j))).comp hp).const_mul _

private theorem G0_continuous {μ : PMF ℕ} {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) (x : ℝ) :
    Continuous (fun u : ℝ => G0 μ θ u x) := by
  have hd := Scalar.continuous_stableDensity hθ
  unfold G0 finVarShift
  split_ifs <;> fun_prop

private theorem F0_integrable {m : ℝ} (hm : 0 < m) (hm1 : m < 1) : Integrable (F0 m) := by
  have ha : 0 < m ^ 2 / (2 * (1 - m)) := by positivity
  apply ((integrable_exp_neg_mul_sq ha).div_const (Real.sqrt (2 * Real.pi * (1 - m)))).congr
  exact Eventually.of_forall fun u => by
    exact congrArg (fun t : ℝ => Real.exp t / Real.sqrt (2 * Real.pi * (1 - m)))
      (by ring : -(m ^ 2 / (2 * (1 - m))) * u ^ 2 = -(m ^ 2 * u ^ 2) / (2 * (1 - m)))

private theorem window_weight_integrable : Integrable (fun u : ℝ => 1 / max 1 (u ^ 2)) := by
  have hm : Measurable (fun u : ℝ => 1 / max 1 (u ^ 2)) := by fun_prop
  apply (integrable_inv_one_add_sq.const_mul 2).mono' hm.aestronglyMeasurable
  exact Eventually.of_forall fun u => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / max 1 (u ^ 2))]
    rw [show 2 * (1 + u ^ 2)⁻¹ = 2 / (1 + u ^ 2) by rfl]
    apply (div_le_div_iff₀ (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (by positivity)).mpr
    nlinarith [le_max_left (1 : ℝ) (u ^ 2), le_max_right (1 : ℝ) (u ^ 2)]

private theorem chiError_measurable {μ : PMF ℕ} {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2)
    (α ε : ℝ) (n : ℕ) : Measurable (chiError μ θ α ε n) := by
  apply supZ_measurable
  intro j
  have ha : Measurable (aWindow μ ε n) := (aN_measurable μ n).indicator measurableSet_Icc
  have hf : Measurable (F0 (μ 0).toReal) := by unfold F0; fun_prop
  have hh := ((ha.mul (bN_measurable μ θ n (j + 1))).sub
    (hf.mul (G0_continuous (μ := μ) hθ ((j : ℝ) / norming (etaLaw μ) θ n)).measurable)).norm
  simpa only [Real.norm_eq_abs, Pi.sub_apply, Pi.mul_apply] using hh


private theorem rN_window_bounds {μ : PMF ℕ} (hm : 0 < (μ 0).toReal)
    (hm1 : (μ 0).toReal < 1) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal))
    {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : |u| ≤ ε * Real.sqrt n) :
    n ≤ rN μ n u ∧ (rN μ n u : ℝ) ≤ (1 / (μ 0).toReal + ε) * n ∧
      |(rN μ n u : ℝ) - ((n : ℝ) / (μ 0).toReal + u * Real.sqrt n)| ≤ 1 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hεm : ε * (μ 0).toReal < 1 - (μ 0).toReal := by
    rw [lt_div_iff₀ (by positivity)] at hε1
    nlinarith
  have hcoef : 1 < 1 / (μ 0).toReal - ε := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ hm]
    nlinarith
  have hs := Real.sq_sqrt (Nat.cast_nonneg n)
  have hulo : -ε * (n : ℝ) ≤ u * Real.sqrt n := by
    have hh := mul_le_mul_of_nonneg_right (neg_le_of_abs_le hu) (Real.sqrt_nonneg (n : ℝ))
    nlinarith
  have huhi : u * Real.sqrt n ≤ ε * (n : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right (le_of_abs_le hu) (Real.sqrt_nonneg (n : ℝ))
    nlinarith
  have hlo : (n : ℝ) ≤ (n : ℝ) / (μ 0).toReal + u * Real.sqrt n := by
    have hh := mul_le_mul_of_nonneg_right hcoef.le (Nat.cast_nonneg n)
    rw [one_mul] at hh
    have heq : (1 / (μ 0).toReal - ε) * (n : ℝ) = (n : ℝ) / (μ 0).toReal - ε * n := by ring
    rw [heq] at hh
    linarith
  have hv0 : 0 ≤ (n : ℝ) / (μ 0).toReal + u * Real.sqrt n := (by positivity : (0 : ℝ) ≤ n).trans hlo
  have hfloor : (rN μ n u : ℝ) ≤ (n : ℝ) / (μ 0).toReal + u * Real.sqrt n := Nat.floor_le hv0
  refine ⟨Nat.le_floor hlo, ?_, ?_⟩
  · have heq : (1 / (μ 0).toReal + ε) * (n : ℝ) = (n : ℝ) / (μ 0).toReal + ε * n := by ring
    rw [heq]
    linarith
  · have hh := Nat.lt_floor_add_one ((n : ℝ) / (μ 0).toReal + u * Real.sqrt n)
    change (n : ℝ) / (μ 0).toReal + u * Real.sqrt n < (rN μ n u : ℝ) + 1 at hh
    rw [abs_le]
    constructor <;> linarith


private theorem sqrt_nat_div_self :
    Tendsto (fun n : ℕ => Real.sqrt n / n) atTop (𝓝 (0 : ℝ)) := by
  have ht := (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop).inv_tendsto_atTop
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sq_sqrt hnR.le
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  change (Real.sqrt (n : ℝ))⁻¹ = Real.sqrt (n : ℝ) / n
  field_simp
  nlinarith

private theorem floor_index_ratio {u : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hu : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (⌊u n⌋₊ : ℝ) / n) atTop (𝓝 l) := by
  have hlow : Tendsto (fun n : ℕ => u n / n - 1 / (n : ℝ)) atTop (𝓝 l) := by
    simpa only [sub_zero] using hu.sub tendsto_one_div_atTop_nhds_zero_nat
  have hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ u n ∧ 0 < (n : ℝ) := by
    filter_upwards [hu.eventually (Ioi_mem_nhds hl), eventually_ge_atTop 1] with n hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [lt_div_iff₀ hnR, zero_mul] at hn
    exact ⟨hn.le, hnR⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow hu
  · filter_upwards [hpos] with n hn
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by linarith [Nat.lt_floor_add_one (u n)]) hn.2.le
  · filter_upwards [hpos] with n hn
    exact div_le_div_of_nonneg_right (Nat.floor_le hn.1) hn.2.le

private theorem rN_ratio {μ : PMF ℕ} (hm : 0 < (μ 0).toReal) (u : ℝ) :
    Tendsto (fun n : ℕ => (rN μ n u : ℝ) / n) atTop (𝓝 (1 / (μ 0).toReal)) := by
  apply floor_index_ratio (one_div_pos.mpr hm)
  have ht' : Tendsto (fun n : ℕ => 1 / (μ 0).toReal + u * (Real.sqrt n / n)) atTop
      (𝓝 (1 / (μ 0).toReal)) := by
    simpa only [mul_zero, add_zero] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => 1 / (μ 0).toReal) atTop
        (𝓝 (1 / (μ 0).toReal))).add (sqrt_nat_div_self.const_mul u)
  apply ht'.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp


section Htheta
variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b) (hnl : ¬ IsLatticeLaw (etaLaw μ))
include hc hne hap hDA hnl

theorem chi_retenir {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / (μ 0).toReal) {n : ℕ} (hn : 1 ≤ n) (j : ℤ)
    (hB : 0 < norming (etaLaw μ) θ n) :
    norming (etaLaw μ) θ n * ((μ 0).toReal * ∑ k ∈ Finset.Icc (⌈(n : ℝ) / (μ 0).toReal - ε * n⌉.toNat)
          ⌊(n : ℝ) / (μ 0).toReal + ε * n⌋₊,
        binomProb (μ 0).toReal (k - 1) (n - 1) * intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j)) =
      (μ 0).toReal * ∫ u in ((⌈(n : ℝ) / (μ 0).toReal - ε * n⌉ - (n : ℝ) / (μ 0).toReal) / Real.sqrt n)..
            ((⌊(n : ℝ) / (μ 0).toReal + ε * n⌋ + 1 - (n : ℝ) / (μ 0).toReal) / Real.sqrt n),
          Real.sqrt n * binomProb (μ 0).toReal (rN μ n u - 1) (n - 1) * bN μ θ n u (j + 1) := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  let a : ℝ := (n : ℝ) / (μ 0).toReal - ε * n
  let b : ℝ := (n : ℝ) / (μ 0).toReal + ε * n
  let f : ℕ → ℝ := fun k => binomProb (μ 0).toReal (k - 1) (n - 1) *
    intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j)
  have ha : 0 ≤ a := by
    dsimp [a]
    rw [div_eq_mul_inv, mul_comm (n : ℝ)]
    have hh := mul_lt_mul_of_pos_right hε1 hnR
    rw [one_div] at hh
    linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hab : a ≤ b := by dsimp [a, b]; nlinarith
  have hlr : ⌈a⌉₊ ≤ ⌊b⌋₊ + 1 := (Nat.ceil_mono hab).trans (Nat.ceil_le_floor_add_one b)
  have hquad : (∫ x in (⌈a⌉ : ℤ)..((⌊b⌋ : ℤ) + 1 : ℝ), f ⌊x⌋₊) =
      ∑ k ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, f k := by
    rw [← natCast_ceil_eq_intCast_ceil ha, ← natCast_floor_eq_intCast_floor hb]
    exact floor_quad_nat f hlr
  have haff := intervalIntegral.integral_comp_add_mul (fun x : ℝ => f ⌊x⌋₊) hs.ne' ((n : ℝ) / (μ 0).toReal)
    (a := (((⌈a⌉ : ℤ) : ℝ) - (n : ℝ) / (μ 0).toReal) / Real.sqrt n)
    (b := (((⌊b⌋ : ℤ) : ℝ) + 1 - (n : ℝ) / (μ 0).toReal) / Real.sqrt n)
  have hleft : (n : ℝ) / (μ 0).toReal + Real.sqrt n *
      ((((⌈a⌉ : ℤ) : ℝ) - (n : ℝ) / (μ 0).toReal) / Real.sqrt n) = (⌈a⌉ : ℤ) := by field_simp; ring
  have hright : (n : ℝ) / (μ 0).toReal + Real.sqrt n *
      ((((⌊b⌋ : ℤ) : ℝ) + 1 - (n : ℝ) / (μ 0).toReal) / Real.sqrt n) = (⌊b⌋ : ℤ) + 1 := by field_simp; ring
  rw [hleft, hright, smul_eq_mul, hquad] at haff
  have heq (u : ℝ) : Real.sqrt n * binomProb (μ 0).toReal (rN μ n u - 1) (n - 1) * bN μ θ n u (j + 1) =
      (Real.sqrt n * norming (etaLaw μ) θ n) * f ⌊(n : ℝ) / (μ 0).toReal + Real.sqrt n * u⌋₊ := by
    have hidx : ⌊(n : ℝ) / (μ 0).toReal + Real.sqrt n * u⌋₊ = rN μ n u := by
      unfold rN
      rw [mul_comm (Real.sqrt n) u]
    simp only [hidx, f, bN]
    rw [show (n : ℤ) - (j + 1) = (n : ℤ) - 1 - j by ring]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul, haff, Int.ceil_toNat]
  change norming (etaLaw μ) θ n * ((μ 0).toReal * ∑ k ∈ Finset.Icc ⌈a⌉₊ ⌊b⌋₊, f k) = _
  field_simp

private theorem eta_bridge_real (p n : ℕ) (j : ℤ) :
    (etaBridgeMass (eta μ.toMeasure) p n j).toReal = intWalkProb (etaLaw μ) p ((n : ℤ) - j) := by
  let := LeafMass.Arithmetic.eta_isProbabilityMeasure hc hne
  let := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have he : etaBridgeMass (eta μ.toMeasure) p n j =
      (Measure.pi (fun _ : Fin p => eta μ.toMeasure)) {ω | bridgeSum ω + j = n} := by
    rw [BGW.pi_eq_tsum_indicator]
    rfl
  rw [he, intWalkProb, LeafMass.Arithmetic.intWalk_eq_map_sum,
    ← LeafMass.Arithmetic.eta_map_cast_eq_etaLaw,
    ← Measure.pi_map_pi (μ := fun _ : Fin p => eta μ.toMeasure)
      (f := fun _ : Fin p => fun k : ℕ => (k : ℤ))
      (fun _ => (measurable_of_countable _).aemeasurable), measureReal_def,
    Measure.map_apply (measurable_of_countable _) (measurableSet_singleton _),
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _).measurableSet]
  congr 2
  ext ω
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, bridgeSum]
  omega

private theorem lastMarkEvent_real {n : ℕ} (hn : 1 ≤ n) (j : ℤ) (p : ℕ) :
    (iidWalk μ).real (lastMarkEvent n j p) =
      (μ 0).toReal * binomProb (μ 0).toReal p (n - 1) *
        intWalkProb (etaLaw μ) (p - (n - 1)) ((n : ℤ) - 1 - j) := by
  by_cases hnp : n - 1 ≤ p
  · have hμ : μ.toMeasure {0} ≠ 1 := by simpa only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)] using NormRatios.mu0_ne_one hc hne
    rw [measureReal_def, lastMarkEvent_mass, bridgeMass_factorization μ.toMeasure hμ hnp j,
      ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_mul,
      ENNReal.toReal_pow, ENNReal.toReal_pow,
      ENNReal.toReal_sub_of_le prob_le_one ENNReal.one_ne_top,
      PMF.toMeasure_apply_singleton μ 0 (measurableSet_singleton 0),
      eta_bridge_real hc hne hap hDA hnl]
    simp only [ENNReal.toReal_natCast, ENNReal.toReal_one, Nat.cast_sub hn, Nat.cast_one, binomProb]
    ring
  · have he : lastMarkEvent n j p = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro ω ⟨hc, -, -⟩
      have hh : walkLeafCount ω p ≤ p := by
        unfold walkLeafCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      omega
    rw [he, measureReal_empty, binomProb, Nat.choose_eq_zero_of_lt (by omega)]
    simp

private theorem stop_event_union {n : ℕ} (hn : 1 ≤ n) (j : ℤ) :
    walkStopEvent n (-1 - j) = ⋃ q : ℕ, lastMarkEvent n j (n - 1 + q) := by
  ext ω
  constructor
  · rintro ⟨hfinite, hpos⟩
    obtain ⟨m, hm⟩ := walkLeafTime_ne_top_iff.mp hfinite
    have hm0 : m ≠ 0 := by
      intro hz
      have hh := hm.1
      simp [hz, walkLeafCount] at hh
      omega
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm0
    have hcount := (last_mark_iff hn ω p).mp hm
    have hp : n - 1 ≤ p := by
      have hh : walkLeafCount ω p ≤ p := by
        unfold walkLeafCount
        exact (Finset.card_filter_le _ _).trans (by simp)
      omega
    apply Set.mem_iUnion.mpr
    refine ⟨p - (n - 1), ?_⟩
    rw [Nat.add_sub_of_le hp]
    apply (lastMarkEvent_iff hn j p ω).mpr
    refine ⟨hm, ?_⟩
    simpa only [walkStopPos, isMarkTime_walkLeafTime hm, ENat.toNat_natCast] using hpos
  · intro h
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp h
    obtain ⟨hm, hpos⟩ := (lastMarkEvent_iff hn j (n - 1 + q) ω).mp hq
    refine ⟨by rw [isMarkTime_walkLeafTime hm]; exact ENat.natCast_ne_top _, ?_⟩
    simpa only [walkStopPos, isMarkTime_walkLeafTime hm, ENat.toNat_natCast] using hpos

private theorem lastMarkEvent_disjoint {n : ℕ} (hn : 1 ≤ n) (j : ℤ) :
    Pairwise (Function.onFun Disjoint (lastMarkEvent n j)) := by
  intro p q hpq
  apply Set.disjoint_left.mpr
  intro ω hp hq
  have hmp := ((lastMarkEvent_iff hn j p ω).mp hp).1
  have hmq := ((lastMarkEvent_iff hn j q ω).mp hq).1
  have hh := Vervaat.MarkTime.IsMarkTime.unique hmp hmq
  omega

theorem chi_eq_tsum {n : ℕ} (hn : 1 ≤ n) (j : ℤ) :
    (chi μ n j).toReal =
      (μ 0).toReal * ∑' q : ℕ, binomProb (μ 0).toReal (n - 1 + q) (n - 1) *
        intWalkProb (etaLaw μ) q ((n : ℤ) - 1 - j) := by
  unfold chi
  rw [stop_event_union hc hne hap hDA hnl hn,
    measure_iUnion (f := fun q => lastMarkEvent n j (n - 1 + q)) (fun p q hpq => by apply lastMarkEvent_disjoint hc hne hap hDA hnl hn j; omega)
      (fun q => lastMarkEvent_measurable n j (n - 1 + q)),
    ENNReal.tsum_toReal_eq (fun q => measure_ne_top _ _)]
  simp_rw [← measureReal_def, lastMarkEvent_real hc hne hap hDA hnl hn j, Nat.add_sub_cancel_left, mul_assoc]
  rw [tsum_mul_left]

private theorem finite_mark_window {n : ℕ} (hn : 1 ≤ n) (j : ℤ) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 1 ≤ k) :
    (iidWalk μ).real (⋃ k ∈ S, lastMarkEvent n j (k - 1)) =
      (μ 0).toReal * ∑ k ∈ S, binomProb (μ 0).toReal (k - 1) (n - 1) *
        intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j) := by
  rw [measureReal_biUnion_finset (f := fun k => lastMarkEvent n j (k - 1)) (fun p hp q hq hpq => by
      apply lastMarkEvent_disjoint hc hne hap hDA hnl hn j
      have := hS p hp
      have := hS q hq
      omega) (fun k _ => lastMarkEvent_measurable n j (k - 1))]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [lastMarkEvent_real hc hne hap hDA hnl hn j]
  have hidx : k - 1 - (n - 1) = k - n := by have := hS k hk; omega
  rw [hidx, mul_assoc]

private theorem mark_window_subset {n : ℕ} (hn : 1 ≤ n) (j : ℤ) (S : Finset ℕ) :
    (⋃ k ∈ S, lastMarkEvent n j (k - 1)) ⊆ walkStopEvent n (-1 - j) := by
  intro ω hω
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp hω
  obtain ⟨hkS, hk⟩ := Set.mem_iUnion.mp hk
  obtain ⟨hm, hs⟩ := (lastMarkEvent_iff hn j (k - 1) ω).mp hk
  exact ⟨by rw [isMarkTime_walkLeafTime hm]; exact ENat.natCast_ne_top _,
    by simpa only [walkStopPos, isMarkTime_walkLeafTime hm, ENat.toNat_natCast] using hs⟩

private theorem window_error_mass {n : ℕ} (hn : 1 ≤ n) (j : ℤ) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 1 ≤ k) :
    |(chi μ n j).toReal - (μ 0).toReal * ∑ k ∈ S, binomProb (μ 0).toReal (k - 1) (n - 1) *
      intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j)| =
      (iidWalk μ).real (walkStopEvent n (-1 - j) \ ⋃ k ∈ S, lastMarkEvent n j (k - 1)) := by
  rw [← finite_mark_window hc hne hap hDA hnl hn j S hS,
    measureReal_sdiff (mark_window_subset hc hne hap hDA hnl hn j S)
      (MeasurableSet.biUnion (Finset.countable_toSet S) (fun k _ => lastMarkEvent_measurable n j (k - 1)))]
  apply abs_of_nonneg
  exact sub_nonneg.mpr (measureReal_mono (mark_window_subset hc hne hap hDA hnl hn j S))

theorem chi_window {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1 / (μ 0).toReal) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ n : ℕ, 1 ≤ n → ∀ j : ℤ,
      |(chi μ n j).toReal - (μ 0).toReal * ∑ k ∈ Finset.Icc (⌈(n : ℝ) / (μ 0).toReal - ε * n⌉.toNat)
          ⌊(n : ℝ) / (μ 0).toReal + ε * n⌋₊,
        binomProb (μ 0).toReal (k - 1) (n - 1) * intWalkProb (etaLaw μ) (k - n) ((n : ℤ) - 1 - j)| ≤
        C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  let S : ℕ → Finset ℕ := fun n => Finset.Icc ⌈(n : ℝ) / (μ 0).toReal - ε * n⌉₊ ⌊(n : ℝ) / (μ 0).toReal + ε * n⌋₊
  have hS (n : ℕ) (hn : 1 ≤ n) : ∀ k ∈ S n, 1 ≤ k := by
    intro k hk
    have ha : 0 < (n : ℝ) / (μ 0).toReal - ε * n := by
      have hh := mul_lt_mul_of_pos_right hε1 (show (0 : ℝ) < n by exact_mod_cast hn)
      rw [one_div, mul_comm ((μ 0).toReal)⁻¹, ← div_eq_mul_inv] at hh
      linarith
    have hc : 1 ≤ ⌈(n : ℝ) / (μ 0).toReal - ε * n⌉₊ := Nat.ceil_pos.mpr ha
    exact hc.trans (Finset.mem_Icc.mp hk).1
  obtain ⟨C, c, hC, hcp, hb⟩ := Vervaat.MarkTime.lem_CVf2_i μ (hc.apply_zero_ne_zero hne) (NormRatios.mu0_ne_one hc hne)
  have ht : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ (1 / 4 : ℝ)) atTop (𝓝 0) := by
    have hh := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
    apply hh.congr'
    exact Eventually.of_forall fun n => by
      change (n : ℝ) ^ (-(1 / 4 : ℝ)) = 1 / (n : ℝ) ^ (1 / 4 : ℝ)
      simp only [Real.rpow_neg (Nat.cast_nonneg n), one_div]
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_lt_nhds hε))
  have hlarge (n : ℕ) (hn : 1 ≤ n) (hnN : N ≤ n) (j : ℤ) :
      (iidWalk μ).real (walkStopEvent n (-1 - j) \ ⋃ k ∈ S n, lastMarkEvent n j (k - 1)) ≤
        C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
    apply (measureReal_mono (μ := iidWalk μ) (s₂ := {ω | (¬ ∃ k, IsMarkTime n ω k) ∨
      ∃ k, IsMarkTime n ω k ∧ 1 / (n : ℝ) ^ (1 / 4 : ℝ) < |(k : ℝ) / n - 1 / (μ 0).toReal|}) ?_).trans (hb n)
    rintro ω ⟨hstop, hnot⟩
    rw [stop_event_union hc hne hap hDA hnl hn j] at hstop
    obtain ⟨q, hq⟩ := Set.mem_iUnion.mp hstop
    have hmark := ((lastMarkEvent_iff hn j (n - 1 + q) ω).mp hq).1
    have heq : n - 1 + q + 1 = n + q := by omega
    rw [heq] at hmark
    have hH : ω ∈ lastMarkEvent n j (n + q - 1) := by
      have hh : n + q - 1 = n - 1 + q := by omega
      simpa only [hh] using hq
    have hout : ε * n < |((n + q : ℕ) : ℝ) - n / (μ 0).toReal| := by
      by_contra h
      have hh := abs_le.mp (le_of_not_gt h)
      apply hnot
      refine Set.mem_iUnion.mpr ⟨n + q, Set.mem_iUnion.mpr ⟨?_, hH⟩⟩
      apply Finset.mem_Icc.mpr
      exact ⟨Nat.ceil_le.mpr (by linarith [hh.1]), Nat.le_floor (by linarith [hh.2])⟩
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have he : ((n + q : ℕ) : ℝ) / n - 1 / (μ 0).toReal =
        (((n + q : ℕ) : ℝ) - n / (μ 0).toReal) / n := by field_simp
    refine Or.inr ⟨n + q, hmark, (hN n hnN).trans ?_⟩
    rw [he, abs_div, abs_of_pos hnR, lt_div_iff₀ hnR]
    exact hout
  refine ⟨C + Real.exp (c * (N : ℝ) ^ (1 / 2 : ℝ)), c, by positivity, hcp, fun n hn j => ?_⟩
  rw [Int.ceil_toNat, window_error_mass hc hne hap hDA hnl hn j (S n) (hS n hn)]
  by_cases hnN : N ≤ n
  · exact (hlarge n hn hnN j).trans (mul_le_mul_of_nonneg_right (by linarith [Real.exp_pos (c * (N : ℝ) ^ (1 / 2 : ℝ))]) (Real.exp_pos _).le)
  · have hx : (iidWalk μ).real (walkStopEvent n (-1 - j) \ ⋃ k ∈ S n, lastMarkEvent n j (k - 1)) ≤ 1 := measureReal_le_one
    have hpow : (n : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (1 / 2 : ℝ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (show n ≤ N by omega)) (by norm_num)
    have he : 1 ≤ Real.exp (c * (N : ℝ) ^ (1 / 2 : ℝ)) * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)) := by
      rw [← Real.exp_add, Real.one_le_exp_iff]
      nlinarith
    exact hx.trans (he.trans (mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le))

private theorem norming_step_top : Tendsto (norming (stepLaw μ) θ) atTop atTop := by
  obtain ⟨b, hb⟩ := hDA
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  exact TransformConvergence.tendsto_atTop (stepLaw μ) ha

private theorem norming_eta_top : Tendsto (norming (etaLaw μ) θ) atTop atTop := by
  let := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have ha := (etaLaw_norming hc hne (NormRatios.hS_of_nonLattice hc hne hnl) hDA).1
  exact TransformConvergence.tendsto_atTop (etaLaw μ) ha

private theorem bN_shift_tendsto (u : ℝ) {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |bN μ θ n u (j + 1) - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ η := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  obtain ⟨K, hLip⟩ : ∃ K : ℝ≥0, LipschitzWith K (Scalar.stableDensity θ) :=
    ⟨_, Scalar.lipschitzWith_stableDensity hb.alpha_mem⟩
  let L : ℝ := cC μ ^ (1 / θ)
  have hL : 0 < L := Real.rpow_pos_of_pos (div_pos
    (ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0))
    (EtaTransfer.one_sub_apply_zero_pos hc hne)) _
  have ht : Tendsto (fun n : ℕ => L * L * (K : ℝ) * (norming (etaLaw μ) θ n)⁻¹) atTop (𝓝 0) := by
    simpa using ((tendsto_inv_atTop_zero.comp (norming_eta_top hc hne hap hDA hnl)).const_mul (L * L * (K : ℝ)))
  obtain ⟨N₁, h₁⟩ := Technique.bN_tendsto_signed hc hne hap hDA hnl u (by positivity : 0 < 2 * α) (half_pos hη)
  obtain ⟨N₂, h₂⟩ := eventually_atTop.mp
    ((ht.eventually (eventually_lt_nhds (half_pos hη))).and
      (((Filter.Tendsto.const_mul_atTop hα (norming_step_top hc hne hap hDA hnl)).eventually (eventually_ge_atTop 1)).and
        ((norming_eta_top hc hne hap hDA hnl).eventually (eventually_gt_atTop 0))))
  refine ⟨max N₁ N₂, fun n hn j hj => ?_⟩
  obtain ⟨hsm, hBn, hBp⟩ := h₂ n (le_of_max_le_right hn)
  have hjshift : |((j + 1 : ℤ) : ℝ)| ≤ 2 * α * normB μ θ n := by
    rw [Int.cast_add, Int.cast_one]
    have hh := abs_add_le (j : ℝ) 1
    rw [abs_one] at hh
    rw [normB_natCast] at hj ⊢
    nlinarith
  have hmain := h₁ n (le_of_max_le_left hn) (j + 1) hjshift
  have hd : |G0 μ θ u (((j + 1 : ℤ) : ℝ) / norming (etaLaw μ) θ n) -
      G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ η / 2 := by
    let x := -(L * (((j + 1 : ℤ) : ℝ) / norming (etaLaw μ) θ n)) - finVarShift μ u
    let y := -(L * ((j : ℝ) / norming (etaLaw μ) θ n)) - finVarShift μ u
    have harg : |x - y| = L * (norming (etaLaw μ) θ n)⁻¹ := by
      have heq : x - y = -(L / norming (etaLaw μ) θ n) := by dsimp [x, y]; push_cast; ring
      rw [heq, abs_neg, abs_of_pos (div_pos hL hBp), div_eq_mul_inv]
    have hh := hLip.dist_le_mul x y
    rw [Real.dist_eq, Real.dist_eq, harg] at hh
    change |L * Scalar.stableDensity θ x - L * Scalar.stableDensity θ y| ≤ η / 2
    rw [← mul_sub, abs_mul, abs_of_pos hL]
    calc _ ≤ L * ((K : ℝ) * (L * (norming (etaLaw μ) θ n)⁻¹)) := mul_le_mul_of_nonneg_left hh hL.le
      _ = L * L * (K : ℝ) * (norming (etaLaw μ) θ n)⁻¹ := by ring
      _ ≤ η / 2 := hsm.le
  calc
    _ ≤ |bN μ θ n u (j + 1) - G0 μ θ u (((j + 1 : ℤ) : ℝ) / norming (etaLaw μ) θ n)| +
      |G0 μ θ u (((j + 1 : ℤ) : ℝ) / norming (etaLaw μ) θ n) - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| := abs_sub_le _ _ _
    _ ≤ η / 2 + η / 2 := add_le_add hmain hd
    _ = η := by ring

private theorem step_norming_pos : ∀ᶠ n : ℕ in atTop, 0 < norming (stepLaw μ) θ n := by
  obtain ⟨b, hb⟩ := hDA
  obtain ⟨N, hN⟩ := (locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩).pos
  exact eventually_atTop.mpr ⟨N, hN⟩


private theorem chiError_tendsto {α ε : ℝ} (hα : 0 < α) (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) (u : ℝ) :
    Tendsto (fun n : ℕ => chiError μ θ α ε n u) atTop (𝓝 0) := by
  have h0 := hc.apply_zero_ne_zero hne
  have h1 := NormRatios.mu0_ne_one hc hne
  obtain ⟨Cb, Nb, hb⟩ := Technique.bN_bounded hc hne hap hDA hnl hε0 hε1
  rw [Metric.tendsto_atTop]
  intro η hη
  let δa : ℝ := η / (4 * (|Cb| + 1))
  let δb : ℝ := η / (4 * (|F0 (μ 0).toReal u| + 1))
  have hδa : 0 < δa := by dsimp [δa]; positivity
  have hδb : 0 < δb := by dsimp [δb]; positivity
  obtain ⟨Na, ha⟩ := Metric.tendsto_atTop.mp (Technique.aN_tendsto h0 h1 u) δa hδa
  obtain ⟨Nbn, hbn⟩ := bN_shift_tendsto hc hne hap hDA hnl u hα hδb
  have hwindow : ∀ᶠ n : ℕ in atTop, |u| ≤ ε * Real.sqrt n :=
    (Filter.Tendsto.const_mul_atTop hε0 (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)).eventually
      (eventually_ge_atTop |u|)
  obtain ⟨Nw, hw⟩ := eventually_atTop.mp hwindow
  obtain ⟨Np, hp⟩ := eventually_atTop.mp (step_norming_pos hc hne hap hDA hnl)
  refine ⟨max Na (max Nbn (max Nb (max Nw Np))), fun n hn => ?_⟩
  have hna : Na ≤ n := by omega
  have hnbn : Nbn ≤ n := by omega
  have hnb : Nb ≤ n := by omega
  have hnw : Nw ≤ n := by omega
  have hnp : Np ≤ n := by omega
  have hu := hw n hnw
  have hwin : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n) := abs_le.mp hu
  have hαB : 0 ≤ α * normB μ θ n := by rw [normB_natCast]; exact mul_nonneg hα.le (hp n hnp).le
  let f : ℤ → ℝ := fun j => |aWindow μ ε n u * bN μ θ n u (j + 1) -
    F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)|
  have hf : ∀ j ∈ signedRange μ θ α n, 0 ≤ f j ∧ f j ≤ η / 2 := by
    intro j hj
    have hja := signedRange_bound hαB hj
    have haclose : |aN μ n u - F0 (μ 0).toReal u| ≤ δa := by
      simpa only [Real.dist_eq] using (ha n hna).le
    have hbclose : |bN μ θ n u (j + 1) - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ δb := by
      exact hbn n hnbn j hja
    have hbbound : |bN μ θ n u (j + 1)| ≤ |Cb| := (hb n hnb u hu (j + 1)).trans (le_abs_self Cb)
    refine ⟨abs_nonneg _, ?_⟩
    dsimp only [f]
    rw [aWindow, Set.indicator_of_mem hwin]
    calc
      _ = |(aN μ n u - F0 (μ 0).toReal u) * bN μ θ n u (j + 1) +
        F0 (μ 0).toReal u * (bN μ θ n u (j + 1) - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n))| := by congr 1; ring
      _ ≤ |(aN μ n u - F0 (μ 0).toReal u) * bN μ θ n u (j + 1)| +
        |F0 (μ 0).toReal u * (bN μ θ n u (j + 1) - G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n))| := abs_add_le _ _
      _ ≤ δa * |Cb| + |F0 (μ 0).toReal u| * δb := by
        rw [abs_mul, abs_mul]
        exact add_le_add (mul_le_mul haclose hbbound (abs_nonneg _) hδa.le)
          (mul_le_mul_of_nonneg_left hbclose (abs_nonneg _))
      _ ≤ δa * (|Cb| + 1) + (|F0 (μ 0).toReal u| + 1) * δb := by nlinarith [hδa.le, hδb.le]
      _ = η / 2 := by dsimp [δa, δb]; field_simp; ring
  have hs := supZ_bounds (by positivity : 0 ≤ η / 2) hf
  change dist (supZ (signedRange μ θ α n) f) 0 < η
  rw [Real.dist_eq, sub_zero, abs_of_nonneg hs.1]
  exact lt_of_le_of_lt hs.2.1 (by linarith)

private theorem chiError_domination {α ε : ℝ} (_hα : 0 < α) (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    ∃ g : ℝ → ℝ, Integrable g ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ u : ℝ,
      0 ≤ chiError μ θ α ε n u ∧ chiError μ θ α ε n u ≤ g u ∧
      ∀ j ∈ signedRange μ θ α n,
        |aWindow μ ε n u * bN μ θ n u (j + 1) -
          F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ chiError μ θ α ε n u := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hcC : 0 < cC μ := div_pos hm (by linarith)
  let L : ℝ := cC μ ^ (1 / θ)
  have hL : 0 < L := Real.rpow_pos_of_pos hcC _
  obtain ⟨Ca, Na, ha⟩ := Technique.aN_majorant (hc.apply_zero_ne_zero hne) (NormRatios.mu0_ne_one hc hne) hε0 hε1
  obtain ⟨Cb, Nb, hb⟩ := Technique.bN_bounded hc hne hap hDA hnl hε0 hε1
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  let g : ℝ → ℝ := fun u => |Ca| * |Cb| / max 1 (u ^ 2) + (L * M) * |F0 (μ 0).toReal u|
  have hgi : Integrable g := by
    have hh := (window_weight_integrable.const_mul (|Ca| * |Cb|)).add
      ((F0_integrable hm hm1).abs.const_mul (L * M))
    convert hh using 1
    ext u
    simp only [g, Pi.add_apply, div_eq_mul_inv, one_mul]
  refine ⟨g, hgi, max Na Nb, fun n hn u => ?_⟩
  have hna : Na ≤ n := by omega
  have hnb : Nb ≤ n := by omega
  have hg0 : 0 ≤ g u := by dsimp [g]; positivity
  have hf (j : ℤ) : 0 ≤ |aWindow μ ε n u * bN μ θ n u (j + 1) -
      F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ∧
      |aWindow μ ε n u * bN μ θ n u (j + 1) -
      F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ g u := by
    refine ⟨abs_nonneg _, ?_⟩
    have hprod : |aWindow μ ε n u * bN μ θ n u (j + 1)| ≤ |Ca| * |Cb| / max 1 (u ^ 2) := by
      by_cases hwin : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
      · have hu : |u| ≤ ε * Real.sqrt n := abs_le.mpr hwin
        have hCa : aN μ n u ≤ |Ca| / max 1 (u ^ 2) :=
          (ha n hna u hu).trans (div_le_div_of_nonneg_right (le_abs_self Ca) (by positivity))
        have hCb : |bN μ θ n u (j + 1)| ≤ |Cb| := (hb n hnb u hu (j + 1)).trans (le_abs_self Cb)
        rw [aWindow, Set.indicator_of_mem hwin, abs_mul, abs_of_nonneg (aN_nonneg μ n u)]
        calc
          _ ≤ (|Ca| / max 1 (u ^ 2)) * |Cb| := mul_le_mul hCa hCb (abs_nonneg _) (by positivity)
          _ = |Ca| * |Cb| / max 1 (u ^ 2) := by ring
      · rw [aWindow, Set.indicator_of_notMem hwin, zero_mul, abs_zero]
        positivity
    have hG : |G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ L * M := by
      change |L * Scalar.stableDensity θ _| ≤ L * M
      rw [abs_mul, abs_of_pos hL]
      exact mul_le_mul_of_nonneg_left (hbound _) hL.le
    have hh := abs_sub_le (aWindow μ ε n u * bN μ θ n u (j + 1)) 0
      (F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n))
    simp only [sub_zero, zero_sub, abs_neg] at hh
    calc
      _ ≤ |aWindow μ ε n u * bN μ θ n u (j + 1)| +
        |F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| := hh
      _ ≤ |Ca| * |Cb| / max 1 (u ^ 2) + |F0 (μ 0).toReal u| * (L * M) := by
        rw [abs_mul (F0 _ u)]
        exact add_le_add hprod (mul_le_mul_of_nonneg_left hG (abs_nonneg _))
      _ = g u := by dsimp [g]; ring
  exact supZ_bounds hg0 (fun j _ => hf j)

private theorem chiError_integral {α ε : ℝ} (hα : 0 < α) (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    Tendsto (fun n : ℕ => ∫ u, chiError μ θ α ε n u) atTop (𝓝 0) ∧
      ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Integrable (chiError μ θ α ε n) ∧
        ∀ u : ℝ, 0 ≤ chiError μ θ α ε n u ∧
          ∀ j ∈ signedRange μ θ α n,
            |aWindow μ ε n u * bN μ θ n u (j + 1) -
              F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ chiError μ θ α ε n u := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  obtain ⟨g, hgi, N, hbnd⟩ := chiError_domination hc hne hap hDA hnl hα hε0 hε1
  have hmeas n := (chiError_measurable hb.alpha_mem α ε n (μ := μ)).aestronglyMeasurable (μ := volume)
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ᵐ u : ℝ, ‖chiError μ θ α ε n u‖ ≤ g u := by
    filter_upwards [eventually_ge_atTop N] with n hn
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hbnd n hn u).1]
      exact (hbnd n hn u).2.1
  have ht := tendsto_integral_filter_of_dominated_convergence g (Eventually.of_forall hmeas)
    hbound hgi (Eventually.of_forall (fun u => chiError_tendsto hc hne hap hDA hnl hα hε0 hε1 u))
  refine ⟨by simpa only [integral_zero] using ht, N, fun n hn => ?_⟩
  refine ⟨hgi.mono' (hmeas n) (Eventually.of_forall fun u => ?_), fun u => ?_⟩
  · rw [Real.norm_eq_abs, abs_of_nonneg (hbnd n hn u).1]
    exact (hbnd n hn u).2.1
  · exact ⟨(hbnd n hn u).1, (hbnd n hn u).2.2⟩


private theorem G0_product_integrable (x : ℝ) :
    Integrable (fun u : ℝ => F0 (μ 0).toReal u * G0 μ θ u x) := by
  obtain ⟨b, hb⟩ := hDA
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hL : 0 ≤ cC μ ^ (1 / θ) := Real.rpow_nonneg (div_nonneg hm.le (by linarith)) _
  obtain ⟨M, hM, hbound⟩ := Scalar.exists_stableDensity_le (α := θ)
  apply (((F0_integrable hm hm1).abs).mul_const (cC μ ^ (1 / θ) * M)).mono'
    (((by unfold F0; fun_prop : Continuous (F0 (μ 0).toReal)).mul (G0_continuous (μ := μ) hb.alpha_mem x)).aestronglyMeasurable)
  exact Eventually.of_forall fun u => by
    simp only [Pi.mul_apply, Real.norm_eq_abs, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    change |cC μ ^ (1 / θ) * Scalar.stableDensity θ _| ≤ cC μ ^ (1 / θ) * M
    rw [abs_mul, abs_of_nonneg hL]
    exact mul_le_mul_of_nonneg_left (hbound _) hL

private theorem chi_integral_limit {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |(μ 0).toReal * (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
            aN μ n u * bN μ θ n u (j + 1)) -
        (μ 0).toReal * ∫ u : ℝ, F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)| ≤ ε' := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  obtain ⟨ht, N, hN⟩ := chiError_integral hc hne hap hDA hnl hα hε0 hε1
  have hlim : Tendsto (fun n : ℕ => (μ 0).toReal * ∫ u, chiError μ θ α ε n u) atTop (𝓝 0) := by
    simpa using ht.const_mul (μ 0).toReal
  obtain ⟨N', hN'⟩ := Metric.tendsto_atTop.mp hlim ε' hε'
  refine ⟨max N N', fun n hn j hjup => ?_⟩
  have hnN : N ≤ n := by omega
  have hnN' : N' ≤ n := by omega
  have hjS : j ∈ signedRange μ θ α n := signedRange_mem hjup
  let D : ℝ → ℝ := fun u => aWindow μ ε n u * bN μ θ n u (j + 1) -
      F0 (μ 0).toReal u * G0 μ θ u ((j : ℝ) / norming (etaLaw μ) θ n)
  have hdmeas : Measurable D := by
    have ha := (aN_measurable μ n).indicator (s := Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)) measurableSet_Icc
    simpa only [D, aWindow, Pi.mul_def, Pi.sub_def] using (ha.mul (bN_measurable μ θ n (j + 1))).sub
      ((by unfold F0; fun_prop : Continuous (F0 (μ 0).toReal)).measurable.mul
        (G0_continuous (μ := μ) hb.alpha_mem ((j : ℝ) / norming (etaLaw μ) θ n)).measurable)
  have hDi : Integrable D := (hN n hnN).1.mono' hdmeas.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact (hN n hnN).2 u |>.2 j hjS)
  have hFG := G0_product_integrable hc hne hap hDA hnl ((j : ℝ) / norming (etaLaw μ) θ n)
  have hprod : Integrable (fun u => aWindow μ ε n u * bN μ θ n u (j + 1)) := by
    convert hDi.add hFG using 1
    ext u
    dsimp [D]
    ring
  have heq : (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u (j + 1)) =
      ∫ u, aWindow μ ε n u * bN μ θ n u (j + 1) := by
    rw [intervalIntegral.integral_of_le (by nlinarith [mul_nonneg hε0.le (Real.sqrt_nonneg (n : ℝ))]),
      ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
      · simp only [aWindow, Set.indicator_of_mem hu]
      · simp only [aWindow, Set.indicator_of_notMem hu, zero_mul]
  rw [heq, ← mul_sub, ← integral_sub hprod hFG, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  calc
    _ ≤ (μ 0).toReal * (∫ u, chiError μ θ α ε n u) := by
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      apply (abs_integral_le_integral_abs (f := D)).trans
      exact integral_mono hDi.abs (hN n hnN).1 fun u => (hN n hnN).2 u |>.2 j hjS
    _ ≤ ε' := by
      have hh := (hN' n hnN').le
      rw [Real.dist_eq, sub_zero] at hh
      exact (le_abs_self _).trans hh

private noncomputable def timeError (μ : PMF ℕ) (ε : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  (Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)).indicator
    (fun u => |(n : ℝ) / (rN μ n u : ℝ) - (μ 0).toReal| / max 1 (u ^ 2)) u

private theorem timeError_integral {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    Tendsto (fun n : ℕ => ∫ u, timeError μ ε n u) atTop (𝓝 0) ∧
      ∀ n : ℕ, 1 ≤ n → Integrable (timeError μ ε n) ∧ ∀ u, 0 ≤ timeError μ ε n u := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hmeas n : Measurable (timeError μ ε n) := by
    have hr : Measurable (fun u : ℝ => (rN μ n u : ℝ)) :=
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (Nat.measurable_floor.comp (measurable_const.add (measurable_id.mul_const _)))
    unfold timeError
    apply Measurable.indicator _ measurableSet_Icc
    have hratio : Measurable (fun u : ℝ => (n : ℝ) / (rN μ n u : ℝ) - (μ 0).toReal) := by
      simpa only [Pi.div_def, Pi.sub_def] using (measurable_const.div hr).sub measurable_const
    have hden : Measurable (fun u : ℝ => max 1 (u ^ 2)) := by fun_prop
    simpa only [Pi.div_def, Real.norm_eq_abs] using hratio.norm.div hden
  have hb n (hn : 1 ≤ n) u : 0 ≤ timeError μ ε n u ∧ timeError μ ε n u ≤ 2 / max 1 (u ^ 2) := by
    by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
    · obtain ⟨hnr, -, -⟩ := rN_window_bounds hm hm1 hε0 hε1 hn (abs_le.mpr hu)
      have hr : (0 : ℝ) < rN μ n u := by exact_mod_cast (show 0 < rN μ n u by omega)
      have hfrac : (n : ℝ) / (rN μ n u : ℝ) ≤ 1 := (div_le_one hr).mpr (by exact_mod_cast hnr)
      have hnfrac : 0 ≤ (n : ℝ) / (rN μ n u : ℝ) := by positivity
      rw [timeError, Set.indicator_of_mem hu]
      refine ⟨by positivity, div_le_div_of_nonneg_right ?_ (by positivity)⟩
      rw [abs_le]
      constructor <;> linarith
    · rw [timeError, Set.indicator_of_notMem hu]
      exact ⟨le_rfl, by positivity⟩
  have hdom : Integrable (fun u : ℝ => 2 / max 1 (u ^ 2)) := by
    convert window_weight_integrable.const_mul 2 using 1
    ext u
    ring
  have hi n hn : Integrable (timeError μ ε n) := hdom.mono' (hmeas n).aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs, abs_of_nonneg (hb n hn u).1]; exact (hb n hn u).2)
  have ht u : Tendsto (fun n : ℕ => timeError μ ε n u) atTop (𝓝 0) := by
    have hr : Tendsto (fun n : ℕ => (n : ℝ) / (rN μ n u : ℝ)) atTop (𝓝 (μ 0).toReal) := by
      have hh := (rN_ratio hm u).inv₀ (one_div_pos.mpr hm).ne'
      simpa only [inv_div, div_one] using hh
    have hraw : Tendsto (fun n : ℕ => |(n : ℝ) / (rN μ n u : ℝ) - (μ 0).toReal| / max 1 (u ^ 2)) atTop (𝓝 0) := by
      simpa using ((hr.sub_const (μ 0).toReal).abs.div_const (max 1 (u ^ 2)))
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hraw
    · exact (eventually_ge_atTop 1).mono fun n hn => (hb n hn u).1
    · exact Eventually.of_forall fun n => by
        unfold timeError
        by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
        · rw [Set.indicator_of_mem hu]
        · rw [Set.indicator_of_notMem hu]; positivity
  have hdct := tendsto_integral_filter_of_dominated_convergence (fun u : ℝ => 2 / max 1 (u ^ 2))
    (Eventually.of_forall fun n => (hmeas n).aestronglyMeasurable)
    ((eventually_ge_atTop 1).mono fun n hn => Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hb n hn u).1]; exact (hb n hn u).2)
    hdom (Eventually.of_forall ht)
  exact ⟨by simpa only [integral_zero] using hdct, fun n hn => ⟨hi n hn, fun u => (hb n hn u).1⟩⟩


private theorem time_factor_limit {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ,
      |(∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
          (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u (j + 1)) -
        (μ 0).toReal * ∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
          aN μ n u * bN μ θ n u (j + 1)| ≤ η := by
  obtain ⟨Ca, Na, ha⟩ := Technique.aN_majorant (hc.apply_zero_ne_zero hne) (NormRatios.mu0_ne_one hc hne) hε0 hε1
  obtain ⟨Cb, Nb, hb⟩ := Technique.bN_bounded hc hne hap hDA hnl hε0 hε1
  obtain ⟨ht, hi⟩ := timeError_integral hc hne hap hDA hnl hε0 hε1
  let C : ℝ := |Ca| * |Cb|
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hlim : Tendsto (fun n : ℕ => C * ∫ u, timeError μ ε n u) atTop (𝓝 0) := by simpa using ht.const_mul C
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hlim.eventually (eventually_lt_nhds hη))
  refine ⟨max 1 (max N (max Na Nb)), fun n hn j => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnN : N ≤ n := by omega
  have hnNa : Na ≤ n := by omega
  have hnNb : Nb ≤ n := by omega
  let P : ℝ → ℝ := fun u => aWindow μ ε n u * bN μ θ n u (j + 1)
  let D : ℝ → ℝ := fun u => ((n : ℝ) / (rN μ n u : ℝ) - (μ 0).toReal) * P u
  have hPmeas : Measurable P := by
    simpa only [P, aWindow, Pi.mul_def] using
      ((aN_measurable μ n).indicator (s := Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)) measurableSet_Icc).mul (bN_measurable μ θ n (j + 1))
  have hDmeas : Measurable D := by
    have hr : Measurable (fun u : ℝ => (rN μ n u : ℝ)) :=
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp (Nat.measurable_floor.comp (measurable_const.add (measurable_id.mul_const _)))
    simpa only [D, Pi.mul_def, Pi.sub_def, Pi.div_def] using
      ((measurable_const.div hr).sub measurable_const).mul hPmeas
  have hPb u : |P u| ≤ C / max 1 (u ^ 2) := by
    by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
    · have hau := ha n hnNa u (abs_le.mpr hu)
      have hbu := hb n hnNb u (abs_le.mpr hu) (j + 1)
      dsimp only [P]
      rw [aWindow, Set.indicator_of_mem hu, abs_mul, abs_of_nonneg (aN_nonneg μ n u)]
      calc
        _ ≤ (|Ca| / max 1 (u ^ 2)) * |Cb| := mul_le_mul
          (hau.trans (div_le_div_of_nonneg_right (le_abs_self Ca) (by positivity)))
          (hbu.trans (le_abs_self Cb)) (abs_nonneg _) (by positivity)
        _ = _ := by dsimp [C]; ring
    · simp only [P, aWindow, Set.indicator_of_notMem hu, zero_mul, abs_zero]
      positivity
  have hDb u : |D u| ≤ C * timeError μ ε n u := by
    by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
    · dsimp only [D]
      rw [abs_mul, timeError, Set.indicator_of_mem hu]
      calc
        _ ≤ |(n : ℝ) / (rN μ n u : ℝ) - (μ 0).toReal| * (C / max 1 (u ^ 2)) := mul_le_mul_of_nonneg_left (hPb u) (abs_nonneg _)
        _ = _ := by ring
    · simp only [D, P, aWindow, timeError, Set.indicator_of_notMem hu, zero_mul, mul_zero, abs_zero]
      rfl
  have hPi : Integrable P := by
    apply (window_weight_integrable.const_mul C).mono' hPmeas.aestronglyMeasurable
    exact Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]
      simpa only [one_div, one_mul, div_eq_mul_inv] using hPb u
  have hDi : Integrable D := ((hi n hn1).1.const_mul C).mono' hDmeas.aestronglyMeasurable
    (Eventually.of_forall fun u => by rw [Real.norm_eq_abs]; exact hDb u)
  have hTPi : Integrable (fun u => (n : ℝ) / (rN μ n u : ℝ) * P u) := by
    convert hDi.add (hPi.const_mul (μ 0).toReal) using 1
    ext u
    dsimp [D]
    ring
  have hI (f : ℝ → ℝ) : (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), f u * aN μ n u * bN μ θ n u (j + 1)) = ∫ u, f u * P u := by
    rw [intervalIntegral.integral_of_le (by nlinarith [mul_nonneg hε0.le (Real.sqrt_nonneg (n : ℝ))]),
      ← integral_Icc_eq_integral_Ioc, ← integral_indicator measurableSet_Icc]
    apply integral_congr_ae
    exact Eventually.of_forall fun u => by
      by_cases hu : u ∈ Set.Icc (-(ε * Real.sqrt n)) (ε * Real.sqrt n)
      · simp only [P, aWindow, Set.indicator_of_mem hu, mul_assoc]
      · simp only [P, aWindow, Set.indicator_of_notMem hu, zero_mul, mul_zero]
  have hIP : (∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n), aN μ n u * bN μ θ n u (j + 1)) = ∫ u, P u := by
    simpa only [one_mul] using hI (fun _ => 1)
  have heq : (∫ u, (n : ℝ) / (rN μ n u : ℝ) * P u) - (μ 0).toReal * ∫ u, P u = ∫ u, D u := by
    rw [← integral_const_mul, ← integral_sub hTPi (hPi.const_mul (μ 0).toReal)]
    congr 1
    ext u
    dsimp [D]
    ring
  rw [hI, hIP, heq]
  calc
    _ ≤ C * ∫ u, timeError μ ε n u := by
      rw [← integral_const_mul]
      exact (abs_integral_le_integral_abs (f := D)).trans
        (integral_mono hDi.abs ((hi n hn1).1.const_mul C) hDb)
    _ ≤ η := (hN n hnN).le

private theorem time_kernel_interval {ε : ℝ} (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ,
      IntervalIntegrable (fun u => (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u (j + 1))
        volume (-(ε * Real.sqrt n)) (ε * Real.sqrt n) := by
  obtain ⟨Ca, Na, ha⟩ := Technique.aN_majorant (hc.apply_zero_ne_zero hne) (NormRatios.mu0_ne_one hc hne) hε0 hε1
  obtain ⟨Cb, Nb, hb⟩ := Technique.bN_bounded hc hne hap hDA hnl hε0 hε1
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  refine ⟨max 1 (max Na Nb), fun n hn j => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnNa : Na ≤ n := by omega
  have hnNb : Nb ≤ n := by omega
  have hmeas : Measurable (fun u => (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u (j + 1)) := by
    have hr : Measurable (fun u : ℝ => (rN μ n u : ℝ)) :=
      (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
        (Nat.measurable_floor.comp (measurable_const.add (measurable_id.mul_const _)))
    simpa only [Pi.mul_def, Pi.div_def] using ((measurable_const.div hr).mul (aN_measurable μ n)).mul (bN_measurable μ θ n (j + 1))
  apply (intervalIntegrable_iff_integrableOn_Icc_of_le (by nlinarith [mul_nonneg hε0.le (Real.sqrt_nonneg (n : ℝ))])).mpr
  apply Measure.integrableOn_of_bounded (by simp) hmeas.aestronglyMeasurable (M := |Ca| * |Cb|)
  apply ae_restrict_of_forall_mem measurableSet_Icc
  intro u hu
  have huu := abs_le.mpr hu
  have hnr := (rN_window_bounds hm hm1 hε0 hε1 hn1 huu).1
  have hrpos : (0 : ℝ) < rN μ n u := by exact_mod_cast (show 0 < rN μ n u by omega)
  have hfrac : (n : ℝ) / (rN μ n u : ℝ) ≤ 1 := (div_le_one hrpos).mpr (by exact_mod_cast hnr)
  have hannon : 0 ≤ aN μ n u := aN_nonneg μ n u
  have han : aN μ n u ≤ |Ca| := by
    calc _ ≤ Ca / max 1 (u ^ 2) := ha n hnNa u huu
      _ ≤ |Ca| / max 1 (u ^ 2) := div_le_div_of_nonneg_right (le_abs_self Ca) (by positivity)
      _ ≤ |Ca| := div_le_self (abs_nonneg _) (le_max_left _ _)
  have hbn : |bN μ θ n u (j + 1)| ≤ |Cb| := (hb n hnNb u huu (j + 1)).trans (le_abs_self Cb)
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) / (rN μ n u : ℝ)), abs_of_nonneg hannon]
  calc _ ≤ (1 * |Ca|) * |Cb| := mul_le_mul (mul_le_mul hfrac han hannon (by norm_num)) hbn (abs_nonneg _) (by positivity)
    _ = _ := by ring

private theorem step_bp_ratio : ∃ R : ℝ,
    Tendsto (fun n : ℕ => norming (stepLaw μ) θ n / norming (etaLaw μ) θ n) atTop (𝓝 R) := by
  by_cases hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)
  · let sp := Real.sqrt (StableAnalysis.variance (etaLaw μ))
    have hS := NormRatios.hS_of_nonLattice hc hne hnl
    have hsp : 0 < sp := Real.sqrt_pos.mpr (LeafMass.YLaw.variance_etaLaw_pos hc hne hS
      (integrable_sq_etaLaw hc hne hfin))
    refine ⟨Real.sqrt (StableAnalysis.variance (stepLaw μ)) / sp, ?_⟩
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hs : Real.sqrt ((n : ℝ) / 2) ≠ 0 := (Real.sqrt_pos.mpr (by positivity)).ne'
    rw [norming_of_integrable_sq hfin, norming_etaLaw_finiteVariance hc hne hfin]
    dsimp only [sp]
    field_simp
  · refine ⟨((1 - (μ 0).toReal) ^ (-(1 / θ)))⁻¹, ?_⟩
    have hh := (lem_hhp hc hne hap hDA hfin).inv₀
      (Real.rpow_pos_of_pos (EtaTransfer.one_sub_apply_zero_pos hc hne) _).ne'
    simpa only [inv_div] using hh


private theorem normBp_eventually_pos : ∀ᶠ n : ℕ in atTop, 0 < norming (etaLaw μ) θ n := by
  let := EtaTransfer.isProbabilityMeasure_etaLaw hc hne
  have ha := (etaLaw_norming hc hne (NormRatios.hS_of_nonLattice hc hne hnl) hDA).1
  exact (TransformConvergence.tendsto_atTop (etaLaw μ) ha).eventually (eventually_gt_atTop 0)

private theorem density_norm_compare {r : ℝ} (hr : 0 < r)
    (ht : Tendsto (fun n : ℕ => norming (etaLaw μ) θ n /
        normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 r))
    {α : ℝ} (hα : 0 < α) {η : ℝ} (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |r * Scalar.stableDensity θ (-(r * ((j : ℝ) / norming (etaLaw μ) θ n))) -
        r * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ η := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  obtain ⟨R, hR⟩ := step_bp_ratio hc hne hap hDA hnl
  obtain ⟨K, hLip⟩ : ∃ K : ℝ≥0, LipschitzWith K (Scalar.stableDensity θ) :=
    ⟨_, Scalar.lipschitzWith_stableDensity hb.alpha_mem⟩
  let A : ℝ := α * (|R| + 1)
  have hA : 0 < A := by dsimp [A]; positivity
  have hnorm : ∀ᶠ n : ℕ in atTop, normB μ θ n / norming (etaLaw μ) θ n ≤ |R| + 1 := by
    filter_upwards [hR.eventually (Metric.ball_mem_nhds R zero_lt_one)] with n hn
    rw [Real.dist_eq] at hn
    have := le_abs_self (norming (stepLaw μ) θ n / norming (etaLaw μ) θ n - R)
    rw [normB_natCast]
    linarith [le_abs_self R]
  have hsmall : Tendsto (fun n : ℕ => (r * (K : ℝ) * A) *
      |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)|) atTop (𝓝 0) := by
    simpa using ((((tendsto_const_nhds : Tendsto (fun _ : ℕ => r) atTop (𝓝 r)).sub ht).abs).const_mul (r * (K : ℝ) * A))
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    ((hsmall.eventually (eventually_lt_nhds hη)).and (hnorm.and (normBp_eventually_pos hc hne hap hDA hnl)))
  refine ⟨N, fun n hn j hj => ?_⟩
  obtain ⟨hs, hnb, hpos⟩ := hN n hn
  have hjA : |(j : ℝ) / norming (etaLaw μ) θ n| ≤ A := by
    rw [abs_div, abs_of_pos hpos]
    calc _ ≤ α * normB μ θ n / norming (etaLaw μ) θ n := div_le_div_of_nonneg_right hj hpos.le
      _ = α * (normB μ θ n / norming (etaLaw μ) θ n) := by ring
      _ ≤ A := mul_le_mul_of_nonneg_left hnb hα.le
  have heq : -(r * ((j : ℝ) / norming (etaLaw μ) θ n)) -
      (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))) =
      -((j : ℝ) / norming (etaLaw μ) θ n) *
        (r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) := by
    field_simp [hpos.ne']
    ring
  have hd := hLip.dist_le_mul (-(r * ((j : ℝ) / norming (etaLaw μ) θ n)))
    (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))
  rw [Real.dist_eq, Real.dist_eq, heq, abs_mul, abs_neg] at hd
  rw [← mul_sub, abs_mul, abs_of_pos hr]
  calc
    _ ≤ r * ((K : ℝ) * (|(j : ℝ) / norming (etaLaw μ) θ n| *
      |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)|)) := mul_le_mul_of_nonneg_left hd hr.le
    _ ≤ (r * (K : ℝ) * A) * |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)| := by
      calc
        _ ≤ r * ((K : ℝ) * (A * |r - norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)|)) := by
          apply mul_le_mul_of_nonneg_left _ hr.le
          apply mul_le_mul_of_nonneg_left _ K.coe_nonneg
          exact mul_le_mul_of_nonneg_right hjA (abs_nonneg _)
        _ = _ := by ring
    _ ≤ η := hs.le

private theorem F0_mass {m : ℝ} (hm : 0 < m) (hm1 : m < 1) : m * ∫ u : ℝ, F0 m u = 1 := by
  have hq : 0 < 1 - m := by linarith
  have heq : F0 m = fun u : ℝ => Real.exp (-(m ^ 2 / (2 * (1 - m))) * u ^ 2) /
      Real.sqrt (2 * Real.pi * (1 - m)) := by
    ext u
    unfold F0
    congr 2
    ring
  rw [heq, integral_div, integral_gaussian]
  have ht : 0 ≤ Real.sqrt (Real.pi / (m ^ 2 / (2 * (1 - m)))) := Real.sqrt_nonneg _
  have hd : 0 < Real.sqrt (2 * Real.pi * (1 - m)) := by positivity
  have ht2 := Real.sq_sqrt (by positivity : 0 ≤ Real.pi / (m ^ 2 / (2 * (1 - m))))
  have hd2 := Real.sq_sqrt (by positivity : 0 ≤ 2 * Real.pi * (1 - m))
  have hid : m ^ 2 * (Real.pi / (m ^ 2 / (2 * (1 - m)))) = 2 * Real.pi * (1 - m) := by field_simp
  have hprod : m * Real.sqrt (Real.pi / (m ^ 2 / (2 * (1 - m)))) = Real.sqrt (2 * Real.pi * (1 - m)) := by
    apply (sq_eq_sq₀ (mul_nonneg hm.le ht) hd.le).mp
    rw [mul_pow, ht2, hd2, hid]
  rw [← mul_div_assoc, hprod, div_self hd.ne']


private theorem G0_finite (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    (hθ : θ = 2) (u x : ℝ) :
    G0 μ θ u x = G0fv (μ 0).toReal (Real.sqrt (variance (etaLaw μ))) x u := by
  have hle : (μ 0).toReal ≤ 1 := by
    have := ENNReal.toReal_mono ENNReal.one_ne_top (PMF.coe_le_one μ 0)
    simpa using this
  have hc0 : 0 ≤ cC μ := div_nonneg ENNReal.toReal_nonneg (sub_nonneg.2 hle)
  subst hθ
  unfold G0 finVarShift G0fv
  simp only [hfin, ite_true]
  rw [stableDensity_two]
  have hs : cC μ ^ (1 / 2 : ℝ) = Real.sqrt (cC μ) := by rw [Real.sqrt_eq_rpow]
  have h32 : cC μ ^ (3 / 2 : ℝ) = cC μ * Real.sqrt (cC μ) := by
    rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add' hc0 (by norm_num), Real.rpow_one, hs]
  rw [hs, h32]
  unfold cC
  rfl


private theorem norming_eta_small : ∀ᶠ n : ℕ in atTop, norming (etaLaw μ) θ n ≤ n := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hDA' : ∃ b, IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b :=
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  have hat := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA'
  have hmono := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA').1
  rw [mean_stepLaw hc] at hat
  obtain ⟨a, heq, h⟩ := hat.exists_stableDomain hc hne hmono
  have ha0 := (Scalar.regularlyVaryingSeq h).tendsto_div_self h.monotone h.pos
    (by have := h.alpha_mem.1; positivity : 0 ≤ 1 / θ)
    ((div_lt_one (by linarith [h.alpha_mem.1] : 0 < θ)).mpr h.alpha_mem.1)
  have hstep : Tendsto (fun n : ℕ => normB μ θ n / n) atTop (𝓝 0) := by
    simp only [normB_natCast]
    exact ha0.congr' (heq.mono fun n hn => by rw [hn])
  have hraw : Tendsto (fun n : ℕ => ((n : ℝ) / (μ 0).toReal) / n) atTop (𝓝 (1 / (μ 0).toReal)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp
  have htar := NormRatios.normB_ratio_tendsto hc hne hap hDA (one_div_pos.mpr hm) hraw
  have htarpos : ∀ᶠ n : ℕ in atTop, 0 < normB μ θ ((n : ℝ) / (μ 0).toReal) := by
    filter_upwards [htar.eventually (Ioi_mem_nhds (Real.rpow_pos_of_pos (one_div_pos.mpr hm) (1 / θ))),
      step_norming_pos hc hne hap hDA hnl] with n hn hBn
    rw [normB_natCast, lt_div_iff₀ hBn, zero_mul] at hn
    exact hn
  have htar0 : Tendsto (fun n : ℕ => normB μ θ ((n : ℝ) / (μ 0).toReal) / n) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (normB μ θ ((n : ℝ) / (μ 0).toReal) / normB μ θ n) * (normB μ θ n / n)) atTop (𝓝 0) := by
      simpa only [mul_zero] using htar.mul hstep
    apply hh.congr'
    filter_upwards [step_norming_pos hc hne hap hDA hnl] with n hn
    rw [normB_natCast]
    field_simp
  obtain ⟨R, hR⟩ : ∃ R : ℝ, Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 R) := by
    by_cases hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)
    · exact ⟨_, NormRatios.normBp_div_normB_finVar hc hne hap hDA hfin⟩
    · exact ⟨_, NormRatios.normBp_div_normB_infVar hc hne hap hDA hfin⟩
  have hzero : Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / n) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => (norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) *
        (normB μ θ ((n : ℝ) / (μ 0).toReal) / n)) atTop (𝓝 0) := by simpa only [mul_zero] using hR.mul htar0
    apply hh.congr'
    filter_upwards [htarpos] with n hn
    field_simp
  filter_upwards [hzero.eventually (eventually_lt_nhds zero_lt_one), eventually_ge_atTop 1] with n hn hn1
  exact ((div_lt_one (by exact_mod_cast hn1 : (0 : ℝ) < n)).mp hn).le

private theorem fixed_window_limit {r : ℝ} (hr : 0 < r)
    (hrat : Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 r))
    (heval : ∀ x : ℝ, (μ 0).toReal * (∫ u : ℝ, F0 (μ 0).toReal u * G0 μ θ u x) = r * Scalar.stableDensity θ (-(r * x)))
    {α ε η : ℝ} (hα : 0 < α) (hε0 : 0 < ε)
    (hε1 : ε < (1 - (μ 0).toReal) / (2 * (μ 0).toReal)) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |(∫ u in (-(ε * Real.sqrt n))..(ε * Real.sqrt n),
          (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u (j + 1)) -
        r * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ η := by
  obtain ⟨N₁, h₁⟩ := time_factor_limit hc hne hap hDA hnl hε0 hε1 (by positivity : 0 < η / 3)
  obtain ⟨N₂, h₂⟩ := chi_integral_limit hc hne hap hDA hnl hα hε0 hε1 (by positivity : 0 < η / 3)
  obtain ⟨N₃, h₃⟩ := density_norm_compare hc hne hap hDA hnl hr hrat hα (by positivity : 0 < η / 3)
  refine ⟨max N₁ (max N₂ N₃), fun n hn j hj => ?_⟩
  have h1 := h₁ n (by omega) j
  have h2 := h₂ n (by omega) j hj
  have h3 := h₃ n (by omega) j hj
  rw [heval] at h2
  rw [abs_le] at h1 h2 h3 ⊢
  constructor <;> linarith


private theorem chi_scaled_limit {r : ℝ} (hr : 0 < r)
    (hrat : Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 r))
    (heval : ∀ x : ℝ, (μ 0).toReal * (∫ u : ℝ, F0 (μ 0).toReal u * G0 μ θ u x) = r * Scalar.stableDensity θ (-(r * x)))
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |norming (etaLaw μ) θ n * (chi μ n j).toReal -
        r * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ η := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hq := EtaTransfer.one_sub_apply_zero_pos hc hne
  have hm1 : (μ 0).toReal < 1 := by linarith
  let δ : ℝ := (1 - (μ 0).toReal) / (8 * (μ 0).toReal)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hδwide : 2 * δ < (1 - (μ 0).toReal) / (2 * (μ 0).toReal) := by dsimp [δ]; field_simp; nlinarith
  have hδsmall : δ / 2 < (1 - (μ 0).toReal) / (2 * (μ 0).toReal) := by linarith
  have hδ1 : δ < 1 / (μ 0).toReal := by
    dsimp [δ]
    apply (div_lt_div_iff₀ (by positivity) hm).mpr
    nlinarith
  obtain ⟨Ns, hs⟩ := fixed_window_limit hc hne hap hDA hnl hr hrat heval hα (half_pos hδ) hδsmall (half_pos hη)
  obtain ⟨Nw, hw⟩ := fixed_window_limit hc hne hap hDA hnl hr hrat heval hα (by positivity : 0 < 2 * δ) hδwide (half_pos hη)
  obtain ⟨Ni, hi⟩ := time_kernel_interval hc hne hap hDA hnl (by positivity : 0 < 2 * δ) hδwide
  obtain ⟨C, c, hC, hcp, hb⟩ := chi_window hc hne hap hDA hnl hδ hδ1
  obtain ⟨D, hD, hpoly⟩ := LeafConcentration.OeLemmas.polyExp_absorb (by norm_num : (0 : ℝ) < 1 / 2) 1 (half_pos hcp) (half_lt_self hcp)
  have hexp : Tendsto (fun n : ℕ => (C * D) * Real.exp (-(c / 2) * (n : ℝ) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop (half_pos hcp) ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop))
    simpa only [Function.comp_apply, neg_mul, mul_zero] using hh.const_mul (C * D)
  have hgrowth : ∀ᶠ n : ℕ in atTop, 2 ≤ δ * (n : ℝ) :=
    (Filter.Tendsto.const_mul_atTop hδ tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 2)
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hexp.eventually (eventually_lt_nhds (half_pos hη))).and
    ((norming_eta_small hc hne hap hDA hnl).and ((normBp_eventually_pos hc hne hap hDA hnl).and hgrowth)))
  refine ⟨max 1 (max N (max Ns (max Nw Ni))), fun n hn j hj => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnN : N ≤ n := by omega
  have hnNs : Ns ≤ n := by omega
  have hnNw : Nw ≤ n := by omega
  have hnNi : Ni ≤ n := by omega
  obtain ⟨hex, hBpSmall, hBp, hgr⟩ := hN n hnN
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hsq := Real.sq_sqrt hnR.le
  have hsn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  let L : ℝ := (((⌈(n : ℝ) / (μ 0).toReal - δ * n⌉ : ℤ) : ℝ) - (n : ℝ) / (μ 0).toReal) / Real.sqrt n
  let U : ℝ := (((⌊(n : ℝ) / (μ 0).toReal + δ * n⌋ : ℤ) : ℝ) + 1 - (n : ℝ) / (μ 0).toReal) / Real.sqrt n
  have hL0 : -(2 * δ * Real.sqrt n) ≤ L := by
    dsimp [L]
    rw [le_div_iff₀ hsn]
    nlinarith [Int.le_ceil ((n : ℝ) / (μ 0).toReal - δ * n)]
  have hL1 : L ≤ -(δ / 2 * Real.sqrt n) := by
    dsimp [L]
    rw [div_le_iff₀ hsn]
    nlinarith [Int.ceil_lt_add_one ((n : ℝ) / (μ 0).toReal - δ * n)]
  have hU0 : δ / 2 * Real.sqrt n ≤ U := by
    dsimp [U]
    rw [le_div_iff₀ hsn]
    nlinarith [Int.lt_floor_add_one ((n : ℝ) / (μ 0).toReal + δ * n)]
  have hU1 : U ≤ 2 * δ * Real.sqrt n := by
    dsimp [U]
    rw [div_le_iff₀ hsn]
    nlinarith [Int.floor_le ((n : ℝ) / (μ 0).toReal + δ * n)]
  have hLU : L ≤ U := by nlinarith [mul_nonneg hδ.le hsn.le]
  let F : ℝ → ℝ := fun u => (n : ℝ) / (rN μ n u : ℝ) * aN μ n u * bN μ θ n u (j + 1)
  have hFn u : 0 ≤ F u := by
    have hb0 : 0 ≤ bN μ θ n u (j + 1) := mul_nonneg hBp.le measureReal_nonneg
    exact mul_nonneg (mul_nonneg (by positivity) (aN_nonneg μ n u)) hb0
  have hFi := hi n hnNi j
  have hsub : Set.uIcc L U ⊆ Set.uIcc (-(2 * δ * Real.sqrt n)) (2 * δ * Real.sqrt n) := by
    rw [Set.uIcc_of_le hLU, Set.uIcc_of_le (show -(2 * δ * Real.sqrt n) ≤ 2 * δ * Real.sqrt n by nlinarith [mul_nonneg hδ.le hsn.le])]
    exact Set.Icc_subset_Icc hL0 hU1
  have hsmallI := intervalIntegral.integral_mono_interval hL1
    (by nlinarith [mul_nonneg hδ.le hsn.le] : -(δ / 2 * Real.sqrt n) ≤ δ / 2 * Real.sqrt n) hU0
    (Eventually.of_forall hFn) (hFi.mono_set hsub)
  have hlargeI := intervalIntegral.integral_mono_interval hL0 hLU hU1 (Eventually.of_forall hFn) hFi
  have hret := chi_retenir hc hne hap hDA hnl hδ hδ1 hn1 j hBp
  have hevalret : (μ 0).toReal * (∫ u in L..U,
      Real.sqrt n * binomProb (μ 0).toReal (rN μ n u - 1) (n - 1) * bN μ θ n u (j + 1)) = ∫ u in L..U, F u := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr_Ioo_of_le hLU
    intro u hu
    have huwide : |u| ≤ 2 * δ * Real.sqrt n := abs_le.mpr ⟨hL0.trans hu.1.le, hu.2.le.trans hU1⟩
    have hnr := (rN_window_bounds hm hm1 (by positivity : 0 < 2 * δ) hδwide hn1 huwide).1
    have hrpos : (0 : ℝ) < rN μ n u := by exact_mod_cast (show 0 < rN μ n u by omega)
    change (μ 0).toReal * (Real.sqrt n * binomProb (μ 0).toReal (rN μ n u - 1) (n - 1) * bN μ θ n u (j + 1)) = F u
    rw [Technique.aTilde_eq (hc.apply_zero_ne_zero hne) (NormRatios.mu0_ne_one hc hne) hn1 u (by omega)]
    dsimp only [F]
    field_simp
  change norming (etaLaw μ) θ n * ((μ 0).toReal * ∑ k ∈ _, _) = _ at hret
  rw [hevalret] at hret
  have herr : |norming (etaLaw μ) θ n * (chi μ n j).toReal - ∫ u in L..U, F u| ≤ η / 2 := by
    rw [← hret, ← mul_sub, abs_mul, abs_of_pos hBp]
    calc
      _ ≤ norming (etaLaw μ) θ n * (C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (hb n hn1 j) hBp.le
      _ ≤ (n : ℝ) * (C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) := mul_le_mul_of_nonneg_right hBpSmall (by positivity)
      _ = C * ((n : ℝ) ^ (1 : ℝ) * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) := by rw [Real.rpow_one]; ring
      _ ≤ C * (D * Real.exp (-(c / 2) * (n : ℝ) ^ (1 / 2 : ℝ))) := mul_le_mul_of_nonneg_left (hpoly n) hC.le
      _ = _ := by ring
      _ ≤ η / 2 := hex.le
  have hs' := hs n hnNs j hj
  have hw' := hw n hnNw j hj
  rw [abs_le] at hs' hw' herr ⊢
  constructor <;> linarith

private theorem finite_kernel_eval
    (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)) :
    0 < Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) / Real.sqrt (variance (stepLaw μ)) ∧
    ∀ x : ℝ, (μ 0).toReal * (∫ u : ℝ, F0 (μ 0).toReal u * G0 μ θ u x) =
      (Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) / Real.sqrt (variance (stepLaw μ))) *
        Scalar.stableDensity θ (-((Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) / Real.sqrt (variance (stepLaw μ))) * x)) := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  have hθ : θ = 2 := DomainCriterion.index_eq_two_of_integrable_sq
    (stableDomain_isStableAttracted hb) (integrable_stepLaw hc) hfin
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hs : 0 < Real.sqrt (variance (stepLaw μ)) := Real.sqrt_pos.mpr
    (DomainCriterion.variance_pos_of_integrable_sq (stableDomain_isStableAttracted hb) (integrable_stepLaw hc) hfin)
  have hsp : 0 < Real.sqrt (variance (etaLaw μ)) := Real.sqrt_pos.mpr
    (LeafMass.YLaw.variance_etaLaw_pos hc hne (NormRatios.hS_of_nonLattice hc hne hnl) (integrable_sq_etaLaw hc hne hfin))
  have hvar : (Real.sqrt (variance (etaLaw μ))) ^ 2 =
      (Real.sqrt (variance (stepLaw μ))) ^ 2 / (1 - (μ 0).toReal) - (μ 0).toReal / (1 - (μ 0).toReal) ^ 2 := by
    rw [Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mp hsp)), Real.sq_sqrt (le_of_lt (Real.sqrt_pos.mp hs))]
    exact variance_etaLaw hc hne hfin
  refine ⟨by positivity, fun x => ?_⟩
  simp_rw [G0_finite hc hne hap hDA hnl hfin hθ]
  rw [gaussian_convolution_identity hm hm1 hs hsp hvar, hθ, stableDensity_two]
  unfold gaussDensity
  rw [neg_sq]

theorem chi_Bprime_infVar (hinf : ¬ Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {α : ℝ} (hα : 0 < α) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |norming (etaLaw μ) θ n * (chi μ n j).toReal -
        cC μ ^ (1 / θ) * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ ε' := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  have hL : 0 < cC μ ^ (1 / θ) := Real.rpow_pos_of_pos (div_pos hm (by linarith)) _
  apply chi_scaled_limit hc hne hap hDA hnl hL (NormRatios.normBp_div_normB_infVar hc hne hap hDA hinf) _ hα hε'
  intro x
  simp only [G0, finVarShift, ite_eq_right hinf, sub_zero]
  rw [integral_mul_const, ← mul_assoc, F0_mass hc hne hap hDA hnl hm hm1, one_mul]

theorem chi_Bprime_finVar_corrected (hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ))
    {α : ℝ} (hα : 0 < α) {ε' : ℝ} (hε' : 0 < ε') :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |norming (etaLaw μ) θ n * (chi μ n j).toReal -
        Real.sqrt (μ 0).toReal * Real.sqrt (variance (etaLaw μ)) / Real.sqrt (variance (stepLaw μ)) *
          Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ ε' := by
  obtain ⟨hr, heval⟩ := finite_kernel_eval hc hne hap hDA hnl hfin
  exact chi_scaled_limit hc hne hap hDA hnl hr (NormRatios.normBp_div_normB_finVar hc hne hap hDA hfin) heval hα hε'

theorem lem_technic3 {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
      |normB μ θ ((n : ℝ) / (μ 0).toReal) * (chi μ n j).toReal -
        Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ ε := by
  obtain ⟨r, hr, hratio, hmain⟩ : ∃ r : ℝ, 0 < r ∧
      Tendsto (fun n : ℕ => norming (etaLaw μ) θ n / normB μ θ ((n : ℝ) / (μ 0).toReal)) atTop (𝓝 r) ∧
      (∀ η : ℝ, 0 < η → ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℤ, |(j : ℝ)| ≤ α * normB μ θ n →
        |norming (etaLaw μ) θ n * (chi μ n j).toReal -
          r * Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))| ≤ η) := by
    by_cases hfin : Integrable (fun z : ℤ => (z : ℝ) ^ 2) (stepLaw μ)
    · exact ⟨_, (finite_kernel_eval hc hne hap hDA hnl hfin).1,
        NormRatios.normBp_div_normB_finVar hc hne hap hDA hfin,
        fun η hη => chi_Bprime_finVar_corrected hc hne hap hDA hnl hfin hα hη⟩
    · have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
      have hL : 0 < cC μ ^ (1 / θ) := Real.rpow_pos_of_pos (div_pos hm (EtaTransfer.one_sub_apply_zero_pos hc hne)) _
      exact ⟨_, hL, NormRatios.normBp_div_normB_infVar hc hne hap hDA hfin,
        fun η hη => chi_Bprime_infVar hc hne hap hDA hnl hfin hα hη⟩
  have hi : Tendsto (fun n : ℕ => normB μ θ ((n : ℝ) / (μ 0).toReal) / norming (etaLaw μ) θ n) atTop (𝓝 r⁻¹) := by
    simpa only [inv_div] using hratio.inv₀ hr.ne'
  have hir : 0 < r⁻¹ := inv_pos.mpr hr
  obtain ⟨M, hM, hMb⟩ := Scalar.exists_stableDensity_le (α := θ)
  have hsmall : Tendsto (fun n : ℕ => M * |(normB μ θ ((n : ℝ) / (μ 0).toReal) / norming (etaLaw μ) θ n) * r - 1|) atTop (𝓝 0) := by
    simpa only [inv_mul_cancel₀ hr.ne', sub_self, abs_zero, mul_zero] using ((hi.mul_const r).sub_const 1).abs.const_mul M
  let η : ℝ := ε / (2 * (r⁻¹ + 2))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨Nm, hm⟩ := hmain η hη
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hsmall.eventually (eventually_lt_nhds (half_pos hε))).and
    ((hi.eventually (Ioi_mem_nhds hir)).and ((hi.eventually (eventually_lt_nhds (show r⁻¹ < r⁻¹ + 1 by linarith))).and
      (normBp_eventually_pos hc hne hap hDA hnl))))
  refine ⟨max Nm N, fun n hn j hj => ?_⟩
  have hmain' := hm n (le_of_max_le_left hn) j hj
  obtain ⟨hs, hpos, hbound, hBp⟩ := hN n (le_of_max_le_right hn)
  let d : ℝ := Scalar.stableDensity θ (-((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)))
  let s : ℝ := normB μ θ ((n : ℝ) / (μ 0).toReal) / norming (etaLaw μ) θ n
  have heq : normB μ θ ((n : ℝ) / (μ 0).toReal) * (chi μ n j).toReal - d =
      s * (norming (etaLaw μ) θ n * (chi μ n j).toReal - r * d) + (s * r - 1) * d := by
    dsimp [s]
    field_simp
    ring
  rw [heq]
  apply (abs_add_le _ _).trans
  rw [abs_mul, abs_mul, abs_of_pos hpos]
  have h₁ : s * |norming (etaLaw μ) θ n * (chi μ n j).toReal - r * d| ≤ ε / 2 := by
    calc _ ≤ (r⁻¹ + 1) * η := mul_le_mul hbound.le hmain' (abs_nonneg _) (by positivity)
      _ ≤ (r⁻¹ + 2) * η := mul_le_mul_of_nonneg_right (by linarith) hη.le
      _ = ε / 2 := by dsimp [η]; field_simp
  have h₂ : |s * r - 1| * |d| ≤ ε / 2 := by
    calc _ ≤ |s * r - 1| * M := mul_le_mul_of_nonneg_left (hMb _) (abs_nonneg _)
      _ = M * |s * r - 1| := by ring
      _ ≤ ε / 2 := hs.le
  linarith

end Htheta

end BGWLeaves.LocalEstimates.Chi
