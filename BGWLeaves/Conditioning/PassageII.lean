module

public import BGWLeaves.Conditioning.PassageProof
public import BGWLeaves.Conditioning.LeafTail
import BGWLeaves.LeafConcentration.OeLemmas
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Proposition 4.4(ii): passage from size-tail to leaf-tail conditioning

This extension imports the finished passage and tail providers without introducing
an import cycle. It exports `BGWLeaves.Conditioning.LeafTail.prop_passage_ii`
with the frozen type. The error is normalized by the size tail, bounded by the
polynomial lower estimate, and sent to zero using the size-window estimate and
exponential decay. The remaining normalization is `leafGe_sizeGe_ratio`.
-/

@[expose] public section

namespace BGWLeaves.Conditioning.LeafTail

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW
open BGW.StableTrees BGW.LocallyFinite BGWLeaves.StableAnalysis
open scoped ENNReal Topology

private theorem passageII_cond_div {α : Type*} [MeasurableSpace α] (P : Measure α)
    (s : Set α) (U : α → ℝ) :
    (∫ x, U x ∂(P[|s])) = (∫ x in s, U x ∂P) / P.real s := by
  simp only [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv,
    Measure.real, smul_eq_mul, div_eq_mul_inv, mul_comm]

private theorem passageII_poly_exp {c : ℝ} (hc : 0 < c) (q : ℝ) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ q * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hb⟩ := LeafConcentration.OeLemmas.polyExp_absorb
    (by norm_num : (0 : ℝ) < 1 / 2) q (half_pos hc) (half_lt_self hc)
  have hr : Tendsto (fun n : ℕ => (c / 2) * (n : ℝ) ^ (1 / 2 : ℝ)) atTop atTop :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul_atTop (half_pos hc)
  have he := (Real.tendsto_exp_neg_atTop_nhds_zero.comp hr).const_mul C
  rw [mul_zero] at he
  apply squeeze_zero' (Eventually.of_forall (fun n => by positivity))
    (Eventually.of_forall hb)
  simpa only [Function.comp_apply, neg_mul] using he

/-- Proposition 4.4(ii), assembled after the passage and tail providers to keep imports acyclic. -/
theorem prop_passage_ii {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1)
    (hap : Aperiodic μ) (hDA : ∃ a, StableDomain μ θ a) {M : ℝ} {U : ℕ → LocallyFinite.Tree → ℝ}
    (hU : ∀ n, IsBoundedTest M (U n)) {L : ℝ}
    (h : Tendsto (fun n : ℕ => ∫ τ, U n τ ∂((bienaymeLaw μ.toMeasure)[|sizeGeEvent n])) atTop (𝓝 L)) :
    Tendsto (fun n : ℕ => ∫ τ, U n τ
      ∂((bienaymeLaw μ.toMeasure)[|leafGeEvent (leafCutoff μ n)])) atTop (𝓝 L) := by
  obtain ⟨C, c, hC, hc0, hb⟩ := PassageProof.lemma_passage_tree hc hne
  obtain ⟨d, hd, N, hN⟩ := sizeGe_poly_lower hc hne hap hDA
    (η := (1 / 8 : ℝ)) (by norm_num)
  let P := bienaymeLaw μ.toMeasure
  let a : ℕ → ℝ := fun n => P.real (sizeGeEvent n)
  let b : ℕ → ℝ := fun n => P.real (leafGeEvent (leafCutoff μ n))
  let A : ℕ → ℝ := fun n => ∫ τ in sizeGeEvent n, U n τ ∂P
  let B : ℕ → ℝ := fun n => ∫ τ in leafGeEvent (leafCutoff μ n), U n τ ∂P
  let W : ℕ → ℝ := fun n => P.real (sizeWindow (μ 0).toReal n)
  let q : ℝ := 1 / θ + 1 / 8
  have hM : 0 ≤ M := ((hU 0).2 PlaneTree.leaf.toLocallyFinite).1.trans
    ((hU 0).2 PlaneTree.leaf.toLocallyFinite).2
  have hapos : ∀ᶠ n : ℕ in atTop, 0 < a n := by
    filter_upwards [eventually_ge_atTop (max N 1)] with n hn
    exact lt_of_lt_of_le (mul_pos hd (Real.rpow_pos_of_pos
      (show (0 : ℝ) < n by exact_mod_cast le_trans (le_max_right _ _) hn) _))
      (hN n (le_trans (le_max_left _ _) hn))
  have hwindow := sizeWindow_small hc hne hap hDA (η := (1 / 8 : ℝ)) (by norm_num) (by norm_num)
  have hexp := passageII_poly_exp hc0 q
  have hmajor : Tendsto (fun n : ℕ => (M / d) *
      ((n : ℝ) ^ q * W n + C * ((n : ℝ) ^ q * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)))))
      atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using (hwindow.add (hexp.const_mul C)).const_mul (M / d)
  have herr : Tendsto (fun n : ℕ => (A n - B n) / a n) atTop (𝓝 0) := by
    apply squeeze_zero_norm' _ hmajor
    filter_upwards [hapos, eventually_ge_atTop (max N 1)] with n hn hnN
    have hn1 : 1 ≤ n := le_trans (le_max_right _ _) hnN
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hnp := Real.rpow_pos_of_pos hn0 q
    have hlo := hN n (le_trans (le_max_left _ _) hnN)
    have hlo' : d / (n : ℝ) ^ q ≤ a n := by
      have he : -(1 / θ) - (1 / 8 : ℝ) = -q := by dsimp [q]; ring
      change d * (n : ℝ) ^ (-(1 / θ) - (1 / 8 : ℝ)) ≤ a n at hlo
      rw [he, Real.rpow_neg hn0.le] at hlo
      simpa only [div_eq_mul_inv] using hlo
    have hcap : d ≤ a n * (n : ℝ) ^ q := (div_le_iff₀ hnp).1 hlo'
    have hinv : 1 / a n ≤ (n : ℝ) ^ q / d := (div_le_div_iff₀ hn hd).2 (by nlinarith)
    have hdiff := hb n hn1 M (U n) (hU n)
    change |A n - B n| ≤ M * (W n + C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) at hdiff
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hn]
    calc
      |A n - B n| / a n ≤
          (M * (W n + C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ)))) * ((n : ℝ) ^ q / d) := by
        rw [div_eq_mul_inv]
        exact mul_le_mul hdiff (by simpa only [one_div] using hinv) (inv_nonneg.2 hn.le)
          (by dsimp [W]; positivity)
      _ = _ := by ring
  have hratio := leafGe_sizeGe_ratio hc hne hap hDA
  have ht := (h.sub herr).div hratio one_ne_zero
  simp only [sub_zero, div_one] at ht
  apply ht.congr'
  filter_upwards [hapos] with n hn
  change ((∫ τ, U n τ ∂(P[|sizeGeEvent n])) - (A n - B n) / a n) / (b n / a n) = _
  rw [passageII_cond_div, passageII_cond_div]
  change (A n / a n - (A n - B n) / a n) / (b n / a n) = B n / b n
  rw [← sub_div, sub_sub_cancel]
  exact div_div_div_cancel_right₀ hn.ne' _ _

end BGWLeaves.Conditioning.LeafTail
