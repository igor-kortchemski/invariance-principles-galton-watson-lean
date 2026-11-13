module

public import BGWLeaves.LocalEstimates.Defs
import BGWLeaves.LocalEstimates.NormRatios
import BGWLeaves.LocalEstimates.SizeTailKernel
import BGWLeaves.LocalEstimates.Technique
import BGWLeaves.Conditioning.PassageProof
import BGWLeaves.Conditioning.LeafTail
import BGWLeaves.Conditioning.Basics
import BGWLeaves.StableAnalysis.TransformConvergence
import BGWLeaves.StableAnalysis.EtaTransfer
import Mathlib.Order.Lattice.Nat
import BGW.StableTrees.RegularVariation.Consequences

/-! # M7 provider `LeafWindow`: short size windows, threshold inversion and Corollary 5.5. -/

@[expose] public section

namespace BGWLeaves.LocalEstimates.LeafWindow

open MeasureTheory ProbabilityTheory Filter Asymptotics BGW BGW.StableTrees BGW.LocallyFinite
open BGWLeaves.StableAnalysis
open scoped ENNReal Topology

set_option linter.unusedSectionVars false

private theorem ceil_index_ratio {u : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hu : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => (⌈u n⌉₊ : ℝ) / n) atTop (𝓝 l) := by
  have hupper : Tendsto (fun n : ℕ => u n / n + 1 / (n : ℝ)) atTop (𝓝 l) := by
    simpa only [add_zero] using hu.add tendsto_one_div_atTop_nhds_zero_nat
  have hpos : ∀ᶠ n : ℕ in atTop, 0 ≤ u n ∧ 0 < (n : ℝ) := by
    filter_upwards [hu.eventually (Ioi_mem_nhds hl), eventually_ge_atTop 1] with n hn hn1
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [lt_div_iff₀ hnR, zero_mul] at hn
    exact ⟨hn.le, hnR⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hu hupper
  · filter_upwards [hpos] with n hn
    exact div_le_div_of_nonneg_right (Nat.le_ceil _) hn.2.le
  · filter_upwards [hpos] with n hn
    rw [← add_div]
    exact div_le_div_of_nonneg_right (Nat.ceil_lt_add_one hn.1).le hn.2.le

private theorem index_atTop {k : ℕ → ℕ} {l : ℝ} (hl : 0 < l)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 l)) : Tendsto k atTop atTop := by
  have ht := hk.pos_mul_atTop hl tendsto_natCast_atTop_atTop
  have ht' : Tendsto (fun n : ℕ => (k n : ℝ)) atTop atTop := ht.congr' (by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    field_simp)
  exact tendsto_natCast_atTop_iff.mp ht'

section Htheta
variable {μ : PMF ℕ} {θ : ℝ} (hc : IsCritical μ) (hne : μ 1 ≠ 1) (hap : Aperiodic μ)
  (hDA : ∃ b, StableDomain μ θ b)
include hc hne hap hDA

private theorem norming_positive : ∀ᶠ n : ℕ in atTop, 0 < norming (stepLaw μ) θ n := by
  obtain ⟨b, hb⟩ := hDA
  have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc)
    ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
  exact (TransformConvergence.tendsto_atTop (stepLaw μ) ha).eventually (eventually_gt_atTop 0)

private theorem tail_at_index {k : ℕ → ℕ}
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 1))
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |sizeTailProb μ (k n) j - sizeTailKernel θ 1 ((j : ℝ) / normB μ θ n)| ≤ η := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  have hktop := index_atTop zero_lt_one hk
  have hratio : Tendsto (fun n : ℕ => normB μ θ n / normB μ θ (k n)) atTop (𝓝 1) := by
    have ht := (NormRatios.normB_ratio_tendsto hc hne hap hDA zero_lt_one hk).inv₀ (by simp)
    simpa only [Real.one_rpow, inv_one, inv_div] using ht
  obtain ⟨L, hL, hLip⟩ := SizeTailKernel.sizeTailKernel_lipschitz hb.alpha_mem
  have hsmall : Tendsto (fun n : ℕ => L * α * |normB μ θ n / normB μ θ (k n) - 1|) atTop (𝓝 0) := by
    simpa using (hratio.sub_const 1).abs.const_mul (L * α)
  obtain ⟨Nt, ht⟩ := SizeTailKernel.lem_technical2 hc hne hap hDA (by positivity : 0 < 2 * α) (half_pos hη)
  have hev : ∀ᶠ n : ℕ in atTop,
      0 < normB μ θ n ∧ 0 < normB μ θ (k n) ∧ Nt ≤ k n ∧
      normB μ θ n / normB μ θ (k n) ≤ 2 ∧
      L * α * |normB μ θ n / normB μ θ (k n) - 1| < η / 2 := by
    filter_upwards [norming_positive hc hne hap hDA, hktop.eventually (norming_positive hc hne hap hDA),
      hktop.eventually (eventually_ge_atTop Nt), hratio.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2)),
      hsmall.eventually (eventually_lt_nhds (half_pos hη))] with n hn hkn hnt hr hs
    exact ⟨by simpa only [normB_natCast] using hn, by simpa only [normB_natCast] using hkn, hnt, hr.le, hs⟩
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨N, fun n hn j hj hju => ?_⟩
  obtain ⟨hpos, hkpos, hnt, hr, hs⟩ := hN n hn
  have hjk : (j : ℝ) ≤ (2 * α) * normB μ θ (k n) := by
    have hh := (div_le_iff₀ hkpos).mp hr
    nlinarith
  have hkt := ht (k n) hnt j hj hjk
  have hdiff : |sizeTailKernel θ 1 ((j : ℝ) / normB μ θ (k n)) -
      sizeTailKernel θ 1 ((j : ℝ) / normB μ θ n)| ≤ η / 2 := by
    apply (hLip _ _ (by positivity) (by positivity)).trans
    have heq : (j : ℝ) / normB μ θ (k n) - (j : ℝ) / normB μ θ n =
        ((j : ℝ) / normB μ θ n) * (normB μ θ n / normB μ θ (k n) - 1) := by field_simp
    rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) / normB μ θ n)]
    have hjdiv : (j : ℝ) / normB μ θ n ≤ α := (div_le_iff₀ hpos).mpr hju
    calc
      _ ≤ L * (α * |normB μ θ n / normB μ θ (k n) - 1|) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hjdiv (abs_nonneg _)) hL
      _ = L * α * |normB μ θ n / normB μ θ (k n) - 1| := by ring
      _ ≤ η / 2 := hs.le
  calc
    _ ≤ |sizeTailProb μ (k n) j - sizeTailKernel θ 1 ((j : ℝ) / normB μ θ (k n))| +
        |sizeTailKernel θ 1 ((j : ℝ) / normB μ θ (k n)) - sizeTailKernel θ 1 ((j : ℝ) / normB μ θ n)| := abs_sub_le _ _ _
    _ ≤ η / 2 + η / 2 := add_le_add hkt hdiff
    _ = η := by ring

omit hc hne hap hDA in
private theorem threshold_ratio (m : ℝ) :
    Tendsto (fun r : ℕ => (m * r - (r : ℝ) ^ (3 / 4 : ℝ)) / r) atTop (𝓝 m) := by
  have ht := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  have hh : Tendsto (fun r : ℕ => m - (r : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 m) := by
    simpa using (tendsto_const_nhds.sub ht : Tendsto (fun r : ℕ => m - (r : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 (m - 0)))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [sub_div, mul_div_cancel_right₀ _ hrR.ne', ← Real.rpow_sub_one hrR.ne']
  norm_num

omit hc hne hap hDA in
private theorem threshold_top {m : ℝ} (hm : 0 < m) :
    Tendsto (fun r : ℕ => m * r - (r : ℝ) ^ (3 / 4 : ℝ)) atTop atTop := by
  have ht := (threshold_ratio m).pos_mul_atTop hm tendsto_natCast_atTop_atTop
  apply ht.congr'
  filter_upwards [eventually_ge_atTop 1] with r hr
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast (show r ≠ 0 by omega)
  field_simp

private theorem threshold_member {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ thresholdInv (μ 0).toReal n ∧
      ⌈(μ 0).toReal * thresholdInv (μ 0).toReal n - (thresholdInv (μ 0).toReal n : ℝ) ^ (3 / 4 : ℝ)⌉ = (n : ℤ) := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hm1 : (μ 0).toReal < 1 := by have := EtaTransfer.one_sub_apply_zero_pos hc hne; linarith
  let S : Set ℕ := {r | 1 ≤ r ∧ ⌈(μ 0).toReal * r - (r : ℝ) ^ (3 / 4 : ℝ)⌉ = (n : ℤ)}
  have hS : S.Nonempty := by
    obtain ⟨r, hr⟩ := Conditioning.Basics.leafCutoff_surjective hm hm1 n hn
    have hr1 : 1 ≤ r := by
      by_contra h
      have : r = 0 := by omega
      simp [this, leafCutoff] at hr
      omega
    have hx : 0 ≤ (μ 0).toReal * r - (r : ℝ) ^ (3 / 4 : ℝ) := by
      have hn0 : 0 < leafCutoff μ r := by omega
      exact (Nat.ceil_pos.mp hn0).le
    refine ⟨r, hr1, ?_⟩
    rw [← Int.natCast_ceil_eq_ceil hx]
    exact_mod_cast hr
  have hB : BddAbove S := by
    obtain ⟨N, hN⟩ := eventually_atTop.mp ((threshold_top hm).eventually (eventually_gt_atTop (n : ℝ)))
    refine ⟨N, fun r hr => ?_⟩
    by_contra h
    have hh := hN r (by omega)
    have he := Int.le_ceil ((μ 0).toReal * r - (r : ℝ) ^ (3 / 4 : ℝ))
    rw [hr.2] at he
    exact (not_lt_of_ge he) hh
  exact Nat.sSup_mem hS hB

theorem thresholdInv_spec :
    (∀ᶠ n : ℕ in atTop, 1 ≤ thresholdInv (μ 0).toReal n ∧
      ⌈(μ 0).toReal * thresholdInv (μ 0).toReal n - (thresholdInv (μ 0).toReal n : ℝ) ^ (3 / 4 : ℝ)⌉ =
        (n : ℤ)) ∧
    Tendsto (fun n : ℕ => (thresholdInv (μ 0).toReal n : ℝ) / n) atTop (𝓝 (1 / (μ 0).toReal)) := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hev := (eventually_ge_atTop 1).mono fun n hn => threshold_member hc hne hap hDA hn
  have hrtop : Tendsto (thresholdInv (μ 0).toReal) atTop atTop := by
    apply tendsto_atTop.2
    intro K
    filter_upwards [hev, tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ((μ 0).toReal * K + 1))] with n hn hng
    have hh := Int.ceil_lt_add_one ((μ 0).toReal * thresholdInv (μ 0).toReal n - (thresholdInv (μ 0).toReal n : ℝ) ^ (3 / 4 : ℝ))
    rw [hn.2] at hh
    simp only [Int.cast_natCast] at hh
    have hh' : (K : ℝ) < thresholdInv (μ 0).toReal n := by
      nlinarith [Real.rpow_nonneg (Nat.cast_nonneg (thresholdInv (μ 0).toReal n)) (3 / 4 : ℝ)]
    exact_mod_cast hh'.le
  have hf := (threshold_ratio (μ 0).toReal).comp hrtop
  have hz : Tendsto (fun n : ℕ => 1 / (thresholdInv (μ 0).toReal n : ℝ)) atTop (𝓝 0) := tendsto_one_div_atTop_nhds_zero_nat.comp hrtop
  have hupper : Tendsto (fun n : ℕ =>
      ((μ 0).toReal * thresholdInv (μ 0).toReal n - (thresholdInv (μ 0).toReal n : ℝ) ^ (3 / 4 : ℝ)) / thresholdInv (μ 0).toReal n +
      1 / (thresholdInv (μ 0).toReal n : ℝ)) atTop (𝓝 (μ 0).toReal) := by simpa only [Function.comp_apply, add_zero] using hf.add hz
  have hinv : Tendsto (fun n : ℕ => (n : ℝ) / (thresholdInv (μ 0).toReal n : ℝ)) atTop (𝓝 (μ 0).toReal) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hf hupper
    · filter_upwards [hev] with n hn
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      simpa only [hn.2, Int.cast_natCast] using Int.le_ceil ((μ 0).toReal * thresholdInv (μ 0).toReal n - (thresholdInv (μ 0).toReal n : ℝ) ^ (3 / 4 : ℝ))
    · filter_upwards [hev] with n hn
      rw [← add_div]
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have hh := Int.ceil_lt_add_one ((μ 0).toReal * thresholdInv (μ 0).toReal n - (thresholdInv (μ 0).toReal n : ℝ) ^ (3 / 4 : ℝ))
      rw [hn.2, Int.cast_natCast] at hh
      exact hh.le
  refine ⟨hev, ?_⟩
  simpa only [inv_div, one_div] using hinv.inv₀ hm.ne'

private theorem finite_forest_measurable {j : ℕ} {s : Set (Fin j → Tree)}
    (hs : ∀ F ∈ s, ∃ ts : Fin j → PlaneTree, F = fun i => (ts i).toLocallyFinite) : MeasurableSet s := by
  apply Set.Countable.measurableSet
  apply (Set.countable_range (fun ts : Fin j → PlaneTree => fun i => (ts i).toLocallyFinite)).mono
  rintro F hF
  obtain ⟨ts, rfl⟩ := hs F hF
  exact Set.mem_range_self _

private theorem size_unique {j p q : ℕ} {F : Fin j → Tree}
    (hp : F ∈ forestSizeEvent j p) (hq : F ∈ forestSizeEvent j q) : p = q := by
  obtain ⟨ts, hp, hts⟩ := hp
  obtain ⟨us, hq, hus⟩ := hq
  have he : ts = us := by
    funext i
    exact PlaneTree.toLocallyFinite_injective (congrFun (hts.symm.trans hus) i)
  subst us
  exact hp.symm.trans hq

private theorem tail_measurable (j n : ℕ) : MeasurableSet (forestSizeGeEvent j n) := by
  have hf : MeasurableSet {F : Fin j → Tree | ∃ p : ℕ, F ∈ forestSizeEvent j p ∧ n ≤ p} := by
    apply finite_forest_measurable hc hne hap hDA
    rintro F ⟨p, ⟨ts, -, hF⟩, -⟩
    exact ⟨ts, hF⟩
  have hi : MeasurableSet {F : Fin j → Tree | ∃ i, ¬ FiniteVertices (F i)} := by
    convert MeasurableSet.iUnion (fun i : Fin j =>
      (measurableSet_finiteVertices.preimage (measurable_pi_apply i)).compl) using 1
    ext F
    simp
  exact hi.union hf

private theorem window_tail_difference (j n : ℕ) :
    (forestLaw μ j).real (forestSizeWindow (μ 0).toReal j n) =
      sizeTailProb μ ⌈(n : ℝ) - (1 / (μ 0).toReal + 1) * (n : ℝ) ^ (3 / 4 : ℝ)⌉₊ j -
        sizeTailProb μ (n + 1) j := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  let k : ℕ := ⌈(n : ℝ) - (1 / (μ 0).toReal + 1) * (n : ℝ) ^ (3 / 4 : ℝ)⌉₊
  have hkn : k ≤ n := Nat.ceil_le.mpr (by
    have hw : 0 ≤ (1 / (μ 0).toReal + 1) * (n : ℝ) ^ (3 / 4 : ℝ) := by positivity
    linarith)
  have hsub : forestSizeGeEvent j (n + 1) ⊆ forestSizeGeEvent j k := by
    rintro F (h | ⟨p, hp, hn⟩)
    · exact Or.inl h
    · exact Or.inr ⟨p, hp, by omega⟩
  have he : forestSizeWindow (μ 0).toReal j n = forestSizeGeEvent j k \ forestSizeGeEvent j (n + 1) := by
    ext F
    constructor
    · rintro ⟨p, hp, hlo, hhi⟩
      refine ⟨Or.inr ⟨p, hp, Nat.ceil_le.mpr hlo⟩, ?_⟩
      rintro (⟨i, hi⟩ | ⟨q, hq, hnq⟩)
      · obtain ⟨ts, -, rfl⟩ := hp
        exact hi (ts i).finiteVertices_toLocallyFinite
      · have := size_unique hc hne hap hDA hp hq
        omega
    · rintro ⟨h, hnot⟩
      rcases h with h | ⟨p, hp, hkp⟩
      · exact False.elim (hnot (Or.inl h))
      · refine ⟨p, hp, Nat.ceil_le.mp hkp, ?_⟩
        by_contra hpn
        exact hnot (Or.inr ⟨p, hp, by omega⟩)
  rw [he, measureReal_sdiff hsub (tail_measurable hc hne hap hDA j (n + 1))]
  rfl

theorem forestSize_window_small {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      (forestLaw μ j).real (forestSizeWindow (μ 0).toReal j n) ≤ ε := by
  let D : ℝ := 1 / (μ 0).toReal + 1
  have hraw : Tendsto (fun n : ℕ => ((n : ℝ) - D * (n : ℝ) ^ (3 / 4 : ℝ)) / n) atTop (𝓝 1) := by
    have ht : Tendsto (fun n : ℕ => 1 - D * (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub
        (((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop).const_mul D) :
          Tendsto (fun n : ℕ => 1 - D * (n : ℝ) ^ (-(1 / 4 : ℝ))) atTop (𝓝 (1 - D * 0)))
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    rw [sub_div, div_self hnR.ne', mul_div_assoc, ← Real.rpow_sub_one hnR.ne']
    norm_num
  have hk := ceil_index_ratio zero_lt_one hraw
  have hnext : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / n) atTop (𝓝 1) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add tendsto_one_div_atTop_nhds_zero_nat
    apply (show Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) by simpa using hh).congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
    push_cast
    field_simp
  obtain ⟨N₁, h₁⟩ := tail_at_index hc hne hap hDA hk hα (half_pos hε)
  obtain ⟨N₂, h₂⟩ := tail_at_index hc hne hap hDA hnext hα (half_pos hε)
  refine ⟨max N₁ N₂, fun n hn j hj hju => ?_⟩
  have h1 := h₁ n (le_of_max_le_left hn) j hj hju
  have h2 := h₂ n (le_of_max_le_right hn) j hj hju
  rw [window_tail_difference hc hne hap hDA j n]
  rw [abs_le] at h1 h2
  dsimp only [D] at h1
  linarith

theorem lem_g {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |sizeTailProb μ n j - (forestLaw μ j).real (forestLeafGeEvent j (leafCutoff μ n))| ≤ ε := by
  obtain ⟨C, c, hC, hcp, hb⟩ := Conditioning.PassageProof.lemma_passage hc hne
  obtain ⟨Ns, hs⟩ := forestSize_window_small hc hne hap hDA hα (half_pos hε)
  have ht : Tendsto (fun n : ℕ => C * Real.exp (-c * (n : ℝ) ^ (1 / 2 : ℝ))) atTop (𝓝 0) := by
    have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
      (Filter.Tendsto.const_mul_atTop hcp ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).comp tendsto_natCast_atTop_atTop))
    simpa only [Function.comp_apply, neg_mul, mul_zero] using hh.const_mul C
  have hsmall : ∀ᶠ n : ℕ in atTop, α * normB μ θ n ≤ n := by
    obtain ⟨b, hb⟩ := hDA
    have hDA' : ∃ b, IsStableAttracted (stepLaw μ) θ (mean (stepLaw μ)) b :=
      ⟨b, by rw [mean_stepLaw hc]; exact stableDomain_isStableAttracted hb⟩
    have ha := locallimit_i (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA'
    have hmono := (locallimit_ii (stepLaw μ) (stepLaw_lt_neg_one μ) (integrable_stepLaw hc) hDA').1
    rw [mean_stepLaw hc] at ha
    obtain ⟨a, heq, h⟩ := ha.exists_stableDomain hc hne hmono
    have hlim := (Scalar.regularlyVaryingSeq h).tendsto_div_self h.monotone h.pos
      (by have := h.alpha_mem.1; positivity : 0 ≤ 1 / θ)
      ((div_lt_one (by linarith [h.alpha_mem.1] : 0 < θ)).mpr h.alpha_mem.1)
    have hlim' : Tendsto (fun n : ℕ => α * (a n / n)) atTop (𝓝 0) := by simpa using hlim.const_mul α
    filter_upwards [hlim'.eventually (eventually_lt_nhds zero_lt_one), heq, eventually_ge_atTop 1] with n hn he hn1
    rw [normB_natCast, ← he]
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
    rw [← mul_div_assoc, div_lt_one hnR] at hn
    exact hn.le
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((ht.eventually (eventually_lt_nhds (half_pos hε))).and hsmall)
  refine ⟨max Ns N, fun n hn j hj hju => ?_⟩
  have hss := hs n (le_of_max_le_left hn) j hj hju
  obtain ⟨he, hnj⟩ := hN n (le_of_max_le_right hn)
  have hjn : j ≤ n := by exact_mod_cast hju.trans hnj
  have hh := hb n j hj hjn 1 (fun _ => 1) isBoundedTest_one
  simp only [setIntegral_const, smul_eq_mul, mul_one, one_mul] at hh
  exact hh.trans (by linarith)

private theorem inverse_scale_ratio {u : ℕ → ℝ} {l : ℝ} (hl : 0 < l)
    (hu : Tendsto (fun n : ℕ => u n / n) atTop (𝓝 l)) :
    Tendsto (fun n : ℕ => normB μ θ n / normB μ θ (u n)) atTop (𝓝 ((l ^ (1 / θ))⁻¹)) ∧
      ∀ᶠ n : ℕ in atTop, 0 < normB μ θ (u n) := by
  have ht := NormRatios.normB_ratio_tendsto hc hne hap hDA hl hu
  have hlp : 0 < l ^ (1 / θ) := Real.rpow_pos_of_pos hl _
  refine ⟨by simpa only [inv_div] using ht.inv₀ hlp.ne', ?_⟩
  filter_upwards [ht.eventually (Ioi_mem_nhds hlp), norming_positive hc hne hap hDA] with n hn hB
  rw [normB_natCast] at hn
  rw [lt_div_iff₀ hB, zero_mul] at hn
  exact hn

private theorem shifted_range {k : ℕ → ℕ} {l : ℝ} (hl : 0 < l)
    (hk : Tendsto (fun n : ℕ => (k n : ℝ) / n) atTop (𝓝 l)) {α : ℝ} (hα : 0 < α) :
    ∃ A : ℝ, 0 < A ∧ ∀ᶠ n : ℕ in atTop, 0 < normB μ θ (k n) ∧ α * normB μ θ n ≤ A * normB μ θ (k n) := by
  obtain ⟨hr, hp⟩ := inverse_scale_ratio hc hne hap hDA hl hk
  let r : ℝ := (l ^ (1 / θ))⁻¹
  have hr0 : 0 < r := by dsimp [r]; positivity
  refine ⟨α * (r + 1), by positivity, ?_⟩
  filter_upwards [hp, hr.eventually (eventually_lt_nhds (show r < r + 1 by linarith))] with n hn hrat
  refine ⟨hn, ?_⟩
  have hh := (div_lt_iff₀ hn).mp hrat
  nlinarith

private theorem uniform_scale_compare (f : ℝ → ℝ)
    (hf : ∀ A : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, 0 ≤ x → x ≤ A → 0 ≤ y → y ≤ A → |f x - f y| ≤ L * |x - y|)
    {d e : ℕ → ℝ} {r : ℝ}
    (hd : Tendsto (fun n : ℕ => normB μ θ n / d n) atTop (𝓝 r))
    (he : Tendsto (fun n : ℕ => normB μ θ n / e n) atTop (𝓝 r))
    (hp : ∀ᶠ n : ℕ in atTop, 0 < d n ∧ 0 < e n)
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, (j : ℝ) ≤ α * normB μ θ n →
      |f ((j : ℝ) / d n) - f ((j : ℝ) / e n)| ≤ η := by
  let A : ℝ := α * (|r| + 1)
  obtain ⟨L, hL, hLip⟩ := hf A
  have hsmall : Tendsto (fun n : ℕ => L * α * |normB μ θ n / d n - normB μ θ n / e n|) atTop (𝓝 0) := by
    simpa using (hd.sub he).abs.const_mul (L * α)
  have hdu : ∀ᶠ n : ℕ in atTop, normB μ θ n / d n ≤ |r| + 1 := by
    filter_upwards [hd.eventually (Metric.ball_mem_nhds r zero_lt_one)] with n hn
    rw [Real.dist_eq] at hn
    linarith [le_abs_self (normB μ θ n / d n - r), le_abs_self r]
  have heu : ∀ᶠ n : ℕ in atTop, normB μ θ n / e n ≤ |r| + 1 := by
    filter_upwards [he.eventually (Metric.ball_mem_nhds r zero_lt_one)] with n hn
    rw [Real.dist_eq] at hn
    linarith [le_abs_self (normB μ θ n / e n - r), le_abs_self r]
  obtain ⟨N, hN⟩ := eventually_atTop.mp ((hsmall.eventually (eventually_lt_nhds hη)).and
    (hp.and (hdu.and (heu.and (norming_positive hc hne hap hDA)))))
  refine ⟨N, fun n hn j hju => ?_⟩
  obtain ⟨hs, ⟨hdp, hep⟩, hdb, heb, hBp⟩ := hN n hn
  have hB : 0 < normB μ θ n := by simpa only [normB_natCast] using hBp
  have harg (a : ℝ) (ha : 0 < a) (hab : normB μ θ n / a ≤ |r| + 1) : 0 ≤ (j : ℝ) / a ∧ (j : ℝ) / a ≤ A := by
    refine ⟨by positivity, ?_⟩
    calc _ ≤ α * normB μ θ n / a := div_le_div_of_nonneg_right hju ha.le
      _ = α * (normB μ θ n / a) := by ring
      _ ≤ A := mul_le_mul_of_nonneg_left hab hα.le
  obtain ⟨hxd, hxdA⟩ := harg (d n) hdp hdb
  obtain ⟨hxe, hxeA⟩ := harg (e n) hep heb
  apply (hLip _ _ hxd hxdA hxe hxeA).trans
  have heq : (j : ℝ) / d n - (j : ℝ) / e n =
      ((j : ℝ) / normB μ θ n) * (normB μ θ n / d n - normB μ θ n / e n) := by field_simp
  rw [heq, abs_mul, abs_of_nonneg (by positivity : 0 ≤ (j : ℝ) / normB μ θ n)]
  have hjdiv : (j : ℝ) / normB μ θ n ≤ α := (div_le_iff₀ hB).mpr hju
  calc
    _ ≤ L * (α * |normB μ θ n / d n - normB μ θ n / e n|) := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hjdiv (abs_nonneg _)) hL
    _ = L * α * |normB μ θ n / d n - normB μ θ n / e n| := by ring
    _ ≤ η := hs.le

private theorem linear_time_ratio (m : ℝ) (hm : 0 < m) :
    Tendsto (fun n : ℕ => ((n : ℝ) / m) / n) atTop (𝓝 (1 / m)) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  field_simp

theorem lem_technical_i {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(psiStar μ n j).toReal - sizeTailKernel θ 1 ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  obtain ⟨hkvalid, hk⟩ := thresholdInv_spec hc hne hap hDA
  have hktop := index_atTop (one_div_pos.mpr hm) hk
  obtain ⟨A, hA, hrange⟩ := shifted_range hc hne hap hDA (one_div_pos.mpr hm) hk hα
  obtain ⟨Ng, hg⟩ := lem_g hc hne hap hDA hA (by positivity : 0 < ε / 3)
  obtain ⟨Nt, ht⟩ := SizeTailKernel.lem_technical2 hc hne hap hDA hA (by positivity : 0 < ε / 3)
  obtain ⟨hr₁, hp₁⟩ := inverse_scale_ratio hc hne hap hDA (one_div_pos.mpr hm) hk
  obtain ⟨hr₂, hp₂⟩ := inverse_scale_ratio hc hne hap hDA (one_div_pos.mpr hm)
    (linear_time_ratio hc hne hap hDA (μ 0).toReal hm)
  obtain ⟨L, hL, hLip⟩ := SizeTailKernel.sizeTailKernel_lipschitz hb.alpha_mem
  obtain ⟨Nc, hcomp⟩ := uniform_scale_compare hc hne hap hDA (sizeTailKernel θ 1)
    (fun _ => ⟨L, hL, fun x y hx _ hy _ => hLip x y hx hy⟩) hr₁ hr₂
    (hp₁.and hp₂) hα (by positivity : 0 < ε / 3)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hkvalid.and (hrange.and
    ((hktop.eventually (eventually_ge_atTop Ng)).and (hktop.eventually (eventually_ge_atTop Nt)))))
  refine ⟨max 1 (max N Nc), fun n hn j hj hju => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have hnN : N ≤ n := by omega
  have hnNc : Nc ≤ n := by omega
  obtain ⟨⟨hkn, hceil⟩, ⟨hkpos, hju'⟩, hkg, hkt⟩ := hN n hnN
  have hjk : (j : ℝ) ≤ A * normB μ θ (thresholdInv (μ 0).toReal n) := hju.trans hju'
  have hg' := hg _ hkg j hj hjk
  have ht' := ht _ hkt j hj hjk
  have hc' := hcomp n hnNc j hju
  have hcut : leafCutoff μ (thresholdInv (μ 0).toReal n) = n := by
    unfold leafCutoff
    rw [← Int.ceil_toNat, hceil, Int.toNat_natCast]
  rw [hcut] at hg'
  change |sizeTailProb μ (thresholdInv (μ 0).toReal n) j - (psiStar μ n j).toReal| ≤ ε / 3 at hg'
  rw [abs_le] at hg' ht' hc' ⊢
  constructor <;> linarith
omit hc hne hap hDA in
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


set_option linter.unusedVariables false in
theorem mn_ratio_tendsto {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal)) :
    Tendsto (fun n : ℕ => ((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℝ) / n) atTop (𝓝 (1 - a)) := by
  clear hr
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hri : Tendsto (fun n : ℕ => (r n : ℝ) / n) atTop (𝓝 (1 / (μ 0).toReal)) := by
    simpa only [inv_div, one_div] using hrn.inv₀ hm.ne'
  have hraw : Tendsto (fun n : ℕ => (a * (μ 0).toReal * r n) / n) atTop (𝓝 a) := by
    have hh := hri.const_mul (a * (μ 0).toReal)
    have he : a * (μ 0).toReal * (1 / (μ 0).toReal) = a := by field_simp
    rw [he] at hh
    simpa only [mul_div_assoc] using hh
  have hfloor := floor_index_ratio ha0 hraw
  have hlim : Tendsto (fun n : ℕ => 1 - (⌊a * (μ 0).toReal * r n⌋₊ : ℝ) / n) atTop (𝓝 (1 - a)) :=
    tendsto_const_nhds.sub hfloor
  apply hlim.congr'
  filter_upwards [hfloor.eventually (eventually_lt_nhds ha1), eventually_ge_atTop 1] with n hn hn1
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn1
  have hle : ⌊a * (μ 0).toReal * r n⌋₊ ≤ n := by
    have hh := (div_lt_one hnR).mp hn
    exact_mod_cast hh.le
  rw [Nat.cast_sub hle, sub_div, div_self hnR.ne']

private theorem uniform_leaf_shift (f : ℝ → ℝ)
    (hf : ∀ A : ℝ, ∃ L : ℝ, 0 ≤ L ∧ ∀ x y : ℝ, 0 ≤ x → x ≤ A → 0 ≤ y → y ≤ A → |f x - f y| ≤ L * |x - y|)
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {α η : ℝ} (hα : 0 < α) (hη : 0 < η) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, (j : ℝ) ≤ α * normB μ θ n →
      |f ((j : ℝ) / ((1 - a) ^ (1 / θ) * normB μ θ ((n : ℝ) / (μ 0).toReal))) -
        f ((j : ℝ) / normB μ θ (((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℝ) / (μ 0).toReal))| ≤ η := by
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hq : 0 < 1 - a := sub_pos.mpr ha1
  have hmn := mn_ratio_tendsto hc hne hap hDA ha0 ha1 hr hrn
  have hv : Tendsto (fun n : ℕ => (((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℝ) / (μ 0).toReal) / n)
      atTop (𝓝 ((1 - a) / (μ 0).toReal)) := by
    convert hmn.div_const (μ 0).toReal using 1
    ext n
    ring
  obtain ⟨ht₁, hp₁⟩ := inverse_scale_ratio hc hne hap hDA (one_div_pos.mpr hm)
    (linear_time_ratio hc hne hap hDA (μ 0).toReal hm)
  obtain ⟨ht₂, hp₂⟩ := inverse_scale_ratio hc hne hap hDA (div_pos hq hm) hv
  have hcpos : 0 < (1 - a) ^ (1 / θ) := Real.rpow_pos_of_pos hq _
  have heq : (((1 - a) / (μ 0).toReal) ^ (1 / θ))⁻¹ =
      ((1 / (μ 0).toReal) ^ (1 / θ))⁻¹ / (1 - a) ^ (1 / θ) := by
    rw [Real.div_rpow hq.le hm.le, Real.div_rpow (by norm_num : (0 : ℝ) ≤ 1) hm.le, Real.one_rpow]
    simp only [inv_div, div_one]
  rw [heq] at ht₂
  have ht₁' : Tendsto (fun n : ℕ => normB μ θ n / ((1 - a) ^ (1 / θ) * normB μ θ ((n : ℝ) / (μ 0).toReal))) atTop
      (𝓝 (((1 / (μ 0).toReal) ^ (1 / θ))⁻¹ / (1 - a) ^ (1 / θ))) := by
    convert ht₁.div_const ((1 - a) ^ (1 / θ)) using 1
    ext n
    ring
  apply uniform_scale_compare hc hne hap hDA f hf ht₁' ht₂ _ hα hη
  filter_upwards [hp₁, hp₂] with n hn₁ hn₂
  exact ⟨mul_pos hcpos hn₁, hn₂⟩

theorem eq_amontrer {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |sizeTailKernel θ 1 ((j : ℝ) / ((1 - a) ^ (1 / θ) * normB μ θ ((n : ℝ) / (μ 0).toReal))) -
          sizeTailKernel θ 1 ((j : ℝ) / normB μ θ (((n - ⌊a * (μ 0).toReal * r n⌋₊ : ℕ) : ℝ) / (μ 0).toReal))| ≤ ε := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  obtain ⟨L, hL, hLip⟩ := SizeTailKernel.sizeTailKernel_lipschitz hb.alpha_mem
  obtain ⟨N, hN⟩ := uniform_leaf_shift hc hne hap hDA (sizeTailKernel θ 1)
    (fun _ => ⟨L, hL, fun x y hx _ hy _ => hLip x y hx hy⟩) ha0 ha1 hr hrn hα hε
  exact ⟨N, fun n hn j _ hj => hN n hn j hj⟩

theorem cor_tejhnique_i {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(psiStar μ (n - ⌊a * (μ 0).toReal * r n⌋₊) j).toReal -
          sizeTailKernel θ (1 - a) ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hq : 0 < 1 - a := sub_pos.mpr ha1
  have hmn := mn_ratio_tendsto hc hne hap hDA ha0 ha1 hr hrn
  have hmtop := index_atTop hq hmn
  obtain ⟨A, hA, hrange⟩ := shifted_range hc hne hap hDA hq hmn hα
  obtain ⟨Nt, ht⟩ := lem_technical_i hc hne hap hDA hA (half_pos hε)
  obtain ⟨Nc, hcomp⟩ := eq_amontrer hc hne hap hDA ha0 ha1 hr hrn hα (half_pos hε)
  obtain ⟨-, hpos⟩ := inverse_scale_ratio hc hne hap hDA (one_div_pos.mpr hm)
    (linear_time_ratio hc hne hap hDA (μ 0).toReal hm)
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrange.and ((hmtop.eventually (eventually_ge_atTop Nt)).and hpos))
  refine ⟨max N Nc, fun n hn j hj hju => ?_⟩
  obtain ⟨⟨hmp, hrng⟩, hnt, hp⟩ := hN n (le_of_max_le_left hn)
  have htt := ht _ hnt j hj (hju.trans hrng)
  have hcc := hcomp n (le_of_max_le_right hn) j hj hju
  have heq : sizeTailKernel θ (1 - a) ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)) =
      sizeTailKernel θ 1 ((j : ℝ) / ((1 - a) ^ (1 / θ) * normB μ θ ((n : ℝ) / (μ 0).toReal))) := by
    rw [SizeTailKernel.sizeTailKernel_scaling hb.alpha_mem hq (by positivity), Real.rpow_neg hq.le]
    congr 1
    ring
  rw [heq, abs_le]
  rw [abs_le] at htt hcc
  constructor <;> linarith

theorem cor_tejhnique_ii (hnl : ¬ IsLatticeLaw (etaLaw μ))
    {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r : ℕ → ℕ} (hr : ∀ n, 0 < r n)
    (hrn : Tendsto (fun n : ℕ => (n : ℝ) / r n) atTop (𝓝 (μ 0).toReal))
    {α : ℝ} (hα : 0 < α) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → ∀ j : ℕ, 1 ≤ j → (j : ℝ) ≤ α * normB μ θ n →
      |(n : ℝ) * (psi μ (n - ⌊a * (μ 0).toReal * r n⌋₊) j).toReal -
          qKernel θ (1 - a) ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal))| ≤ ε := by
  obtain ⟨b, hb⟩ := hDA
  have hDA : ∃ b, StableDomain μ θ b := ⟨b, hb⟩
  have hm : 0 < (μ 0).toReal := ENNReal.toReal_pos (hc.apply_zero_ne_zero hne) (μ.apply_ne_top 0)
  have hq : 0 < 1 - a := sub_pos.mpr ha1
  let k : ℕ → ℕ := fun n => n - ⌊a * (μ 0).toReal * r n⌋₊
  let t : ℝ := 1 / (1 - a)
  let c : ℝ := (1 - a) ^ (1 / θ)
  have ht : 0 < t := one_div_pos.mpr hq
  have hcpos : 0 < c := Real.rpow_pos_of_pos hq _
  let η : ℝ := ε / (3 * (t + 2))
  have hη : 0 < η := by dsimp [η]; positivity
  have hbudget : (t + 1) * η ≤ ε / 3 := by
    calc _ ≤ (t + 2) * η := mul_le_mul_of_nonneg_right (by linarith) hη.le
      _ = ε / 3 := by dsimp [η]; field_simp
  have hmn := mn_ratio_tendsto hc hne hap hDA ha0 ha1 hr hrn
  have hktop : Tendsto k atTop atTop := index_atTop hq hmn
  have hinv : Tendsto (fun n : ℕ => (n : ℝ) / (k n : ℝ)) atTop (𝓝 t) := by
    simpa only [inv_div, one_div, t] using hmn.inv₀ hq.ne'
  obtain ⟨A, hA, hrange⟩ := shifted_range hc hne hap hDA hq hmn hα
  obtain ⟨Nt, htech⟩ := Technique.lem_technical_ii hc hne hap hDA hnl hA hη
  obtain ⟨Nc, hcomp⟩ := uniform_leaf_shift hc hne hap hDA (qKernel θ 1)
    (SizeTailKernel.qKernel_one_lipschitzOn hb.alpha_mem) ha0 ha1 hr hrn hα hη
  obtain ⟨M, hM, hMb⟩ := Scalar.exists_stableDensity_le (α := θ)
  obtain ⟨hDen, hpDen⟩ := inverse_scale_ratio hc hne hap hDA (one_div_pos.mpr hm)
    (linear_time_ratio hc hne hap hDA (μ 0).toReal hm)
  let R : ℝ := ((1 / (μ 0).toReal) ^ (1 / θ))⁻¹ / c
  let Q : ℝ := (α * (|R| + 1)) * M
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hDb : ∀ᶠ n : ℕ in atTop, normB μ θ n / (c * normB μ θ ((n : ℝ) / (μ 0).toReal)) ≤ |R| + 1 := by
    have hd : Tendsto (fun n : ℕ => normB μ θ n / (c * normB μ θ ((n : ℝ) / (μ 0).toReal))) atTop (𝓝 R) := by
      convert hDen.div_const c using 1
      ext n
      ring
    filter_upwards [hd.eventually (Metric.ball_mem_nhds R zero_lt_one)] with n hn
    rw [Real.dist_eq] at hn
    linarith [le_abs_self (normB μ θ n / (c * normB μ θ ((n : ℝ) / (μ 0).toReal)) - R), le_abs_self R]
  have hsmall : Tendsto (fun n : ℕ => Q * |(n : ℝ) / (k n : ℝ) - t|) atTop (𝓝 0) := by
    simpa using (hinv.sub_const t).abs.const_mul Q
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hrange.and ((hktop.eventually (eventually_ge_atTop (max 1 Nt))).and
    (hpDen.and (hDb.and ((hinv.eventually (eventually_lt_nhds (show t < t + 1 by linarith))).and
      (hsmall.eventually (eventually_lt_nhds (by positivity : 0 < ε / 3))))))))
  refine ⟨max N Nc, fun n hn j hj hju => ?_⟩
  obtain ⟨⟨hkp, hrng⟩, hkN, hdp, hdb, hir, hsm⟩ := hN n (le_of_max_le_left hn)
  have hk1 : 1 ≤ k n := le_of_max_le_left hkN
  have hkt : Nt ≤ k n := le_of_max_le_right hkN
  have hk0 : (k n : ℝ) ≠ 0 := by exact_mod_cast (show k n ≠ 0 by omega)
  have hir0 : 0 ≤ (n : ℝ) / (k n : ℝ) := by positivity
  have hT := htech (k n) hkt j hj (hju.trans hrng)
  have hC := hcomp n (le_of_max_le_right hn) j hju
  let x : ℝ := (j : ℝ) / normB μ θ (((k n : ℕ) : ℝ) / (μ 0).toReal)
  let y : ℝ := (j : ℝ) / (c * normB μ θ ((n : ℝ) / (μ 0).toReal))
  have hy : 0 ≤ y := by dsimp [y]; positivity
  have hyA : y ≤ α * (|R| + 1) := by
    calc _ ≤ α * normB μ θ n / (c * normB μ θ ((n : ℝ) / (μ 0).toReal)) := div_le_div_of_nonneg_right hju (by positivity)
      _ = α * (normB μ θ n / (c * normB μ θ ((n : ℝ) / (μ 0).toReal))) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hdb hα.le
  have hqb : |qKernel θ 1 y| ≤ Q := by
    rw [qKernel_one, abs_mul, abs_of_nonneg hy]
    exact mul_le_mul hyA (hMb _) (abs_nonneg _) (by positivity)
  have heval : qKernel θ (1 - a) ((j : ℝ) / normB μ θ ((n : ℝ) / (μ 0).toReal)) = t * qKernel θ 1 y := by
    rw [SizeTailKernel.qKernel_scaling hq, Real.rpow_neg hq.le]
    rw [show (1 - a)⁻¹ = t by dsimp only [t]; rw [one_div]]
    apply congrArg (fun z : ℝ => t * qKernel θ 1 z)
    dsimp only [y, c]
    ring
  have h₁ : |(n : ℝ) * (psi μ (k n) j).toReal - ((n : ℝ) / (k n : ℝ)) * qKernel θ 1 x| ≤ ε / 3 := by
    have heq : (n : ℝ) * (psi μ (k n) j).toReal - ((n : ℝ) / (k n : ℝ)) * qKernel θ 1 x =
        ((n : ℝ) / (k n : ℝ)) * ((k n : ℝ) * (psi μ (k n) j).toReal - qKernel θ 1 x) := by field_simp
    rw [heq, abs_mul, abs_of_nonneg hir0]
    exact (mul_le_mul hir.le hT (abs_nonneg _) (by linarith : 0 ≤ t + 1)).trans hbudget
  have h₂ : |((n : ℝ) / (k n : ℝ)) * qKernel θ 1 x - ((n : ℝ) / (k n : ℝ)) * qKernel θ 1 y| ≤ ε / 3 := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hir0]
    rw [abs_sub_comm] at hC
    exact (mul_le_mul hir.le hC (abs_nonneg _) (by linarith : 0 ≤ t + 1)).trans hbudget
  have h₃ : |((n : ℝ) / (k n : ℝ)) * qKernel θ 1 y - t * qKernel θ 1 y| ≤ ε / 3 := by
    rw [← sub_mul, abs_mul]
    calc _ ≤ |(n : ℝ) / (k n : ℝ) - t| * Q := mul_le_mul_of_nonneg_left hqb (abs_nonneg _)
      _ = Q * |(n : ℝ) / (k n : ℝ) - t| := by ring
      _ ≤ ε / 3 := hsm.le
  have hh := abs_sub_le ((n : ℝ) * (psi μ (k n) j).toReal)
    (((n : ℝ) / (k n : ℝ)) * qKernel θ 1 x) (t * qKernel θ 1 y)
  have hh' := abs_sub_le (((n : ℝ) / (k n : ℝ)) * qKernel θ 1 x)
    (((n : ℝ) / (k n : ℝ)) * qKernel θ 1 y) (t * qKernel θ 1 y)
  rw [heval]
  change |_ - _| ≤ ε
  linarith

end Htheta

end BGWLeaves.LocalEstimates.LeafWindow
