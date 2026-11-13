/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeTailL1
import BGW.StableTrees.SupremumAuxLocalTimeConditionalLimit

/-!
# Conditional potential at the random reflected state

Convergence in mean passes the conditional occupation identity of
`BGW.StableTrees.SupremumPotential` to the clock. Uniform resolvent convergence applies at the
actual reflected state. The time `s` is deterministic.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open BGW.Skorokhod

namespace BGW.StableTrees

/-- **Conditional potential of the reflected family**: for every `q > 0` and `s`,
`E[∫_{(s,∞)} e^{-qt} dL^aux_t | F_s] = e^{-qs} h_q(R^0_s)`. -/
theorem condExp_supAuxDiscountedTail {θ : ℝ} (hθ : 1 < θ ∧ θ ≤ 2) {q : ℝ} (hq : 0 < q)
    (s : ℝ≥0) :
    (stableLocalLaw θ : Measure DLoc)[supAuxDiscountedTail θ q s | DLoc.filtration s]
      =ᵐ[(stableLocalLaw θ : Measure DLoc)]
      fun f => Real.exp (-q * (s : ℝ)) * supPotential θ q (supReflectedFrom 0 f s) := by
  let P : Measure DLoc := stableLocalLaw θ
  let a := Real.exp (-q * (s : ℝ))
  let C := q ^ (1 / θ) / q
  let H : DLoc → ℝ := fun f => a * supPotential θ q (supReflectedFrom 0 f s)
  let Fs : ℕ → DLoc → ℝ := fun n => supAuxOccupationTail q (supAuxEps θ n) s
  let Gs : ℕ → DLoc → ℝ := fun n => P[Fs n | DLoc.filtration s]
  have hseq0 := isSupAuxEpsSeq_supAuxEps hθ
  have hseq : Tendsto (supAuxEps θ) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.mpr ⟨hseq0.2.2.1, Eventually.of_forall hseq0.1⟩
  have hR : Measurable (fun f : DLoc => supReflectedFrom 0 f s) :=
    (measurable_rawFiltration_supReflectedFrom 0 s).mono (DLoc.rawFiltration.le s) le_rfl
  have hHmeas : Measurable H :=
    measurable_const.mul ((continuous_supPotential hθ hq).measurable.comp hR)
  have hHi : Integrable H P := by
    apply Integrable.of_bound hHmeas.aestronglyMeasurable (a * C)
    filter_upwards with f
    change ‖a * supPotential θ q (supReflectedFrom 0 f s)‖ ≤ a * C
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _),
      abs_of_nonneg (supPotential_mem_Icc hθ hq _).1]
    exact mul_le_mul_of_nonneg_left (supPotential_mem_Icc hθ hq _).2 (Real.exp_pos _).le
  have hc (n : ℕ) : Gs n =ᵐ[P]
      fun f => a * supOccupationResolvent θ q (supAuxEps θ n) (supReflectedFrom 0 f s) := by
    have hh := condExp_reflectedResolvent_tail hθ hq 0 s
      (measurable_supOccKernel (supAuxEps θ n))
      ⟨(supAuxEps θ n)⁻¹, fun r => by
        rw [abs_of_nonneg (supOccKernel_mem_Icc (hseq0.1 n) r).1]
        exact (supOccKernel_mem_Icc (hseq0.1 n) r).2⟩
    dsimp only [Gs, Fs, P, a, supAuxOccupationTail, supOccupationResolvent]
    exact hh
  have hGi (n : ℕ) : Integrable (Gs n) P := integrable_condExp
  have hlG : Tendsto (fun n => ∫ f, |Gs n f - H f| ∂P) atTop (𝓝 0) := by
    have hb (n : ℕ) : ∀ᵐ f ∂P, ‖|Gs n f - H f|‖ ≤ a * (2 * C) := by
      filter_upwards [hc n] with f hf
      rw [hf]
      change ‖|a * supOccupationResolvent θ q (supAuxEps θ n) (supReflectedFrom 0 f s) -
        a * supPotential θ q (supReflectedFrom 0 f s)|‖ ≤ a * (2 * C)
      rw [Real.norm_eq_abs, abs_abs, ← mul_sub, abs_mul, abs_of_pos (Real.exp_pos _)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
      have hu := supOccupationResolvent_mem_Icc hθ hq (hseq0.1 n) (supReflectedFrom 0 f s)
      have hv := supPotential_mem_Icc hθ hq (supReflectedFrom 0 f s)
      have hab := abs_sub (supOccupationResolvent θ q (supAuxEps θ n) (supReflectedFrom 0 f s))
        (supPotential θ q (supReflectedFrom 0 f s))
      rw [abs_of_nonneg hu.1, abs_of_nonneg hv.1] at hab
      linarith only [hab, hu.2, hv.2]
    have hpoint : ∀ᵐ f ∂P, Tendsto (fun n => |Gs n f - H f|) atTop (𝓝 0) := by
      filter_upwards [ae_all_iff.mpr hc] with f hf
      have ht := ((tendstoUniformlyOn_supOccupationResolvent hθ hq).tendsto_at
        (supReflectedFrom_nonneg 0 f s)).comp hseq
      have hlim := ((ht.const_mul a).sub (tendsto_const_nhds (x := H f))).abs
      have he : (fun n => |Gs n f - H f|) =
          fun n => |a * supOccupationResolvent θ q (supAuxEps θ n) (supReflectedFrom 0 f s) -
            H f| := funext fun n => congrArg (fun x => |x - H f|) (hf n)
      rw [he]
      simpa only [Function.comp_def, H, sub_self, abs_zero] using hlim
    have hl := tendsto_integral_of_dominated_convergence (μ := P) (fun _ => a * (2 * C))
      (fun n => ((hGi n).sub hHi).abs.aestronglyMeasurable)
      (integrable_const _) hb hpoint
    simpa only [Pi.sub_apply, integral_zero] using hl
  have hlimF := (tendsto_integral_abs_supAuxOccupationTail_sub hθ hq s).comp hseq
  exact condExp_eq_of_integral_abs_tendsto (DLoc.filtration s)
    (F := supAuxDiscountedTail θ q s) (H := H) (Fs := Fs) (Gs := Gs)
    (integrable_supAuxDiscountedTail hθ hq s) hHi
    (fun n => integrable_supAuxOccupationTail θ hq (hseq0.1 n) s)
    hGi
    (fun n => Filter.EventuallyEq.rfl) hlimF hlG

end BGW.StableTrees
