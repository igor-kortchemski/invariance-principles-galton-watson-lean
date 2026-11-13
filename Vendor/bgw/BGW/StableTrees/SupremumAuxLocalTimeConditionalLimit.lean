/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real

/-!
# Passing conditional expectations through convergence in mean

The contraction inequality gives a direct scalar proof without choosing almost-sure versions
of the approximating conditional expectations simultaneously in a real parameter.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace BGW.StableTrees

/-- Conditional expectation passes through two convergences in mean of integrable sequences. -/
theorem condExp_eq_of_integral_abs_tendsto {Ω : Type*} [m₀ : MeasurableSpace Ω]
    {μ : Measure Ω} (m : MeasurableSpace Ω) {F H : Ω → ℝ} {Fs Gs : ℕ → Ω → ℝ}
    (hF : Integrable F μ) (hH : Integrable H μ)
    (hFs : ∀ n, Integrable (Fs n) μ) (hGs : ∀ n, Integrable (Gs n) μ)
    (hcond : ∀ n, μ[Fs n | m] =ᵐ[μ] Gs n)
    (hlF : Tendsto (fun n => ∫ f, |Fs n f - F f| ∂μ) atTop (𝓝 0))
    (hlG : Tendsto (fun n => ∫ f, |Gs n f - H f| ∂μ) atTop (𝓝 0)) :
    μ[F | m] =ᵐ[μ] H := by
  have hDi : Integrable (fun f => |μ[F | m] f - H f|) μ := by
    simpa only [Pi.sub_apply] using (integrable_condExp.sub hH).abs
  have hb (n : ℕ) : (∫ f, |μ[F | m] f - H f| ∂μ) ≤
      (∫ f, |Fs n f - F f| ∂μ) + (∫ f, |Gs n f - H f| ∂μ) := by
    have h1 : Integrable (fun f => |μ[F | m] f - Gs n f|) μ := by
      simpa only [Pi.sub_apply] using (integrable_condExp.sub (hGs n)).abs
    have h2 : Integrable (fun f => |Gs n f - H f|) μ := by
      simpa only [Pi.sub_apply] using ((hGs n).sub hH).abs
    have he : (fun f => μ[F | m] f - Gs n f) =ᵐ[μ] μ[F - Fs n | m] := by
      filter_upwards [condExp_sub hF (hFs n) m, hcond n] with f hf hg
      simpa only [Pi.sub_apply, hg] using hf.symm
    have hle : (∫ f, |μ[F | m] f - Gs n f| ∂μ) ≤ ∫ f, |Fs n f - F f| ∂μ := by
      calc
        _ = ∫ f, |μ[F - Fs n | m] f| ∂μ :=
          integral_congr_ae (he.mono fun f hf => congrArg abs hf)
        _ ≤ ∫ f, |(F - Fs n) f| ∂μ := integral_abs_condExp_le _
        _ = _ := by
          apply integral_congr_ae
          exact ae_of_all _ fun f => abs_sub_comm _ _
    calc
      _ ≤ ∫ f, |μ[F | m] f - Gs n f| + |Gs n f - H f| ∂μ := by
        apply integral_mono_ae hDi (h1.add h2)
        exact ae_of_all _ fun f => abs_sub_le _ _ _
      _ = _ := integral_add h1 h2
      _ ≤ _ := add_le_add hle le_rfl
  have hz : (∫ f, |μ[F | m] f - H f| ∂μ) = 0 := by
    apply le_antisymm _ (integral_nonneg fun f => abs_nonneg _)
    simpa only [add_zero] using ge_of_tendsto (hlF.add hlG) (Eventually.of_forall hb)
  have hae := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun f => abs_nonneg _) hDi).mp hz
  filter_upwards [hae] with f hf
  exact sub_eq_zero.mp (abs_eq_zero.mp hf)

end BGW.StableTrees
