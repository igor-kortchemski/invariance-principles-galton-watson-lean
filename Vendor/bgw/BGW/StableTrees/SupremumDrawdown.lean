/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumDrawdownBrownian

/-!
# Exponential drawdown and the supremum transform

The drawdown at an independent exponential clock has exponential law. Independence
and the process transform determine the supremum transform below its apparent pole;
real analyticity extends the denominator-free identity and gives its diagonal value.

Main results, with `Φ = q^{1/θ}`: `law_supReflected_expTime` (the drawdown is exponential with
parameter `Φ`), `integral_exp_neg_eval_expTime`, `integral_exp_neg_supRunning_expTime`
(`E e^{-λ S_{e_q}} = q (Φ - λ) / (Φ (q - λ^θ))`), its diagonal value `1/θ`, the Brownian case
`law_supRunning_expTime_two`, and `law_supRunning_expTime_ne_exp` for `θ < 2`.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
* A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed., Springer, 2014,
  Chapter 6 (Wiener–Hopf factorization).
-/

@[expose] public section
