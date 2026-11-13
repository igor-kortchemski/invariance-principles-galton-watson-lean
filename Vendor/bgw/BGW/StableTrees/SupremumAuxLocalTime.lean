/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumAuxLocalTimeInverse
public import BGW.StableTrees.SupremumAuxLocalTimeInverseMeasurable

/-!
# Auxiliary continuous local time at the supremum

The occupation limit `supAuxLimit` of `BGW.StableTrees.SupremumCauchy` is a continuous monotone
clock, positive immediately and recurrent.
Its atomless Stieltjes measure is supported on supremum contact. Its strict inverse and ladder
height satisfy simultaneous pathwise geometry, with fixed-level a.e. measurability.

The mean and conditional discounted potentials are proved first from `supOccupationResolvent`
(`BGW.StableTrees.SupremumPotential`) and `supAuxLimit`, using ordinary cumulative-integral
formulas and half-rate growth bounds. The ENNReal germ helper is defined locally in this module.
Scaling and Blumenthal's law then prove positivity and recurrence. The proof uses no
identification of the public local time, all-path inverse measurability or stopping-time result.

The conditional potential is a deterministic-time identity. Consumers must not substitute a
random time into that almost-everywhere equality without a separate stopping argument.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VI.
* R. M. Blumenthal and R. K. Getoor, *Markov Processes and Potential Theory*, Academic Press,
  1968, Chapter V.
* A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed., Springer, 2014,
  Chapter 6.
-/

@[expose] public section
