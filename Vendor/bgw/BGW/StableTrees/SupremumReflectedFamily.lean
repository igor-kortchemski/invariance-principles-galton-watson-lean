/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.SupremumReflectedFamilyMarkov

/-!
# The reflected-at-supremum family

For a path `f` and a starting value `x ≥ 0`, `supReflectedFrom x f t = max x S_t - X_t` is the
process reflected at its running supremum. This module collects:

* the restart identity at deterministic and random times (`supReflectedFrom_restart`,
  `supReflectedFrom_restart_shiftAt`) and joint measurability
  (`measurable_supReflectedFrom_uncurry`);
* absence of positive jumps under the stable law (`ae_supReflectedFrom_le_leftLim`);
* the Markov and strong Markov properties of the reflected family under `stableLocalLaw θ`
  (`condExp_supReflectedFromLoc_markov`, `integral_supReflectedFromLoc_strongMarkov`);
* continuity of the occupation functionals `supOccupation ε` and the geometry of the contact set
  (`isClosed_supContact`, `exists_excursionInterval_of_supReflected_pos`);
* prefix dependence and adaptedness to the raw filtration.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters III, IV and VI.
* A. E. Kyprianou, *Fluctuations of Lévy Processes with Applications*, 2nd ed., Springer, 2014,
  Chapters 3 and 6.
-/

@[expose] public section
