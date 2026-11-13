/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.StraddlingExcursionLaw

/-!
# The excursion straddling a fixed time

Path extraction, predictable compensation, the passage potential, the joint start/lifetime
and shape law, independence, and the generalized arcsine law for the start.

## References

* J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapters IV and VIII.
* L. Chaumont, *Excursion normalisée, méandre et pont pour les processus de Lévy stables*,
  Bull. Sci. Math. 121 (1997), 377–403.
-/

@[expose] public section
