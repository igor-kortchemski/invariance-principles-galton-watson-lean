/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.MarkedExcursionsLifetime
public import BGW.StableTrees.MarkedExcursionsMarkov
public import BGW.StableTrees.MarkedExcursionsScaling

/-!
# The marked excursion point measure

The measure attaches the excursion cut to every positive passage-jump level. The imported
modules prove its counting form, AE measurability, support, lifetime sum, finite long-excursion
counts, simultaneous restart identity, fresh-measure law and independence from the stopped past,
and stationarity of translated windows.

The stopped-path enumeration proves stopped-history measurability. Consecutive windows are
independent, every measurable modification satisfies the time-simple Lévy interface, and
space-time scaling transports the marked measure pathwise on the full-probability support event.

(J. Bertoin, *Lévy Processes*, Cambridge University Press, 1996, Chapter IV, Sections 2–4; K. Itô,
Poisson point processes attached to Markov processes, Proc. Sixth Berkeley Symp. Math. Statist.
Probab. 3 (1972), 225–239.)
-/

@[expose] public section
