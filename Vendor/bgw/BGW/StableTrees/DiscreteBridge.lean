/-
Copyright (c) 2026 Igor Kortchemski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Kortchemski
-/
module

public import BGW.StableTrees.DiscreteBridgeInvariance

/-!
# Walk bridge convergence and the discrete cyclic law

The offspring-vector bridge converges in Skorokhod space to the stable bridge
along unbounded admissible sizes. Its Vervaat image is the exact-size tree walk.
Strict-prefix Radon–Nikodym identities, lattice local limits and reversal control
the singular conditioning and the terminal window.
-/

@[expose] public section
