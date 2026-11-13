# Kolmogorov extension source slice

Apache-2.0 source extracted from
[RemyDegenne/kolmogorov_extension4](https://github.com/RemyDegenne/kolmogorov_extension4/tree/c20f168ed693537c78111ffeabc2ab5f384e35d6).
Only the three modules required by the Brownian construction are included; authors and
copyright notices are preserved.

`MathlibCompat.lean` backports the missing compact-system declarations from Mathlib
[e91b128](https://github.com/leanprover-community/mathlib4/tree/e91b128082cc221d6432a6a5aadcd3243af8e76c)
to our fixed Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
`CompactSystem.lean` imports this compatibility module. No mathematical hypothesis is added.
