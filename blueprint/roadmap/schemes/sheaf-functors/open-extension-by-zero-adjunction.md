---
article_id: af_813ed5a3017d80bd70095202
declaration: theorem
origin: bridged
source_units: [chapter-ii-sections-1-3]
---

# Open extension by zero is left adjoint to restriction

Let `j : U ↪ X` be an open immersion. The conditional-presheaf construction
of `j_!` is left adjoint to restriction along `j`:

`Hom_X(j_!F,G) ≃ Hom_U(F,j^*G)`.

The equivalence is natural in `F` and `G` and agrees with the canonical map
from the conditional presheaf construction. This is the ordinary sheaf
adjunction, not a statement about derived extraordinary functors.

## Depends on

- [Open extension by zero](open-extension-by-zero.md)
- [Inverse image of a sheaf](inverse-image.md)

## Proof depends on

- The generic sheafified left-Kan-extension construction of a left adjoint to
  restriction, together with its comparison to the conditional presheaf.

## Sources

- [Hartshorne II.1, Exercise 1.19(b) (p. 68), supplemented by the universal property needed to identify the construction](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
