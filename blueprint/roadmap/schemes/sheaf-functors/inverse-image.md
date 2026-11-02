---
article_id: af_d72b5b55337c6e5a69a60321
declaration: definition
origin: cited
mathlib: true
mathlib_declaration: TopCat.Sheaf.pullback
mathlib_file: Mathlib/Topology/Sheaves/Functors.lean
---

# Inverse image of a sheaf

For a continuous map $f : X \to Y$ and a sheaf $G$ on $Y$, define $f^{-1}G$ as
the associated sheaf of the presheaf whose value on $U \subseteq X$ is the colimit of
$G(V)$ over opens $V \subseteq Y$ containing $f(U)$.

## Depends on

- [The associated sheaf](../sheaves/associated-sheaf.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, definition of inverse image (p. 65)](../../../sources/hartshorne-ii-1.md#sheaf-functors-printed-p-65)
