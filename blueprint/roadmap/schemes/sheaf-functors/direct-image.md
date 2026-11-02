---
article_id: af_4a417e63d714ab6f6e4c4aa5
declaration: definition
origin: cited
mathlib: true
mathlib_declaration: TopCat.Sheaf.pushforward
mathlib_file: Mathlib/Topology/Sheaves/Functors.lean
---

# Direct image of a sheaf

For a continuous map $f : X \to Y$ and a sheaf $F$ on $X$, define the direct
image sheaf on $Y$ by

$(f_*F)(V) = F(f^{-1}(V))$.

The restrictions are those of $F$, and the sheaf condition follows
by taking inverse images of open covers.

## Depends on

- [Sheaves of abelian groups](../sheaves/sheaves-of-abelian-groups.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, definition of direct image (p. 65)](../../../sources/hartshorne-ii-1.md#sheaf-functors-printed-p-65)
