---
article_id: af_998ec5272223d187cf27ff4c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_restrictionStalkIso
---

# Restriction preserves stalks

Let $i : Z \hookrightarrow X$ be the inclusion of a topological subspace and define the
restriction $F|Z$ as $i^{-1}F$. For every $z \in Z$, construct a natural
isomorphism

$(F|Z)_z \cong F_{i(z)}$.

Restriction does not change a stalk because open neighbourhoods
inside the subspace form a cofinal family of neighbourhoods of the
point. Sheafification preserves this comparison.

## Depends on

- [Inverse image of a sheaf](inverse-image.md)
- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

- [Sheafification preserves stalks](../sheaves/associated-sheaf-stalks.md)

## Sources

- [Hartshorne II.1, restriction to a subspace and its stalks (p. 65)](../../../sources/hartshorne-ii-1.md#sheaf-functors-printed-p-65)
