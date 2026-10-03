---
declaration: definition
origin: cited
source_units: [chapter-ii-sections-1-3]
---

# Open extension by zero

Let `j : U ↪ X` be the inclusion of an open subspace and `F` a sheaf on `U`.
Define `j_!F` by sheafifying the presheaf which is `F(V)` when `V ⊆ U` and
zero otherwise. Prove that its restriction to `U` is `F`, its stalk is `Fₓ`
on `U` and zero off `U`, and these properties characterize it uniquely up to
unique isomorphism.

This is ordinary extension by zero for abelian sheaves, not the later derived
extraordinary functor. No exact pinned-Mathlib construction was found.

## Depends on

- [The associated sheaf](../sheaves/associated-sheaf.md)
- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

- [Isomorphisms are detected on stalks](../sheaves/stalkwise-isomorphism.md)
- [Restriction preserves stalks](restriction-stalk.md)

## Sources

- [Hartshorne II.1, Exercise 1.19(b) (p. 68), used on p. 111](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)

