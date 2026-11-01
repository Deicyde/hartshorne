---
article_id: af_33e0735e317f0ed6698a6053
declaration: definition
origin: cited
lean: Hartshorne.openExtensionByZero
statement: formalized
proof: formalized
---

# Open extension by zero

Let `j : U ↪ X` be the inclusion of an open subspace and `F` a sheaf on `U`.
Define `j_!F` by sheafifying the presheaf which is `F(V)` when `V ⊆ U` and
zero otherwise.

For `V ⊆ U`, the inverse-image open `j⁻¹V` is `V` regarded as an open of
`U`, so the formal value `F(j⁻¹V)` is canonically the source value `F(V)`.
The zero branch is the zero additive subgroup; restrictions are inherited
from `F`.

This is ordinary extension by zero for abelian sheaves, not the later derived
extraordinary functor. Its adjunction and its source-stated restriction, stalk,
and compatible uniqueness properties are recorded in separate theorem leaves.

## Depends on

- [The associated sheaf](../sheaves/associated-sheaf.md)
- [Stalks and germs](../sheaves/stalks-and-germs.md)

## Proof depends on

No additional project-local results.

## Sources

- [Hartshorne II.1, Exercise 1.19(b) (p. 68), used on p. 111](../../../sources/hartshorne-ii-1.md#adopted-exercises-and-later-use-evidence)
