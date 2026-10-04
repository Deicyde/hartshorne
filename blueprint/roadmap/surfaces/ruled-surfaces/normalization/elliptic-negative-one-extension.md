---
article_id: af_66125d60d978c9100ccb0df8
declaration: theorem
origin: cited
source_units: [chapter-v-section-2]
---

# An elliptic ruled surface with invariant minus one

Let `C` be an elliptic curve and `P` a point. Up to isomorphism there is a
unique nonsplit extension

`0 -> O_C -> E -> O_C(P) -> 0`.

The bundle `E` is normalized, and `P_C(E)` is a ruled surface with
`e=-1`. This construction is valid in arbitrary characteristic.

## Depends on

- [Extensions and Ext-one](../../../cohomology/ext-groups/global-ext/ext-one-extension-classification.md)
- [Global Ext from the structure sheaf](../../../cohomology/ext-groups/global-ext/global-ext-structure-sheaf-cohomology.md)
- [Vector-bundle Serre duality](../../../cohomology/serre-duality/projective-duality/vector-bundle-serre-duality.md)
- [Genus-one canonical bundle is trivial](../../../curves/riemann-roch/genus-one-canonical-trivial.md)
- [Every ruled surface has a normalized projective-bundle presentation](normalized-projective-bundle-existence.md)

## Proof depends on

- `Ext^1(O(P),O)` is one-dimensional. For every negative-degree line
  bundle `A`, the extension sequence after tensoring by `A` has no global
  sections; when `A=O(-P)`, its connecting map sends `1` to the nonzero
  extension class.

## Sources

- [Hartshorne V.2, Example 2.11.6, p.375](../../../../sources/hartshorne-v-2.md)
