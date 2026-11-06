---
article_id: af_b8676c84ea1c7ada3d8fddba
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.varietyAssociatedSchemeConstants Hartshorne.varietyAssociatedSchemeStructureMorphism Hartshorne.varietyAssociatedScheme_structureMorphism_appTop Hartshorne.varietyAssociatedScheme_structureMorphism_unique Hartshorne.varietyAssociatedSchemeCanonicallyOver Hartshorne.varietyAssociatedScheme_over Hartshorne.SchemeVarietyCat.toSchemeCanonicallyOver
---

# The associated scheme is a scheme over the base field

For a variety $V$ over $k$, the inclusion of constant regular functions
$k \to \Gamma (t(V),\mathcal{O} )$ determines a canonical structure morphism

$t(V) \to \operatorname{Spec} k$.

This makes the associated scheme a scheme over $k$. The global-sections–
spectrum adjunction gives the unique morphism with the prescribed map on
global sections.

Here, as for the associated scheme itself, $V$ has an affine-open basis and
$k$ is algebraically closed.

## Depends on

- [A variety with an affine-open basis has an associated scheme](variety-associated-scheme.md)
- [Schemes over a base](../spectrum-and-schemes/over-base.md)

## Proof depends on

- [Morphisms to an affine scheme](../foundational-properties/morphisms-to-affine.md)

## Sources

- [Hartshorne II.2, structure morphism in Proposition 2.6 (pp. 78–79)](../../../sources/hartshorne-ii-2.md#schemes-over-a-base-and-proposition-26)
