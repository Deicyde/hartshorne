---
article_id: af_fd7f03cd7818de492f1610fc
declaration: def
origin: cited
source_units: [chapter-ii-section-4]
---

# Quasi-projective morphisms

A morphism `f : X ⟶ Y` is quasi-projective when there are a scheme `X'`,
an open immersion `j : X ⟶ X'`, and a projective morphism
`g : X' ⟶ Y` such that `f = j ≫ g`.

Package the intermediate scheme, immersion, projectivity witness, and
factorization equation as the defining data. The property should respect
isomorphism of arrows and admit the direct constructor showing every
projective morphism is quasi-projective via the identity open immersion.

## Depends on

- [Projective morphisms](projective-morphism.md)
- [Open immersions and open subschemes](../subschemes-and-dimension/open-immersions.md)

## Proof depends on

- Arrow-isomorphism invariance of open immersions and projectivity.

## Sources

- [Hartshorne II.4, definition of quasi-projective morphisms](../../../sources/hartshorne-ii-4.md#projective-morphisms)
