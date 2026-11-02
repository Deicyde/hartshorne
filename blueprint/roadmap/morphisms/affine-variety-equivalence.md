---
article_id: af_f801b5bc0f2a08bbd4e42e42
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.coordEquivalence
---

# Equivalence with finitely generated domains

The coordinate-ring construction is a contravariant equivalence between
affine varieties over the algebraically closed field $k$ and finitely
generated integral domains over $k$. This is Hartshorne's Corollary I.3.8.

Morphisms of varieties correspond naturally to $k$-algebra homomorphisms
in the reverse direction. [The affine realization theorem](../affine-varieties/coordinate-ring-realization.md)
ensures that every finitely generated domain is the coordinate ring of
some affine variety. Pullback of regular functions respects identity and
composition, giving the functoriality of the correspondence.

## Depends on

- [Morphisms into an affine variety](hom-affine-bijection.md)
- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)
- [Morphisms](morphism.md)

## Proof depends on

- [Isomorphism via coordinate rings](affine-iso-iff-algebra-iso.md)
- [The coordinate ring is the ring of regular functions](global-regular-eq-coordinate-ring.md)
- [Points and maximal ideals](points-eq-maximal-ideals.md)
- [Every finitely generated domain is a coordinate ring](../affine-varieties/coordinate-ring-realization.md)

## Sources

- [Hartshorne I.3, Corollary 3.8 (p. 20)](../../sources/hartshorne.md#i3)
