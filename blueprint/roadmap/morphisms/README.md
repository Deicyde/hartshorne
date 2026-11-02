---
article_id: af_8c0bb06941286b62e3549f9e
---

# Morphisms

Regular functions and morphisms connect the varieties constructed in the
first two sections. A regular function is locally a quotient of polynomials;
a morphism is a continuous map that pulls regular functions back to regular
functions. The four kinds of variety from Sections 1–2 then form a single
category.

Three rings describe a variety: its global regular functions $\mathcal{O} (Y)$, the
local ring $\mathcal{O} _{P,Y}$ of germs at a point, and its function field $K(Y)$.
Hartshorne identifies the global and local rings as subrings of $K(Y)$
and proves that the global ring is the intersection of all the local rings.
The injections, bundled algebra maps, and intersection formula are
formalized in this project.

For an affine variety, Theorem 3.2 computes these rings from $A(Y)$ and its
localizations. For a projective variety, Theorem 3.4 gives $\mathcal{O} (Y) = k$;
the local data is described through graded localizations of $S(Y)$.
[Corollary I.3.8](affine-variety-equivalence.md) concludes with an arrow-reversing equivalence between affine
varieties over $k$ and finitely generated integral domains over $k$.

## Regular functions

- [Regular functions on a quasi-affine variety](regular-function-quasi-affine.md)
- [Regular functions are continuous](regular-function-continuous.md)
- [Regular functions on a quasi-projective variety](regular-function-quasi-projective.md)

## The category of varieties

- [Varieties](variety.md)
- [Morphisms](morphism.md)

## The three rings

- [The ring of regular functions](ring-of-regular-functions.md)
- [The local ring at a point](local-ring.md)
- [The local ring is local](local-ring-is-local.md)
- [The local ring is functorial](local-ring-functorial.md)
- [The function field](function-field.md)
- [The function field of an arbitrary variety](function-field-abstract.md)
- [The function field is functorial for dominant morphisms](function-field-functorial.md)
- [The underlying maps into germs and rational functions are injective](function-field-injections.md)
- [Global functions and local rings](global-functions/README.md)

## Computing them

- [Points and maximal ideals](points-eq-maximal-ideals.md)
- [The coordinate ring is the ring of regular functions](global-regular-eq-coordinate-ring.md)
- [The local ring is a localisation](local-ring-is-localization.md)
- [The function field is the fraction field](function-field-is-fraction-field.md)
- [The local ring and function field of an affine variety](affine-variety-rings.md)

## The projective case

- [The rings of a projective variety](projective-rings/README.md)

## Affine varieties and finitely generated domains

- [Criterion for a morphism into an affine variety](morphism-to-affine-criterion.md)
- [Morphisms into an affine variety](hom-affine-bijection.md)
- [Isomorphism via coordinate rings](affine-iso-iff-algebra-iso.md)
- [Equivalence with finitely generated domains](affine-variety-equivalence.md)
