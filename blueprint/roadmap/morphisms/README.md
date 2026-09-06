# Morphisms

The first two sections produced objects with no maps between them, so there was
no way to say when two varieties are the same. This section fixes that. A
regular function is one that is locally a quotient of polynomials, a morphism is
a continuous map that pulls regular functions back to regular functions, and the
four kinds of variety from §§1–2 become a single category.

Three rings come with each variety: the global regular functions `𝒪(Y)`, the
local ring `𝒪_{P,Y}` of germs at a point, and the function field `K(Y)`. Because
a regular function that vanishes on a nonempty open set vanishes everywhere, all
three sit inside one another as subrings of `K(Y)`, and all three are invariants
of the isomorphism class.

The section then computes them. For an affine variety, Theorem 3.2 identifies
all three with `A(Y)` and its localizations, which says the coordinate ring loses
nothing. For a projective variety, Theorem 3.4 says the opposite: `𝒪(Y) = k`, so
the global functions see nothing at all, and the local data lives in graded
localizations of `S(Y)`. The chapter's payoff is Corollary 3.8, an
arrow-reversing equivalence between affine varieties over `k` and finitely
generated integral domains over `k`, which is the precise sense in which affine
geometry and commutative algebra are the same subject.

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
- [The three rings embed in the function field](function-field-injections.md)
- [Global regular functions inside the function field](global-regular-in-function-field.md)

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
