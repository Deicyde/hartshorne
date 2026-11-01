---
article_id: af_50efedaea918279cc0a904e9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.QuasiProjective.finiteType_and_isSeparated Hartshorne.QuasiProjective.finiteType_and_isSeparated_of_isLocallyNoetherian
---

# Quasi-projective morphisms are finite type and separated

Let `f : X ⟶ Y` be a quasi-projective morphism of Noetherian schemes. Then
`f` is finite type and separated.

Choose a factorization of `f` as an open immersion `X ⟶ X'` followed by a
projective morphism `X' ⟶ Y`. The projective map is proper, hence separated
and finite type. An open immersion is locally finite type and separated; with
locally Noetherian target, it is also quasi-compact, hence finite type.
Composition gives both conclusions for `f`.

Keep the Noetherian hypothesis visible: an arbitrary open immersion need not
be quasi-compact, so Hartshorne's finite-type conclusion is not unconditional.

The hypothesis that `X` is Noetherian is retained to match Hartshorne's source
statement, although the separate generalization proves both conclusions for
an arbitrary `X` over a locally Noetherian `Y`.

## Depends on

- [Quasi-projective morphisms](quasi-projective-morphism.md)
- [Separated morphisms](../separated-morphisms/separated-morphism.md)
- [Morphisms of finite type](../first-properties/finite-type.md)
- [Noetherian schemes and finite affine covers](../first-properties/noetherian-scheme.md)

## Proof depends on

- [Projective morphisms are proper](projective-morphism-proper.md)
- [Separated-morphism calculus](../separated-morphisms/separated-morphism-calculus.md)
- [Locally Noetherian schemes](../first-properties/locally-noetherian.md)
- Quasi-compactness of open immersions into locally Noetherian schemes.
- [Finite-type morphisms compose](../first-properties/finite-type-composition.md)

## Sources

- [Hartshorne II.4, second assertion of Theorem 4.9](../../../sources/hartshorne-ii-4.md#projective-morphisms)
