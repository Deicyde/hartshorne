---
article_id: af_784fde36202d6caa05445aeb
declaration: theorem
origin: cited
mathlib: true
mathlib_declaration: AlgebraicGeometry.IsClosedImmersion.Spec_iff
mathlib_file: Mathlib/AlgebraicGeometry/Morphisms/ClosedImmersion.lean
---

# Closed subschemes of an affine scheme

For a morphism $f : X \to \operatorname{Spec} A$, $f$ is a closed immersion if and only if
there is an ideal $I \subseteq A$ and an isomorphism
$X \cong \operatorname{Spec} (A/I)$ over $\operatorname{Spec} A$.

The quotient map is surjective, and its spectrum has image $V(I)$.
Conversely, a closed immersion into an affine scheme gives a
surjection on global sections, identifying the source with the
spectrum of the quotient.

## Depends on

- [Closed immersions and closed subschemes](closed-immersions.md)
- [The contravariant Spec functor](../spectrum-and-schemes/spec-functor.md)

## Proof depends on

- Surjectivity on affine global sections and the first isomorphism theorem.

## Sources

- [Hartshorne II.3 (subschemes-and-dimension)](../../../sources/hartshorne-ii-3.md#subschemes-and-dimension)
