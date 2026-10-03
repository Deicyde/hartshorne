---
declaration: isomorphism
origin: cited
source_units: [appendix-a-sections-1-2]
---

# The Chow ring of projective space

For projective `n`-space and the hyperplane class `h in A^1(P^n)`,

`A(P^n) ~= Z[h]/(h^(n+1))`

as graded rings.

## Depends on

- [Affine-space pullback is an isomorphism](chow-affine-homotopy-invariance.md)
- [Localization exact sequence](chow-localization-exact-sequence.md)
- [Codimension-one Chow classes are the Picard group](chow-codimension-one-picard.md)
- [Cartier-divisor intersection normalization](../product/cartier-divisor-normalization.md)
- [Degree of a zero-cycle on a complete variety](../cycles/complete-variety-zero-cycle-degree.md)

## Proof depends on

- Induct on `n` using `P^n-P^(n-1)~=A^n`, localization, and homotopy
  invariance. Multiplication by `h` identifies the successive linear-subspace
  classes, and dimension gives `h^(n+1)=0`.

## Sources

- [Hartshorne Appendix A.2, Example 2.0.1, p.429](../../../../sources/hartshorne-appendix-a-1-2.md)
