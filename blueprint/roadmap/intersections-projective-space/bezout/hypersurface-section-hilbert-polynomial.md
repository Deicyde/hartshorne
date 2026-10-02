---
article_id: af_04d24636e86b8040a6664a1a
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.hypersurfaceSection_hilbertPolynomial_and_leadingCoeff
---

# The Hilbert polynomial of a hypersurface section is a difference

Let `Y` be a projective variety and let `H = Z(f)` be a degree-`d`
hypersurface not containing `Y`. Put `M = S/(I(Y)+I(H))`. The
[hypersurface-section exact sequence](hypersurface-section-exact-sequence.md)
gives

`P_M(z) = P_Y(z) - P_Y(z-d)`.

If `Y` has dimension `r ≥ 1` and degree `e`, the leading coefficient of
`P_M` is `d·e/(r-1)!`.

## Depends on

- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)
- [A degree-d hypersurface has degree d](hypersurface-hilbert-polynomial.md)
- [The hypersurface-section coordinate-ring sequence is exact](hypersurface-section-exact-sequence.md)

## Proof depends on

- [Integer-graded module twists](../hilbert/graded-module-twists.md)
- [The Hilbert function](../hilbert/hilbert-function.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)
- [Dimension in projective space](../../projective-varieties/projective-dimension.md)
- [The homogeneous prime at a point](../../morphisms/projective-rings/point-ideal.md)

## Sources

- [Hartshorne I.7, proof of Theorem 7.7 (p. 53)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
