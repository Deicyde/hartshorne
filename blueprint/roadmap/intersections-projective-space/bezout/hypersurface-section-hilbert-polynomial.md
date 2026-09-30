---
article_id: af_04d24636e86b8040a6664a1a
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
---

# The Hilbert polynomial of a hypersurface section is a difference

Let `Y` be a projective variety and let `H = Z(f)` be a degree-`d`
hypersurface not containing `Y`. For
`M = S/(I(Y)+I(H))`, multiplication by `f` induces a graded exact sequence

`0 → S(Y)(-d) → S(Y) → M → 0`,

and hence `P_M(z) = P_Y(z) - P_Y(z-d)`. If `Y` has dimension `r ≥ 1` and
degree `e`, the leading coefficient of `P_M` is `d·e/(r-1)!`.

## Depends on

- [Integer-graded module twists](../hilbert/graded-module-twists.md)
- [The Hilbert function](../hilbert/hilbert-function.md)
- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)
- [A degree-d hypersurface has degree d](hypersurface-hilbert-polynomial.md)

## Proof depends on

- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Sources

- [Hartshorne I.7, proof of Theorem 7.7 (p. 53)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
