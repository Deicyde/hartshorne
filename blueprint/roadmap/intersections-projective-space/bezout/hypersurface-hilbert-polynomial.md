---
article_id: af_cfa44c986c3be95861967648
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
---

# A degree-d hypersurface has degree d

Let `f ∈ k[x₀,…,xₙ]` be a nonzero homogeneous polynomial of positive degree
`d`, and let `H = Z(f) ⊆ ℙⁿ`. Then

`P_H(z) = P_{ℙⁿ}(z) - P_{ℙⁿ}(z-d)`

and `projectiveDegree H = d`.

This is Proposition 7.6(d). Multiplication by `f` gives the graded exact
sequence `0 → S(-d) → S → S/(f) → 0`; the Hilbert-function difference gives
the polynomial identity, and the leading term is `d/(n-1)!`.

## Depends on

- [Integer-graded module twists](../hilbert/graded-module-twists.md)
- [The Hilbert function](../hilbert/hilbert-function.md)
- [Projective space has degree one](projective-space-hilbert-polynomial.md)
- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)

## Proof depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)

## Sources

- [Hartshorne I.7, Proposition 7.6(d) (p. 52)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
