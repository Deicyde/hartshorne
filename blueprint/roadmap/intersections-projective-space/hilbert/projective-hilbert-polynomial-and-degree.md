---
article_id: af_5b7e34d5e45271c5c73168b1
declaration: definition
origin: cited
source_units: [chapter-i-section-7-main]
---

# Hilbert polynomials and degrees of projective algebraic sets

For a projective algebraic set `Y ⊆ ℙⁿ`, define its Hilbert polynomial
`P_Y` to be the Hilbert polynomial of its homogeneous coordinate module
`S(Y) = S/J(Y)`. If `P_Y` has degree `r`, define

`projectiveDegree Y = r! · P_Y.leadingCoeff`.

The sole main declaration is planned as `Hartshorne.projectiveDegree`; its
required supporting definition is
`Hartshorne.projectiveHilbertPolynomial`. The formula is implemented uniformly
as `P_Y.natDegree.factorial · P_Y.leadingCoeff`, which also assigns degree zero
to the empty set because its Hilbert polynomial is zero. For nonempty `Y`,
Hilbert–Serre identifies `P_Y.natDegree` with the natural dimension of `Y`, so
this is exactly Hartshorne's `r!` times the leading coefficient.

Use the integer grading induced on the quotient by the homogeneous ideal
`J(Y)`. The projective ideal correspondence identifies
`Z(Ann S(Y)) = Z(J(Y))` with `Y`, so the module theorem gives the required
geometric degree statement. Integrality and positivity are deliberately left
to Proposition 7.6(a), rather than being built into this definition.

## Depends on

- [The integer grading on a polynomial ring](integer-polynomial-grading.md)
- [Integer-graded submodules and quotients](graded-submodules-and-quotients.md)
- [Hilbert–Serre](hilbert-serre.md)
- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Proof depends on

- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Sources

- [Hartshorne I.7, definitions after Theorem 7.5 (p. 52)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
