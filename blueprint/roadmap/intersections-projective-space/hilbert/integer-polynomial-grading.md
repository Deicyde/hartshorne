---
article_id: af_c9b34d562bca7bd9350f8d51
declaration: definition
origin: bridged
source_units: [chapter-i-section-7-main]
---

# The integer grading on a polynomial ring

For `S = k[x₀,…,xₙ]`, extend the usual total-degree grading from `ℕ` to `ℤ`
by taking the degree-`d` piece to be the ordinary homogeneous component when
`0 ≤ d` and the zero submodule when `d < 0`. The sole main artifact is planned
as `Hartshorne.integerHomogeneousSubmodule`, together with its certified
`DirectSum.Decomposition` and `GradedAlgebra` instances.

This representation makes the later convention `M(l)_d = M_{d+l}` literal.
It also includes the bridge that an ideal of `S` is homogeneous for this
integer grading exactly when it is homogeneous for the existing natural-number
grading. Thus the new infrastructure can reuse the project's homogeneous
vanishing ideals and quotient gradings without restating them.

Pinned Mathlib provides `MvPolynomial.homogeneousSubmodule` only with natural
indices. It has no integer extension or shift-compatible instance, so this is
a representation bridge rather than a mathematical strengthening of the
source.

## Depends on

- [Homogeneous ideals](../../projective-varieties/homogeneous-ideal.md)

## Sources

- [Hartshorne I.7, graded-ring and graded-module conventions before Proposition 7.4 (p. 50)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
