---
article_id: af_7641a33cab715c6d10fcd498
declaration: definition
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.hilbertFunction
---

# The Hilbert function

For a finite integer-graded module `M = ⊕ d, M_d` over
`S = k[x₀,…,xₙ]`, define its Hilbert function by

`φ_M(d) = dim_k M_d` for `d : ℤ`.

The sole main declaration is planned as `Hartshorne.hilbertFunction`, valued in
`ℕ`; later eventual-polynomial statements compare its cast with evaluation in
`ℚ`.

The supporting API must record the two identities used throughout the source:
twisting translates the argument,
`φ_{M(l)}(d) = φ_M(d+l)`, and a degreewise short exact sequence gives
`φ_M(d) = φ_{M'}(d) + φ_{M''}(d)`. These follow from the induced
subquotient gradings and finite-dimensional rank-nullity, not from a global
dimension of `M`.

## Depends on

- [Integer-graded module twists](graded-module-twists.md)
- [Integer-graded submodules and quotients](graded-submodules-and-quotients.md)
- [Finite-dimensional graded pieces](finite-graded-pieces.md)

## Sources

- [Hartshorne I.7, definition of the Hilbert function and exact-sequence identity in Theorem 7.5 (p. 51)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
