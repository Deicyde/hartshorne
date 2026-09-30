---
article_id: af_82927206aa5b303a075e9d11
declaration: theorem
origin: bridged
source_units: [chapter-i-section-7-main]
---

# The coordinate-ring sequence for a union is exact

For homogeneous ideals `I₁,I₂ ⊆ S`, the canonical sequence

`0 → S/(I₁ ∩ I₂) → S/I₁ ⊕ S/I₂ → S/(I₁ + I₂) → 0`

is an exact sequence of integer-graded `S`-modules. Applied to projective
algebraic sets `Y₁,Y₂`, the three quotients are the coordinate modules of
`Y₁ ∪ Y₂`, the two pieces, and `Y₁ ∩ Y₂`.

This is the exact sequence used in Proposition 7.6(b). The main declaration
packages exactness together with compatibility of the induced gradings, so
Hilbert-function additivity applies without later transport lemmas.

## Depends on

- [Integer-graded submodules and quotients](../hilbert/graded-submodules-and-quotients.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Proof depends on

- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Sources

- [Hartshorne I.7, proof of Proposition 7.6(b) (p. 52)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
