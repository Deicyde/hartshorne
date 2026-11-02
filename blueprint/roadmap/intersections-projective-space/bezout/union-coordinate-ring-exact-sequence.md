---
article_id: af_82927206aa5b303a075e9d11
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.unionCoordinateRing_exact
---

# The coordinate-ring sequence for a union is exact

For homogeneous ideals $I_{1},I_{2} \subseteq S$, the canonical sequence

$0 \to S/(I_{1} \cap I_{2}) \to S/I_{1} \oplus S/I_{2} \to S/(I_{1} + I_{2}) \to 0$

is an exact sequence of integer-graded $S$-modules. Applied to projective
algebraic sets $Y_{1},Y_{2}$, the first three terms are the coordinate modules of
$Y_{1} \cup Y_{2}$ and the two pieces. The final quotient is supported on
$Y_{1} \cap Y_{2}$; it need not be the reduced homogeneous coordinate ring of that
intersection.

This is the exact sequence used in Proposition 7.6(b).
## Depends on

- [Integer-graded submodules and quotients](../hilbert/graded-submodules-and-quotients.md)
- [Algebraic sets and homogeneous radical ideals](../../projective-varieties/homogeneous-ideal-correspondence.md)

## Proof depends on

- [The homogeneous vanishing ideal](../../projective-varieties/homogeneous-vanishing-ideal.md)

## Sources

- [Hartshorne I.7, proof of Proposition 7.6(b) (p. 52)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
