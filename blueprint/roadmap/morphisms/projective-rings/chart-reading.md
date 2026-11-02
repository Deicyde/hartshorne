---
article_id: af_9151d1a05185ce97d9df7ad5
declaration: theorem
origin: bridged
statement: formalized
proof: formalized
lean: Hartshorne.exists_awayToAtPrime_eq_of_globalRegular Hartshorne.exists_homogeneous_repr_of_globalRegular
---

# Reading a global regular function on a chart

Let $Y$ be a projective variety and let $f$ be a global regular function.
On every standard chart $U_i$ meeting $Y$, there are an integer $N\geq0$
and a homogeneous polynomial $g$ of degree $N$ such that

$$f(P)x_i(P)^N=g(P)\qquad(P\in Y\cap U_i).$$

The affine chart identifies the restriction of $f$ with a polynomial in
affine coordinates. Homogenizing that polynomial gives $g$; the factor
$x_i^N$ is the change between affine evaluation and homogeneous evaluation.
The same description says that the function-field image of $f$ belongs
to the degree-zero localization $S(Y)_{(x_i)}$.

This is the chart description used in
[Hartshorne's Theorem I.3.4(a)](projective-global-regular.md).

## Depends on

- [Global regular functions inside the function field](../global-functions/global-regular-in-function-field.md)
- [The charts are isomorphisms of varieties](chart-isomorphism.md)

## Proof depends on

- [The coordinate ring is the ring of regular functions](../global-regular-eq-coordinate-ring.md)
- [The function field of a projective variety](projective-function-field.md)

## Sources

- [Hartshorne I.3, Theorem 3.4(a) (pp. 18-19)](../../../sources/hartshorne.md#i3)
