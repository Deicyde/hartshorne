---
article_id: af_49afe04b8aacd5833ce44137
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.exists_isAffineVariety_coordinateRing_equiv Hartshorne.isAffineVariety_zeroLocus_of_isPrime Hartshorne.vanishingIdeal_zeroLocus_of_isPrime
---

# Every finitely generated domain is a coordinate ring

Any finitely generated $k$-algebra $B$ that is an integral domain is isomorphic
to $A(Y)$ for some affine variety $Y$. Writing $B$ as a quotient
$A/\mathfrak{a}$ of a polynomial ring $A = k[x_{1},\ldots ,x_{n}]$, the variety is $Y = Z(\mathfrak{a} )$.

Hartshorne records this as the second half of Remark 1.4.6 and does not belabour
it, but it carries the two facts that make the construction work. That $B$ is a
domain makes $\mathfrak{a}$ prime, which makes $Z(\mathfrak{a} )$ irreducible and therefore a variety.
That $\mathfrak{a}$ is prime makes it radical, so the Nullstellensatz gives $I(Z(\mathfrak{a} )) = \mathfrak{a}$
rather than merely $\sqrt{\mathfrak{a}}$, and hence $A(Y) = A/I(Z(\mathfrak{a} )) = A/\mathfrak{a} \cong B$.

Both steps fail without the domain hypothesis, which is the reason it appears in
the statement of [Corollary I.3.8](../morphisms/affine-variety-equivalence.md) rather than being dropped for a general finitely
generated $k$-algebra. This article exists separately from the coordinate ring
construction because it is what supplies essential surjectivity in that
corollary, and a functor being essentially surjective is a theorem that wants
its own name.

## Depends on

- [The affine coordinate ring](affine-coordinate-ring.md)
- [Affine and quasi-affine varieties](affine-variety.md)

## Proof depends on

- [Algebraic sets and radical ideals](radical-ideal-correspondence.md)
- [Hilbert's Nullstellensatz](nullstellensatz.md)

## Sources

- [Hartshorne I.1, Remark 1.4.6 (pp. 4-5)](../../sources/hartshorne.md#i1)
