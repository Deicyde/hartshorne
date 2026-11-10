---
article_id: af_8a05003a5be1e12ca9cc7683
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.principalOpenCoordinateRingEquiv
---

# The graph hypersurface has localized coordinate ring

For $0 \ne f \in k[x_{1},\ldots ,x_n]$, let
$H_f = Z(t f - 1) \subseteq \mathbb{A} ^{n+1}$. Its coordinate ring has a canonical
$k$-algebra equivalence

$A(H_f)\cong_k k[x_1,\ldots,x_n]_f$.

This equivalence is the main result. Geometrically, the next node identifies
$H_f$ with the principal open $D(f)$.


## Proof

The quotient of $k[x_1,\ldots,x_n,t]$ by $(tf-1)$ is the localization
$k[x_1,\ldots,x_n]_f$: the new variable represents the inverse of $f$.
This localization is a domain, so $(tf-1)$ is prime. The Nullstellensatz
identifies it with the vanishing ideal of $H_f$, giving the coordinate-ring
isomorphism.

## Depends on

- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [Algebraic sets and radical ideals](../affine-varieties/radical-ideal-correspondence.md)
- [Every finitely generated domain is a coordinate ring](../affine-varieties/coordinate-ring-realization.md)

## Sources

- [Hartshorne I.4, Lemma 4.2 (p. 25)](../../sources/hartshorne.md#i4)
