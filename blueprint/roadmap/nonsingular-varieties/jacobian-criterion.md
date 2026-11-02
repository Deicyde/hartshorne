---
article_id: af_d6e446056a8870546b543b7a
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.isAffineNonsingularAt_iff_isRegularLocalRing
---

# The Jacobian criterion

Let $Y \subseteq \mathbb{A} ^{n}$ be an affine variety and $P \in Y$. Then $P$ is
nonsingular in the Jacobian sense if and only if its local ring
$\mathcal{O} _{P,Y}$ is a regular local ring.

This is Theorem 5.1. Choose the unique natural number $r$ with
$\dim Y = r$. [Theorem I.3.2(c)](../morphisms/affine-variety-rings.md) gives
$\dim \mathcal{O} _{P,Y} = r$, while the cotangent comparison gives

$\dim _k(\mathfrak{m} _P/\mathfrak{m} _P^{2}) + \operatorname{rank} J(P) = n$.

After transporting the residue field of $\mathcal{O} _{P,Y}$ to $k$, regularity says
that the first summand is $r$; elementary finite-dimensional arithmetic then
says exactly that the Jacobian rank is $n - r$. Both implications use the
same equality, so no characteristic assumption enters Theorem 5.1.

## Depends on

- [Regular local rings](regular-local-rings.md)
- [Nonsingular points of an affine variety](affine-nonsingular-points.md)

## Proof depends on

- [The defining ideal and the local cotangent space](defining-ideal-cotangent-sequence.md)
- [The local ring and function field of an affine variety](../morphisms/affine-variety-rings.md)

## Sources

- [Hartshorne I.5, Theorem 5.1 (p. 32)](../../sources/hartshorne.md#i5)
