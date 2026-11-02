---
article_id: af_2a3cea68a7953dda12f13d0c
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.jacobianRank_add_dim_le_ambient Hartshorne.jacobianRank_le_ambient_sub_dim Hartshorne.not_isAffineNonsingularAt_iff_jacobianRank_lt
---

# The Jacobian rank bound

Let $Y \subseteq \mathbb{A} ^{n}$ be an affine variety of dimension $r$. At every point
$P \in Y$,

$\operatorname{rank} J(P) \le n - r$.

Indeed, [Proposition I.5.2A](cotangent-dimension-bound.md) gives
$r = \dim \mathcal{O} _{P,Y} \le \dim _k(\mathfrak{m} _P/\mathfrak{m} _P^{2})$, while the dimension formula
from [Theorem I.5.1](jacobian-criterion.md)'s proof gives
$\dim _k(\mathfrak{m} _P/\mathfrak{m} _P^{2}) + \operatorname{rank} J(P) = n$. Subtracting in $\mathbb{N}$
yields the displayed inequality.

This direction matters: the Jacobian rank cannot exceed the codimension. Hence
a point fails to be nonsingular precisely when the rank is *strictly less* than
$n - r$, which is the determinantal condition used to prove closedness.

## Depends on

- [Jacobian rank is independent of generators](jacobian-rank-invariance.md)
- [Nonsingular points of an affine variety](affine-nonsingular-points.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Proof depends on

- [The cotangent-dimension bound](cotangent-dimension-bound.md)
- [The defining ideal and the local cotangent space](defining-ideal-cotangent-sequence.md)
- [The local ring and function field of an affine variety](../morphisms/affine-variety-rings.md)

## Sources

- [Hartshorne I.5, Proposition 5.2A and proof of Theorem 5.3 (p. 33)](../../sources/hartshorne.md#i5)
