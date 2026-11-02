---
article_id: af_fa06185e80961e6f07a43fc0
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.ringKrullDim_homogeneousCoordinateRing_eq_projDim_add_one
---

# Dimension of the homogeneous coordinate ring

For a projective variety $Y \subseteq \mathbb{P} ^{n}$, $\dim S(Y) = \dim Y + 1$ (Exercise 2.6).

Hartshorne's hint is to identify $A(Y_{i})$ with the degree-zero part of the
localization $S(Y)_{x_i}$ and then show $S(Y)_{x_i}\cong A(Y_i)[x_i,x_i^{-1}]$, comparing
transcendence degrees to get the $+1$.

## Proof by an affine-cone section

The $+1$ is the dimension of the affine cone over $Y$, and the cheapest way to
see it is that $Y_{i}$ is a *hyperplane section* of that cone:

$S(Y)/(x_{i} - 1) \cong A(Y_{i})$.

That is the same identification Hartshorne's hint makes, read on the quotient
instead of the localization, and it avoids the Laurent-polynomial ring entirely.
Dehomogenisation is surjective onto $A(Y_{i})$, and its kernel is $(x_{i} - 1)$ on the
nose: upstairs the kernel of $\alpha$ on the polynomial ring is $(x_{i} - 1)$, by an
induction on monomials, and the ideal correspondence converts a polynomial killed modulo
$I(Y_{i})$ into one killed modulo $J(Y)$ after subtracting a multiple of $x_{i} - 1$.

The dimension then drops by exactly one because $(x_{i} - 1)$ has height one: at
least one since $S(Y)$ is a domain and $x_{i} - 1$ is nonzero, at most one by
Krull's principal ideal theorem. [Theorem I.1.8A(b)](../affine-varieties/dim-formula-catenary.md) converts
the height into the drop. Transcendence degrees are never mentioned, though they
are still there inside 1.8A(b).

Nonvanishing of $x_{i} - 1$ in $S(Y)$ is the one place the grading is used: $x_{i}$ is
homogeneous of degree one and $1$ of degree zero, so they can agree only in the
zero ring.

The geometric half, $\dim Y = \dim Y_{i}$, is the reverse inequality of [Proposition I.1.10](../affine-varieties/dim-quasi-affine.md) again, and again the easy direction is that a subspace has no larger
dimension. A chain of irreducible closed subsets of $Y$ need not meet a *given*
chart — its bottom term can be a point outside $U_{i}$ — but it meets some chart,
since the charts cover $\mathbb{P} ^{n}$ and every term contains the bottom one. Each chain is
therefore bounded by $\dim Y_j$ for a $j$ depending on the chain, and the
algebraic half is what says all those bounds are the same number.


## Depends on

- [The homogeneous vanishing ideal](homogeneous-vanishing-ideal.md)
- [Projective and quasi-projective varieties](projective-variety.md)
- [Dimension of a topological space and of a ring](../affine-varieties/dimension.md)

## Proof depends on

- [The standard affine charts](standard-affine-charts.md)
- [Dimension is the dimension of the coordinate ring](../affine-varieties/dim-eq-coordinate-ring-dim.md)
- [Dimension of a finitely generated domain](../affine-varieties/dim-fg-domain.md)
- [The dimension formula for a finitely generated domain](../affine-varieties/dim-formula-catenary.md)

## Sources

- [Hartshorne I.2, Exercise 2.6 (pp. 11-12)](../../sources/hartshorne.md#i2)
