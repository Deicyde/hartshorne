---
article_id: af_afdae7c93f1d1ddc7a1894cb
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.pointsEquivMaximalIdeals
---

# Points and maximal ideals

For an affine algebraic set $Y$, sending $P$ to the ideal $\mathfrak{m} _P$ of functions
vanishing at $P$ is a bijection from the points of $Y$ to the maximal ideals of
$A(Y)$ (Theorem 3.2(b)).

Evaluation at $P$ descends to $A(Y)$, because every element of $I(Y)$ vanishes
at $P$, and is surjective onto $k$, so its kernel $\mathfrak{m} _P$ is maximal and the
residue field is $k$. Injectivity is the separation of distinct points by a
coordinate function. Surjectivity is the Nullstellensatz: a maximal ideal of
$A(Y)$ pulls back to a maximal ideal of $k[x_{1},\ldots ,x_{n}]$, which is the ideal of a
point, and that point lies in $Z(I(Y)) = Y$.

Split from the rest of Theorem 3.2 because it is the one part that needs
nothing else in §3 and because two later results consume it directly: [Theorem I.3.2(a)](global-regular-eq-coordinate-ring.md) uses it to show an ideal of denominators is the whole ring, and [Theorem I.3.2(c)](affine-variety-rings.md) is stated about the localisation at $\mathfrak{m} _P$.

Stated for an algebraic set rather than a variety: nothing in the argument uses
irreducibility.

## Depends on

- [The affine coordinate ring](../affine-varieties/affine-coordinate-ring.md)

## Proof depends on

- [The Nullstellensatz](../affine-varieties/nullstellensatz.md)
- [Algebraic sets and radical ideals](../affine-varieties/radical-ideal-correspondence.md)

## Sources

- [Hartshorne I.3, Theorem 3.2(b) (p. 17)](../../sources/hartshorne.md#i3)
