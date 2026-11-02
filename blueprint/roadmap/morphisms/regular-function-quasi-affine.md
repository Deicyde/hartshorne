---
article_id: af_591daa60fe66a7f31be6c0b6
declaration: def
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.IsRegularAt Hartshorne.IsRegular
---

# Regular functions on a quasi-affine variety

Let $Y \subseteq \mathbb{A} ^{n}$ be quasi-affine. A function $f : Y \to k$ is *regular at* $P \in Y$
when there is an open $U$ with $P \in U \subseteq Y$ and polynomials $g, h \in A$ such that
$h$ is nowhere zero on $U$ and $f = g/h$ on $U$. It is *regular on* $Y$ when it
is regular at every point.

The definition is local by design, which is what makes it behave like a sheaf
even though sheaves are not available in Chapter I. Note that the pair $(g, h)$
is allowed to vary with the point: a function can be regular without admitting a
single global representation as a quotient, and Hartshorne's later examples turn
on exactly that.

## Depends on

- [Affine and quasi-affine varieties](../affine-varieties/affine-variety.md)

## Sources

- [Hartshorne I.3, definition of a regular function on a quasi-affine variety (p. 15)](../../sources/hartshorne.md#i3)
