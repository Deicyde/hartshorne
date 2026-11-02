---
article_id: af_2bbb46bd7eb09b087128b5f9
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Hartshorne.projectiveDegree_union
---

# Degree is additive across a top-dimensional union

Let $Y = Y_{1} \cup Y_{2}$ be a projective algebraic set. If $Y_{1}$ and $Y_{2}$ both have
dimension $r$ and $\dim (Y_{1} \cap Y_{2}) < r$, then

$\deg Y = \deg Y_{1} + \deg Y_{2}$.

This is Proposition 7.6(b). Additivity of Hilbert polynomials along the union
exact sequence shows that the intersection term has too small a degree to
affect the leading coefficient.

## Depends on

- [Hilbert polynomials and degrees of projective algebraic sets](../hilbert/projective-hilbert-polynomial-and-degree.md)

## Proof depends on

- [The coordinate-ring sequence for a union is exact](union-coordinate-ring-exact-sequence.md)
- [Hilbert–Serre](../hilbert/hilbert-serre.md)

## Sources

- [Hartshorne I.7, Proposition 7.6(b) (p. 52)](../../../sources/hartshorne.md#i7-main-text-and-required-prerequisites)
