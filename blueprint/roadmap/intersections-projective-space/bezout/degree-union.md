---
article_id: af_2bbb46bd7eb09b087128b5f9
declaration: theorem
origin: cited
source_units: [chapter-i-section-7-main]
statement: formalized
proof: formalized
lean: Hartshorne.projectiveDegree_union
---

# Degree is additive across a top-dimensional union

Let `Y = Y₁ ∪ Y₂` be a projective algebraic set. If `Y₁` and `Y₂` both have
dimension `r` and `dim (Y₁ ∩ Y₂) < r`, then

`projectiveDegree Y = projectiveDegree Y₁ + projectiveDegree Y₂`.

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
