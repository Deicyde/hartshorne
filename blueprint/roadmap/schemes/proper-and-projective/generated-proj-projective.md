---
article_id: af_b393ed07c0bc9cca0801abd3
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
---

# Degree-one-generated Proj is projective

Let `S` be a graded ring with `S₀ = A`, finitely generated as an `A`-algebra
by `S₁`. Then the structure morphism `Proj S ⟶ Spec A` is projective.

Choose finitely many degree-one algebra generators. They give a surjective
graded map from a standard polynomial ring `A[x₀,…,xₙ]` to `S`. The induced
map on `Proj` is a closed immersion, defined on the whole source, and its
target is relative projective space over `Spec A`. The factorization through
the projective-space projection is the structure morphism.

## Depends on

- [Projective morphisms](projective-morphism.md)
- [Projective space over a ring](../projective-spectrum/projective-space-over-ring.md)

## Proof depends on

- [A graded quotient induces a closed immersion of Proj](../normalization-and-exercises/proj-surjection-closed-immersion.md)
- A finite degree-one generating family yields a surjective graded polynomial
  algebra map.

## Sources

- [Hartshorne II.4, Example 4.8.1](../../../sources/hartshorne-ii-4.md#projective-morphisms)
