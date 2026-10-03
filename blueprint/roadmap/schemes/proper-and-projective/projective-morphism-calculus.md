---
declaration: theorem
origin: cited
source_units: [chapter-ii-section-4]
---

# Projective-morphism calculus

The two later-used conclusions of Exercises 4.8–4.9 are:

1. projective morphisms compose; and
2. if `X ⟶ Y ⟶ Z` has projective composite and `Y ⟶ Z` is separated,
   then `X ⟶ Y` is projective.

For composition, embed the first source into projective space over the
intermediate scheme and combine that embedding with an embedding of the
intermediate scheme over the base. The product lands in a product of relative
projective spaces; the relative Segre embedding turns it into one projective
space. For cancellation, the graph `X ⟶ X ×[Z] Y` is a closed immersion because
`Y/Z` is separated, and the second projection is a base change of the
projective composite.

Closed-immersion and base-change stability are supporting calculus used in
these proofs, not additional exercise targets. Exercise 4.8(f), concerning
reduction of a morphism, is excluded because no later running-text use was
found.

## Depends on

- [Projective morphisms](projective-morphism.md)
- [Separated morphisms](../separated-morphisms/separated-morphism.md)

## Proof depends on

- [The relative Segre embedding](relative-segre-closed-immersion.md)
- [Separated-morphism calculus](../separated-morphisms/separated-morphism-calculus.md)
- Closed immersions compose and are stable under base change.
- The graph of a morphism into a separated target is a closed immersion.

## Sources

- [Hartshorne II.4, Exercise 4.8(e) and the composition assertion of Exercise 4.9](../../../sources/hartshorne-ii-4.md#adopted-exercises)
