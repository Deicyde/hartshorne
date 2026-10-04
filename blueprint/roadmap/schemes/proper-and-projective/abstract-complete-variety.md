---
article_id: af_1f06f31606760412c5e52f6d
declaration: structure
origin: cited
source_units: [chapter-ii-section-4]
---

# Abstract and complete varieties

For an algebraically closed field `k`, define an abstract variety to be a
scheme over `Spec k` whose total space is integral and whose structure
morphism is separated and finite type. Define such a variety to be complete
when its structure morphism is proper.

Package the structure morphism using `Over (Spec (.of k))`, with fields for
the three mathematical properties. The completion predicate should reuse
`IsProper`; projective varieties become complete through Theorem 4.9. Keep the
new scheme-based object visibly distinct from the project's Chapter-I
`Hartshorne.Variety`, and provide a constructor from the essential-image
comparison rather than identifying the types definitionally.

## Depends on

- [Schemes over a base](../spectrum-and-schemes/over-base.md)
- [Integral schemes](../first-properties/integral-scheme.md)
- [Separated morphisms](../separated-morphisms/separated-morphism.md)
- [Morphisms of finite type](../first-properties/finite-type.md)
- [Proper morphisms](proper-morphism.md)

## Proof depends on

- [Classical varieties are the quasi-projective integral schemes](associated-variety-essential-image.md)
- [Projective morphisms are proper](projective-morphism-proper.md)

## Sources

- [Hartshorne II.4, definition of abstract and complete varieties](../../../sources/hartshorne-ii-4.md#varieties-and-integral-closure)
