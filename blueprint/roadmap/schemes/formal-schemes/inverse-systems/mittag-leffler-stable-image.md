---
article_id: af_c81659bacbfcb45cf90a32f1
declaration: theorem
origin: cited
source_units: [chapter-ii-section-9]
statement: formalized
proof: formalized
lean: Hartshorne.InverseSystem.exists_stableImageSectionsAddEquiv
---

# Stable-image replacement

For a Mittag–Leffler inverse system `A`, let `A' n` be its stable image in
`A n`. The induced transition maps on `A'` are surjective, and the inclusion
of systems induces an isomorphism

`lim A' ≅ lim A`.

The isomorphism of limits is the unique main result.

## Depends on

- [Inverse systems and the Mittag–Leffler condition](inverse-system-mittag-leffler.md)

## Proof depends on

- `CategoryTheory.Functor.toEventualRanges`,
  `toEventualRangesSectionsEquiv`, and
  `surjective_toEventualRanges` from pinned Mathlib.
- Dependent choice for the limit of a sequential system of nonempty sets with
  surjective transition maps.

## Sources

- [Hartshorne II.9, stable-image discussion (pp.191–192)](../../../../sources/hartshorne-ii-9.md#inverse-systems-and-sheaf-limits)
- Stacks Project, tags `0596` and `0597`.
