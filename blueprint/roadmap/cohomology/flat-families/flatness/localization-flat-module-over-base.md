---
article_id: af_bb4d90561957ab97003d834b
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-8-9]
statement: formalized
proof: formalized
lean: Hartshorne.localizedModule_flat_over_base
---

# Localization of a flat module over its base

Let `A -> B` be a ring map, let `M` be a `B`-module flat over `A`, and let
`S` be a multiplicative subset of `B`. Then `S^-1 M`, regarded as an
`A`-module through `A -> B -> S^-1 B`, is flat over `A`.

This is distinct from the exact upstream theorem that a localized ring is
flat over the original ring.

## Depends on

- Flat modules and localization of a module along its `B`-action.

## Proof depends on

- [Localizations are flat](localization-is-flat.md)
- Exactness of `M ⊗_A -` from the assumed `A`-flatness.
- Exactness of `S^-1 B ⊗_B -` from localization flatness.
- Tensor associativity identifying their composite with `S^-1 M ⊗_A -`.

## Sources

- [Hartshorne III.9, Example 9.1.1, p.254](../../../../sources/hartshorne-iii-9.md#flat-modules-and-flat-morphisms-pp253255)
