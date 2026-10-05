---
article_id: af_8f159700097a79f55cfc8959
declaration: theorem
origin: cited
source_units: [chapter-iii-sections-8-9]
statement: formalized
proof: formalized
lean: Hartshorne.moduleSheaf_flatOver_comp
---

# Transitivity for module sheaves flat over a base

Let `f : X -> Y` and `g : Y -> Z`. If an `O_X`-module `F` is flat over `Y`
and the scheme morphism `g` is flat, then `F` is flat over `Z` through
`g after f`.

## Depends on

- [A module sheaf flat over a base](module-sheaf-flat-over-base.md)
- [The stalk criterion for flat morphisms](flat-morphism-stalk-criterion.md)

## Proof depends on

- [Transitivity of flat modules](flat-module-transitivity.md)
- Apply transitivity to the two local-ring actions on every stalk of `F`.

## Sources

- [Hartshorne III.9, Proposition 9.2(c), p.254](../../../../sources/hartshorne-iii-9.md#flat-modules-and-flat-morphisms-pp253255)
