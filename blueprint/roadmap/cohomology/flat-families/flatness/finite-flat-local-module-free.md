---
declaration: theorem
origin: background
source_units: [chapter-iii-sections-8-9]
---

# Finite flat modules over local rings are free

For a Noetherian local ring `R` and a finitely generated `R`-module `M`, the
module `M` is flat if and only if it is finite free.

## Depends on

- Finite modules over Noetherian local rings and flat modules.

## Proof depends on

- `Module.free_of_flat_of_isLocalRing` for the forward implication.
- `Module.Flat.of_free` for the converse.
- [The finitely generated ideal criterion for flatness](flat-module-fg-ideal-criterion.md).

This source-shaped iff is a project wrapper around two upstream facts, not an
exact whole upstream declaration.

## Sources

- [Hartshorne III.9, Proposition 9.1A(f), p.254](../../../../sources/hartshorne-iii-9.md#flat-modules-and-flat-morphisms-pp253255)
