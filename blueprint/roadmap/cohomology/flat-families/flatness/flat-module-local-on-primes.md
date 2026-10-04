---
article_id: af_e1d511e9a9e727ac4e14ccec
declaration: theorem
origin: background
source_units: [chapter-iii-sections-8-9]
statement: formalized
proof: formalized
lean: Hartshorne.flat_iff_localizedModule_atPrime
---

# Flatness is local on prime localizations

An `R`-module `M` is flat if and only if `M_p` is flat over `R_p` for every
prime ideal `p` of `R`.

## Depends on

- Flat modules and localization at prime ideals.

## Proof depends on

- `Module.flat_iff_of_isLocalization` and
  `Module.flat_of_localized_maximal` from pinned Mathlib.
- [The finitely generated ideal criterion for flatness](flat-module-fg-ideal-criterion.md)
  to detect injectivity locally.
- Detection of injectivity after localization at all maximal ideals.

## Sources

- [Hartshorne III.9, Proposition 9.1A(d), pp.253–254](../../../../sources/hartshorne-iii-9.md#flat-modules-and-flat-morphisms-pp253255)
